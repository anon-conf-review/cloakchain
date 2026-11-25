use ark_crypto_primitives::snark::SNARKGadget;
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar, poseidon::PoseidonSponge,
    CryptographicSponge, FieldBasedCryptographicSponge,
};
use ark_ff::{BigInteger, Field, PrimeField};
pub mod snark;

use snark::{PreparedVerifyingKeyVar, Proof, ProofVar, ProvingKey, Snark, VerifierGadget, VerifyingKey};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_r1cs_std::{
    alloc::AllocationMode,
    fields::fp::FpVar,
    groups::curves::short_weierstrass::{non_zero_affine::NonZeroAffineVar, ProjectiveVar},
    pairing::PairingVar,
    prelude::*,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_lib::{poseidon_params, Fr as Fr4};

pub type Fr6 = ark_mnt6_753::Fr;
type Fp6 = FpVar<Fr6>;
type MNT4PairingVar = ark_mnt4_753::constraints::PairingVar;

pub const CHUNK_BITS: usize = 200;

pub fn chunks_per_value() -> usize {
    (Fr4::MODULUS_BIT_SIZE as usize).div_ceil(CHUNK_BITS)
}

fn opt<T: Clone>(o: &Option<T>) -> Result<T, SynthesisError> {
    o.clone().ok_or(SynthesisError::AssignmentMissing)
}

pub fn scalar_mul_le_compact<P: SWCurveConfig>(
    base: &ProjectiveVar<P, FpVar<P::BaseField>>,
    bits: &[Boolean<P::BaseField>],
) -> Result<ProjectiveVar<P, FpVar<P::BaseField>>, SynthesisError>
where
    P::BaseField: PrimeField,
{
    PowersOfTwo::new(base, bits.len())?.scalar_mul_le(bits)
}

pub struct PowersOfTwo<P: SWCurveConfig>
where
    P::BaseField: PrimeField,
{
    infinity: Boolean<P::BaseField>,
    powers: Vec<NonZeroAffineVar<P, FpVar<P::BaseField>>>,
}

impl<P: SWCurveConfig> PowersOfTwo<P>
where
    P::BaseField: PrimeField,
{
    pub fn new(base: &ProjectiveVar<P, FpVar<P::BaseField>>, n: usize) -> Result<Self, SynthesisError> {
        let cs = base.cs();
        let compact = |p: NonZeroAffineVar<P, FpVar<P::BaseField>>| -> Result<_, SynthesisError> {
            if p.x.is_constant() && p.y.is_constant() {
                return Ok(p);
            }
            let x = FpVar::new_witness(cs.clone(), || p.x.value())?;
            let y = FpVar::new_witness(cs.clone(), || p.y.value())?;
            x.enforce_equal(&p.x)?;
            y.enforce_equal(&p.y)?;
            Ok(NonZeroAffineVar::new(x, y))
        };

        let affine = base.to_affine()?;
        let infinity = affine.infinity;
        let x = infinity.select(&FpVar::constant(P::GENERATOR.x), &affine.x)?;
        let y = infinity.select(&FpVar::constant(P::GENERATOR.y), &affine.y)?;
        let mut powers = Vec::with_capacity(n);
        if n > 0 {
            powers.push(NonZeroAffineVar::new(x, y));
        }
        while powers.len() < n {
            let next = compact(powers.last().expect("nonempty").double()?)?;
            powers.push(next);
        }
        Ok(Self { infinity, powers })
    }

    pub fn scalar_mul_le(&self, bits: &[Boolean<P::BaseField>]) -> Result<ProjectiveVar<P, FpVar<P::BaseField>>, SynthesisError> {
        type Point<P> = ProjectiveVar<P, FpVar<<P as ark_ec::CurveConfig>::BaseField>>;
        let scalar_bits = <P::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize;
        assert!(bits.len() <= scalar_bits, "one chunk of scalar bits at most");
        assert!(bits.len() <= self.powers.len(), "not enough precomputed powers");
        if bits.is_empty() {
            return Ok(Point::<P>::zero());
        }

        let mut accumulator = self.powers[0].clone();
        let initial = accumulator.into_projective();
        let split = (scalar_bits - 2).min(bits.len());
        for (bit, power) in bits[1..split].iter().zip(&self.powers[1..split]) {
            let sum = accumulator.add_unchecked(power)?;
            accumulator = bit.select(&sum, &accumulator)?;
        }
        let mut result = accumulator.into_projective() - bits[0].select(&Point::<P>::zero(), &initial)?;
        for (bit, power) in bits[split..].iter().zip(&self.powers[split..]) {
            let sum = &result + &power.into_projective();
            result = bit.select(&sum, &result)?;
        }
        self.infinity.select(&Point::<P>::zero(), &result)
    }
}

#[cfg(not(feature = "groth16"))]
fn verify_mnt4(
    pvk: &PreparedVerifyingKeyVar<MNT4_753, MNT4PairingVar>,
    inputs: &[Vec<Boolean<Fr6>>],
    proof: &ProofVar<MNT4_753, MNT4PairingVar>,
) -> Result<Boolean<Fr6>, SynthesisError> {
    assert_eq!(inputs.len() + 1, pvk.query.len());
    let mut g_psi = pvk.query[0].clone();
    for (bits, base) in inputs.iter().zip(&pvk.query[1..]) {
        g_psi += scalar_mul_le_compact(base, bits)?;
    }

    let test1_a_g_alpha = (proof.a.clone() + &pvk.g_alpha).negate()?;
    let test1_b_h_beta = proof.b.clone() + &pvk.h_beta;
    let test1 = MNT4PairingVar::final_exponentiation(&MNT4PairingVar::miller_loop(
        &[
            MNT4PairingVar::prepare_g1(&test1_a_g_alpha)?,
            MNT4PairingVar::prepare_g1(&g_psi)?,
            MNT4PairingVar::prepare_g1(&proof.c)?,
            pvk.g_alpha_pc.clone(),
        ],
        &[
            MNT4PairingVar::prepare_g2(&test1_b_h_beta)?,
            pvk.h_gamma_pc.clone(),
            pvk.h_pc.clone(),
            pvk.h_beta_pc.clone(),
        ],
    )?)?;
    let test2 = MNT4PairingVar::final_exponentiation(&MNT4PairingVar::miller_loop(
        &[MNT4PairingVar::prepare_g1(&proof.a)?, pvk.g_gamma_pc.clone()],
        &[pvk.h_gamma_pc.clone(), MNT4PairingVar::prepare_g2(&proof.b.negate()?)?],
    )?)?;
    let one = <MNT4PairingVar as PairingVar<MNT4_753>>::GTVar::one();
    Ok(&test1.is_eq(&one)? & &test2.is_eq(&one)?)
}

#[cfg(feature = "groth16")]
fn verify_mnt4(
    pvk: &PreparedVerifyingKeyVar<MNT4_753, MNT4PairingVar>,
    inputs: &[Vec<Boolean<Fr6>>],
    proof: &ProofVar<MNT4_753, MNT4PairingVar>,
) -> Result<Boolean<Fr6>, SynthesisError> {
    assert_eq!(inputs.len() + 1, pvk.gamma_abc_g1.len());
    let mut g_ic = pvk.gamma_abc_g1[0].clone();
    for (bits, base) in inputs.iter().zip(&pvk.gamma_abc_g1[1..]) {
        g_ic += scalar_mul_le_compact(base, bits)?;
    }
    let test = MNT4PairingVar::final_exponentiation(&MNT4PairingVar::miller_loop(
        &[
            MNT4PairingVar::prepare_g1(&proof.a)?,
            MNT4PairingVar::prepare_g1(&g_ic)?,
            MNT4PairingVar::prepare_g1(&proof.c)?,
        ],
        &[MNT4PairingVar::prepare_g2(&proof.b)?, pvk.gamma_g2_neg_pc.clone(), pvk.delta_g2_neg_pc.clone()],
    )?)?;
    test.is_eq(&pvk.alpha_g1_beta_g2)
}

pub const VK_HASH_BITS: usize = 600;

fn vk_coordinates(vk: &VerifyingKey<MNT4_753>) -> Vec<Fr6> {
    let (g1s, g2s) = snark::vk_points(vk);
    let mut out = Vec::new();
    for g in g1s {
        out.extend([g.x, g.y]);
    }
    for g in g2s {
        out.extend([g.x.c0, g.x.c1, g.y.c0, g.y.c1]);
    }
    out
}

pub fn inner_vk_hash(vk: &VerifyingKey<MNT4_753>) -> Fr4 {
    let mut sponge = PoseidonSponge::new(&poseidon_params::mnt6_753_fr_poseidon_config());
    sponge.absorb(&vk_coordinates(vk));
    let digest: Fr6 = sponge.squeeze_native_field_elements(1)[0];
    let bits = &digest.into_bigint().to_bits_le()[..VK_HASH_BITS];
    Fr4::from_bigint(<Fr4 as PrimeField>::BigInt::from_bits_le(bits)).expect("600 bits are below the modulus")
}

fn inner_vk_hash_bits_var(
    cs: ConstraintSystemRef<Fr6>,
    vk: &snark::VerifyingKeyVar<MNT4_753, MNT4PairingVar>,
) -> Result<Vec<Boolean<Fr6>>, SynthesisError> {
    let (g1s, g2s) = snark::vk_var_points(vk);
    let mut coordinates = Vec::new();
    for g in g1s {
        let affine = g.to_affine()?;
        coordinates.extend([affine.x, affine.y]);
    }
    for g in g2s {
        let affine = g.to_affine()?;
        coordinates.extend([affine.x.c0, affine.x.c1, affine.y.c0, affine.y.c1]);
    }
    let mut sponge = PoseidonSpongeVar::new(cs, &poseidon_params::mnt6_753_fr_poseidon_config());
    sponge.absorb(&coordinates)?;
    let digest = sponge.squeeze_field_elements(1)?.remove(0);
    let mut bits = digest.to_bits_le()?;
    bits.truncate(VK_HASH_BITS);
    Ok(bits)
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct WrapCircuit<const N: usize> {

    pub inner_vk: VerifyingKey<MNT4_753>,
    pub inner_proof: Option<Proof<MNT4_753>>,
    pub inner_public_inputs: Option<[Fr4; N]>,
}

impl<const N: usize> ConstraintSynthesizer<Fr6> for WrapCircuit<N> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr6>) -> Result<(), SynthesisError> {

        let bit_len = Fr4::MODULUS_BIT_SIZE as usize;
        let mut per_value_bits: Vec<Vec<Boolean<Fr6>>> = Vec::with_capacity(N);
        for i in 0..N {
            let value_bits: Option<Vec<bool>> =
                self.inner_public_inputs.as_ref().map(|v| v[i].into_bigint().to_bits_le());
            let bits: Vec<Boolean<Fr6>> = (0..bit_len)
                .map(|j| Boolean::new_witness(cs.clone(), || opt(&value_bits.as_ref().map(|b| b[j]))))
                .collect::<Result<_, _>>()?;
            per_value_bits.push(bits);
        }

        let vk_var = VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
            cs.clone(),
            || Ok(self.inner_vk.clone()),
            AllocationMode::Witness,
        )?;
        let hash_bits = inner_vk_hash_bits_var(cs.clone(), &vk_var)?;
        let claimed_bits = &per_value_bits[N - 1];
        for (claimed, actual) in claimed_bits.iter().zip(&hash_bits) {
            claimed.enforce_equal(actual)?;
        }
        for claimed in &claimed_bits[VK_HASH_BITS..] {
            claimed.enforce_equal(&Boolean::FALSE)?;
        }
        let proof_var = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs.clone(), || opt(&self.inner_proof))?;
        let pvk = vk_var.prepare()?;
        verify_mnt4(&pvk, &per_value_bits, &proof_var)?.enforce_equal(&Boolean::TRUE)?;

        for bits in &per_value_bits {
            for chunk in bits.chunks(CHUNK_BITS) {
                let chunk_fp = Boolean::le_bits_to_fp(chunk)?;
                let public_chunk = Fp6::new_input(cs.clone(), || chunk_fp.value())?;
                chunk_fp.enforce_equal(&public_chunk)?;
            }
        }

        Ok(())
    }
}

pub fn combine_chunks_var(chunk_bits: &[Vec<Boolean<Fr4>>]) -> Result<FpVar<Fr4>, SynthesisError> {
    let base = Fr4::from(2u64).pow([CHUNK_BITS as u64]);
    let mut acc = FpVar::<Fr4>::zero();
    let mut place = FpVar::<Fr4>::one();
    for bits in chunk_bits {
        let low_bits = &bits[..CHUNK_BITS.min(bits.len())];
        let value = Boolean::le_bits_to_fp(low_bits)?;
        acc += &value * &place;
        place *= FpVar::<Fr4>::constant(base);
    }
    Ok(acc)
}

pub fn public_input_chunks(values: &[Fr4]) -> Vec<Fr6> {
    let bit_len = Fr4::MODULUS_BIT_SIZE as usize;
    let mut out = Vec::new();
    for v in values {
        let mut bits = v.into_bigint().to_bits_le();
        bits.truncate(bit_len);
        for chunk in bits.chunks(CHUNK_BITS) {
            let mut acc = Fr6::from(0u64);
            let mut place = Fr6::from(1u64);
            for &b in chunk {
                if b {
                    acc += place;
                }
                place *= Fr6::from(2u64);
            }
            out.push(acc);
        }
    }
    out
}

pub fn shaped_inner_vk(n: usize) -> VerifyingKey<MNT4_753> {
    snark::shaped_vk::<MNT4_753>(n)
}

pub fn setup<const N: usize, R: RngCore + CryptoRng>(
    rng: &mut R,
) -> Result<(ProvingKey<MNT6_753>, VerifyingKey<MNT6_753>), SynthesisError> {

    let dummy_proof = Proof::<MNT4_753> {
        a: ark_mnt4_753::G1Affine::identity(),
        b: ark_mnt4_753::G2Affine::identity(),
        c: ark_mnt4_753::G1Affine::identity(),
    };
    let circuit = WrapCircuit::<N> { inner_vk: shaped_inner_vk(N), inner_proof: Some(dummy_proof), inner_public_inputs: None };
    Snark::<MNT6_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove<const N: usize, R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT6_753>,
    circuit: WrapCircuit<N>,
    rng: &mut R,
) -> Result<Proof<MNT6_753>, SynthesisError> {
    Snark::<MNT6_753>::prove(pk, circuit, rng)
}

pub fn verify(
    vk: &VerifyingKey<MNT6_753>,
    public_inputs: &[Fr6],
    proof: &Proof<MNT6_753>,
) -> Result<bool, SynthesisError> {
    Snark::<MNT6_753>::verify(vk, public_inputs, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(not(feature = "groth16"))]
    use ark_crypto_primitives::snark::BooleanInputVar;
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn compact_scalar_mul_matches_the_library() {
        use ark_ec::{CurveGroup, PrimeGroup};
        use ark_relations::r1cs::ConstraintSystem;
        type G1Var = ark_mnt4_753::constraints::G1Var;
        let n = <ark_mnt4_753::Fr as PrimeField>::MODULUS_BIT_SIZE as usize;
        let scalar_bits = |x: ark_mnt4_753::Fr| x.into_bigint().to_bits_le()[..n].to_vec();
        let mut cases: Vec<Vec<bool>> = vec![
            vec![false; n],
            vec![true; n],
            scalar_bits(-ark_mnt4_753::Fr::from(1u64)),
            scalar_bits(-ark_mnt4_753::Fr::from(2u64)),
            scalar_bits(ark_mnt4_753::Fr::from(1u64)),
            scalar_bits(ark_mnt4_753::Fr::from(2u64)),
            scalar_bits(ark_mnt4_753::Fr::from(u64::MAX)),
            vec![true],
            vec![false, true],
        ];
        let mut top = vec![false; n];
        top[n - 1] = true;
        cases.push(top);

        let bases = [
            ark_mnt4_753::G1Projective::generator() * ark_mnt4_753::Fr::from(7u64),
            ark_mnt4_753::G1Projective::default(),
        ];
        for base in bases {
            for bits in &cases {
                let cs = ConstraintSystem::<Fr6>::new_ref();
                let base_var = G1Var::new_witness(cs.clone(), || Ok(base)).unwrap();
                let bit_vars: Vec<Boolean<Fr6>> =
                    bits.iter().map(|b| Boolean::new_witness(cs.clone(), || Ok(*b)).unwrap()).collect();
                let ours = scalar_mul_le_compact(&base_var, &bit_vars).unwrap().value().unwrap();
                let theirs = base_var.scalar_mul_le(bit_vars.iter()).unwrap().value().unwrap();
                assert_eq!(ours.into_affine(), theirs.into_affine(), "{} bits", bits.len());
                assert!(cs.is_satisfied().unwrap());
            }
        }
    }

    #[cfg(not(feature = "groth16"))]
    #[test]
    fn report_inner_verifier_costs() {
        use ark_crypto_primitives::snark::SNARKGadget;
        use ark_ec::{CurveGroup, PrimeGroup};
        use ark_r1cs_std::alloc::AllocationMode;
        use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
        let g1 = ark_mnt4_753::G1Projective::generator().into_affine();
        let g2 = ark_mnt4_753::G2Projective::generator().into_affine();
        for n in [7usize, 8] {
            let vk = VerifyingKey::<MNT4_753> {
                h_g2: g2,
                g_alpha_g1: g1,
                h_beta_g2: g2,
                g_gamma_g1: g1,
                h_gamma_g2: g2,
                query: vec![g1; n + 1],
            };
            for witness_vk in [false, true] {
                let cs = ConstraintSystem::<Fr6>::new_ref();
                cs.set_mode(SynthesisMode::Setup);
                let vk_var = if witness_vk {
                    VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
                        cs.clone(),
                        || Ok(vk.clone()),
                        AllocationMode::Witness,
                    )
                    .unwrap()
                } else {
                    ark_gm17::constraints::VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(cs.clone(), &vk)
                        .unwrap()
                };
                let start = cs.num_constraints();
                let pvk = vk_var.prepare().unwrap();
                let after_prepare = cs.num_constraints();
                let bits: Vec<Vec<Boolean<Fr6>>> = (0..n)
                    .map(|_| {
                        (0..Fr4::MODULUS_BIT_SIZE as usize)
                            .map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap())
                            .collect()
                    })
                    .collect();
                let input = BooleanInputVar::<Fr4, Fr6>::new(bits);
                let dummy = Proof::<MNT4_753> { a: g1, b: g2, c: g1 };
                let proof = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs.clone(), || Ok(dummy)).unwrap();
                let before_verify = cs.num_constraints();
                let _ = VerifierGadget::<MNT4_753, MNT4PairingVar>::verify_with_processed_vk(&pvk, &input, &proof)
                    .unwrap();
                println!(
                    "N={n} vk {:<8}: prepare {:>7}  verify {:>8}  verifier total {:>8}",
                    if witness_vk { "witness" } else { "constant" },
                    after_prepare - start,
                    cs.num_constraints() - before_verify,
                    cs.num_constraints() - before_verify + after_prepare - start,
                );
            }
        }
    }

    #[derive(Clone, Default)]
    struct Toy {
        a: Option<Fr4>,
        b: Option<Fr4>,
        c: Option<Fr4>,
        vk_hash: Option<Fr4>,
    }
    impl ConstraintSynthesizer<Fr4> for Toy {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr4>) -> Result<(), SynthesisError> {
            let a = FpVar::new_input(cs.clone(), || opt(&self.a))?;
            let _vk_hash = FpVar::new_input(cs.clone(), || opt(&self.vk_hash))?;
            let b = FpVar::new_witness(cs.clone(), || opt(&self.b))?;
            let c = FpVar::new_witness(cs.clone(), || opt(&self.c))?;
            (&a * &b).enforce_equal(&c)
        }
    }

    fn toy_proof(claimed_hash: Option<Fr4>) -> (VerifyingKey<MNT4_753>, Proof<MNT4_753>, [Fr4; 2]) {
        let mut rng = StdRng::seed_from_u64(7);
        let (pk, vk) = Snark::<MNT4_753>::circuit_specific_setup(Toy::default(), &mut rng).unwrap();
        let a = Fr4::from(6u64);
        let vk_hash = claimed_hash.unwrap_or_else(|| inner_vk_hash(&vk));
        let circuit = Toy { a: Some(a), b: Some(Fr4::from(7u64)), c: Some(Fr4::from(42u64)), vk_hash: Some(vk_hash) };
        let proof = Snark::<MNT4_753>::prove(&pk, circuit, &mut rng).unwrap();
        assert!(Snark::<MNT4_753>::verify(&vk, &[a, vk_hash], &proof).unwrap());
        (vk, proof, [a, vk_hash])
    }

    fn wrap_satisfied(vk: VerifyingKey<MNT4_753>, proof: Proof<MNT4_753>, inputs: [Fr4; 2]) -> bool {
        let cs = ark_relations::r1cs::ConstraintSystem::<Fr6>::new_ref();
        WrapCircuit::<2> { inner_vk: vk, inner_proof: Some(proof), inner_public_inputs: Some(inputs) }
            .generate_constraints(cs.clone())
            .unwrap();
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn report_wrap_constraints() {
        use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
        let dummy = Proof::<MNT4_753> {
            a: ark_mnt4_753::G1Affine::identity(),
            b: ark_mnt4_753::G2Affine::identity(),
            c: ark_mnt4_753::G1Affine::identity(),
        };
        let cs = ConstraintSystem::<Fr6>::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        WrapCircuit::<8> { inner_vk: shaped_inner_vk(8), inner_proof: Some(dummy), inner_public_inputs: None }
            .generate_constraints(cs.clone())
            .unwrap();
        cs.finalize();
        let m = cs.to_matrices().unwrap();
        println!(
            "WrapCircuit<8>: {} constraints, {} witness variables, nonzeros A {} B {} C {}",
            cs.num_constraints(),
            cs.num_witness_variables(),
            m.a_num_non_zero,
            m.b_num_non_zero,
            m.c_num_non_zero,
        );
    }

    #[cfg(not(feature = "groth16"))]
    #[test]
    fn report_wrap_density() {
        use ark_ec::PrimeGroup;
        use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
        fn report(name: &str, build: impl FnOnce(ConstraintSystemRef<Fr6>)) {
            let cs = ConstraintSystem::<Fr6>::new_ref();
            cs.set_mode(SynthesisMode::Setup);
            build(cs.clone());
            cs.finalize();
            let m = cs.to_matrices().unwrap();
            println!(
                "{name:<28} constraints {:>7}  nonzeros A {:>9} B {:>9} C {:>8}",
                cs.num_constraints(),
                m.a_num_non_zero,
                m.b_num_non_zero,
                m.c_num_non_zero
            );
        }
        let witness_vk = |cs: ConstraintSystemRef<Fr6>| {
            VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
                cs,
                || Ok(shaped_inner_vk(8)),
                AllocationMode::Witness,
            )
            .unwrap()
        };
        report("poseidon, 60 elements", |cs| {
            let xs: Vec<Fp6> = (0..60).map(|_| Fp6::new_witness(cs.clone(), || Ok(Fr6::from(1u64))).unwrap()).collect();
            let mut sponge = PoseidonSpongeVar::new(cs, &poseidon_params::mnt6_753_fr_poseidon_config());
            sponge.absorb(&xs).unwrap();
            sponge.squeeze_field_elements(1).unwrap();
        });
        report("vk hash (to_affine + poseidon)", |cs| {
            let vk = witness_vk(cs.clone());
            inner_vk_hash_bits_var(cs, &vk).unwrap();
        });
        report("prepare witness vk", |cs| {
            witness_vk(cs).prepare().unwrap();
        });
        report("input sum, witness query", |cs| {
            let vk = witness_vk(cs.clone());
            let mut g_psi = vk.query[0].clone();
            for b in vk.query.iter().skip(1) {
                let bits: Vec<Boolean<Fr6>> =
                    (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect();
                g_psi += b.scalar_mul_le(bits.iter()).unwrap();
            }
        });
        report("input sum, constant query", |cs| {
            let vk = ark_gm17::constraints::VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(
                cs.clone(),
                shaped_inner_vk(8),
            )
            .unwrap();
            let mut g_psi = vk.query[0].clone();
            for b in vk.query.iter().skip(1) {
                let bits: Vec<Boolean<Fr6>> =
                    (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect();
                g_psi += b.scalar_mul_le(bits.iter()).unwrap();
            }
        });
        report("miller+final exp, witness", |cs| {
            use ark_r1cs_std::pairing::PairingVar;
            let pvk = witness_vk(cs.clone()).prepare().unwrap();
            let g1 = MNT4PairingVar::prepare_g1(&pvk.query[0]).unwrap();
            let ml = MNT4PairingVar::miller_loop(&[g1], &[pvk.h_gamma_pc.clone()]).unwrap();
            let _ = MNT4PairingVar::final_exponentiation(&ml).unwrap();
        });
        report("miller+final exp, constant", |cs| {
            use ark_r1cs_std::pairing::PairingVar;
            let vk = ark_gm17::constraints::VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(
                cs.clone(),
                shaped_inner_vk(8),
            )
            .unwrap();
            let pvk = vk.prepare().unwrap();
            let p = <MNT4PairingVar as PairingVar<MNT4_753>>::G1Var::new_witness(cs.clone(), || {
                Ok(ark_mnt4_753::G1Projective::generator())
            })
            .unwrap();
            let g1 = MNT4PairingVar::prepare_g1(&p).unwrap();
            let ml = MNT4PairingVar::miller_loop(&[g1], &[pvk.h_gamma_pc.clone()]).unwrap();
            let _ = MNT4PairingVar::final_exponentiation(&ml).unwrap();
        });
        report("verify, witness vk, ours", |cs| {
            let pvk = witness_vk(cs.clone()).prepare().unwrap();
            let bits: Vec<Vec<Boolean<Fr6>>> = (0..8)
                .map(|_| (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect())
                .collect();
            let g1 = ark_mnt4_753::G1Affine::identity();
            let dummy = Proof::<MNT4_753> { a: g1, b: ark_mnt4_753::G2Affine::identity(), c: g1 };
            let proof = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs, || Ok(dummy)).unwrap();
            let _ = verify_mnt4(&pvk, &bits, &proof).unwrap();
        });
        report("verify, witness vk, gadget", |cs| {
            let pvk = witness_vk(cs.clone()).prepare().unwrap();
            let bits: Vec<Vec<Boolean<Fr6>>> = (0..8)
                .map(|_| (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect())
                .collect();
            let g1 = ark_mnt4_753::G1Affine::identity();
            let dummy = Proof::<MNT4_753> { a: g1, b: ark_mnt4_753::G2Affine::identity(), c: g1 };
            let proof = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs, || Ok(dummy)).unwrap();
            let _ = VerifierGadget::<MNT4_753, MNT4PairingVar>::verify_with_processed_vk(
                &pvk,
                &BooleanInputVar::<Fr4, Fr6>::new(bits),
                &proof,
            )
            .unwrap();
        });
    }

    #[test]
    fn vk_hash_gadget_matches_native() {
        let vk = toy_proof(None).0;
        let cs = ark_relations::r1cs::ConstraintSystem::<Fr6>::new_ref();
        let vk_var = VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
            cs.clone(),
            || Ok(vk.clone()),
            AllocationMode::Witness,
        )
        .unwrap();
        let bits: Vec<bool> = inner_vk_hash_bits_var(cs, &vk_var).unwrap().iter().map(|b| b.value().unwrap()).collect();
        let expected = inner_vk_hash(&vk).into_bigint().to_bits_le();
        assert_eq!(bits, expected[..VK_HASH_BITS]);
        assert!(expected[VK_HASH_BITS..].iter().all(|b| !b));
    }

    #[test]
    fn wrap_accepts_a_proof_carrying_its_own_vk_hash() {
        let (vk, proof, inputs) = toy_proof(None);
        assert!(wrap_satisfied(vk, proof, inputs));
    }

    #[test]
    fn wrap_rejects_a_proof_naming_another_vk() {
        let other = inner_vk_hash(&shaped_inner_vk(1));
        let (vk, proof, inputs) = toy_proof(Some(other));
        assert!(!wrap_satisfied(vk, proof, inputs));
    }

    #[test]
    fn proving_wraps_a_proof_end_to_end() {
        let mut rng = StdRng::seed_from_u64(8);
        let (vk, proof, inputs) = toy_proof(None);

        let (wrap_pk, wrap_vk) = setup::<2, _>(&mut rng).unwrap();
        let wrap_circuit = WrapCircuit::<2> { inner_vk: vk, inner_proof: Some(proof), inner_public_inputs: Some(inputs) };
        let wrap_proof = prove::<2, _>(&wrap_pk, wrap_circuit, &mut rng).unwrap();

        let expected_public_inputs = public_input_chunks(&inputs);
        assert_eq!(expected_public_inputs.len(), 2 * chunks_per_value());
        assert!(verify(&wrap_vk, &expected_public_inputs, &wrap_proof).unwrap());

        let mut tampered = expected_public_inputs.clone();
        tampered[0] += Fr6::from(1u64);
        assert!(!verify(&wrap_vk, &tampered, &wrap_proof).unwrap());
    }
}
