use ark_crypto_primitives::snark::{BooleanInputVar, SNARKGadget};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_groth16::{
    constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar},
    Groth16, Proof, ProvingKey, VerifyingKey,
};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_lib::Fr as Fr4;

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
            let value_bits: Option<Vec<bool>> = self
                .inner_public_inputs
                .as_ref()
                .map(|v| v[i].into_bigint().to_bits_le());
            let bits: Vec<Boolean<Fr6>> = (0..bit_len)
                .map(|j| {
                    Boolean::new_witness(cs.clone(), || opt(&value_bits.as_ref().map(|b| b[j])))
                })
                .collect::<Result<_, _>>()?;
            per_value_bits.push(bits);
        }
        let input_var = BooleanInputVar::<Fr4, Fr6>::new(per_value_bits.clone());

        let vk_var =
            VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(cs.clone(), &self.inner_vk)?;
        let proof_var = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs.clone(), || {
            opt(&self.inner_proof)
        })?;
        let pvk = vk_var.prepare()?;
        let ok = Groth16VerifierGadget::<MNT4_753, MNT4PairingVar>::verify_with_processed_vk(
            &pvk, &input_var, &proof_var,
        )?;
        ok.enforce_equal(&Boolean::TRUE)?;

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

pub fn setup<const N: usize, R: RngCore + CryptoRng>(
    inner_vk: VerifyingKey<MNT4_753>,
    rng: &mut R,
) -> Result<(ProvingKey<MNT6_753>, VerifyingKey<MNT6_753>), SynthesisError> {
    let dummy_proof = Proof::<MNT4_753> {
        a: ark_mnt4_753::G1Affine::identity(),
        b: ark_mnt4_753::G2Affine::identity(),
        c: ark_mnt4_753::G1Affine::identity(),
    };
    let circuit = WrapCircuit::<N> {
        inner_vk,
        inner_proof: Some(dummy_proof),
        inner_public_inputs: None,
    };
    Groth16::<MNT6_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove<const N: usize, R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT6_753>,
    circuit: WrapCircuit<N>,
    rng: &mut R,
) -> Result<Proof<MNT6_753>, SynthesisError> {
    Groth16::<MNT6_753>::prove(pk, circuit, rng)
}

pub fn verify(
    vk: &VerifyingKey<MNT6_753>,
    public_inputs: &[Fr6],
    proof: &Proof<MNT6_753>,
) -> Result<bool, SynthesisError> {
    Groth16::<MNT6_753>::verify(vk, public_inputs, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn wraps_a_genesis_spend_proof_end_to_end() {
        let mut rng = StdRng::seed_from_u64(7);

        use ark_relations::r1cs::ConstraintSystemRef;
        use cloakkchain_lib::Fr;

        #[derive(Clone, Default)]
        struct Toy {
            a: Option<Fr>,
            b: Option<Fr>,
            c: Option<Fr>,
        }
        impl ConstraintSynthesizer<Fr> for Toy {
            fn generate_constraints(
                self,
                cs: ConstraintSystemRef<Fr>,
            ) -> Result<(), SynthesisError> {
                let a = FpVar::new_input(cs.clone(), || opt(&self.a))?;
                let b = FpVar::new_witness(cs.clone(), || opt(&self.b))?;
                let c = FpVar::new_input(cs.clone(), || opt(&self.c))?;
                (&a * &b).enforce_equal(&c)
            }
        }

        let (toy_pk, toy_vk) =
            Groth16::<MNT4_753>::circuit_specific_setup(Toy::default(), &mut rng).unwrap();
        let a = Fr::from(6u64);
        let b = Fr::from(7u64);
        let c = Fr::from(42u64);
        let toy_proof = Groth16::<MNT4_753>::prove(
            &toy_pk,
            Toy {
                a: Some(a),
                b: Some(b),
                c: Some(c),
            },
            &mut rng,
        )
        .unwrap();
        assert!(Groth16::<MNT4_753>::verify(&toy_vk, &[a, c], &toy_proof).unwrap());

        let (wrap_pk, wrap_vk) = setup::<2, _>(toy_vk, &mut rng).unwrap();
        let wrap_circuit = WrapCircuit::<2> {
            inner_vk: toy_pk.vk.clone(),
            inner_proof: Some(toy_proof),
            inner_public_inputs: Some([a, c]),
        };
        let wrap_proof = prove::<2, _>(&wrap_pk, wrap_circuit, &mut rng).unwrap();

        let expected_public_inputs = public_input_chunks(&[a, c]);
        assert_eq!(expected_public_inputs.len(), 2 * chunks_per_value());
        assert!(verify(&wrap_vk, &expected_public_inputs, &wrap_proof).unwrap());

        let mut tampered = expected_public_inputs.clone();
        tampered[0] += Fr6::from(1u64);
        assert!(!verify(&wrap_vk, &tampered, &wrap_proof).unwrap());
    }
}
