use ark_crypto_primitives::snark::{constraints::SNARKGadget, BooleanInputVar};
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar,
};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField};
use cloakkchain_circuit_wrap::snark::{
    PreparedVerifyingKeyVar, Proof, ProofVar, ProvingKey, Snark, VerifierGadget, VerifyingKey, VerifyingKeyVar,
};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_circuit_wrap::{chunks_per_value, combine_chunks_var, public_input_chunks, Fr6, CHUNK_BITS};
use cloakkchain_lib::{
    derive_nullifier, derive_tag_key, genesis_pk, owner_pk_to_field_pair, poseidon_params, Anchor, Coin, Fr,
    IndexedLeaf, LeafOpening, NonMembershipWitness, Occurrence, OwnerPk, OwnerScalar, ParentWitness,
    SpendPublicValues, WindowWitness, TAG_DOMAIN, TAG_KEY_DOMAIN, TREE_DEPTH,
};

type Fp = FpVar<Fr>;
type G1Var = ark_mnt6_753::constraints::G1Var;
type MNT6PairingVar = ark_mnt6_753::constraints::PairingVar;

pub use cloakkchain_lib::MAX_INPUTS;

#[cfg(not(feature = "single-output"))]
pub const MAX_OUTPUTS: usize = 2;
#[cfg(feature = "single-output")]
pub const MAX_OUTPUTS: usize = 1;

pub const SPEND_PUBLIC_INPUT_COUNT: usize = MAX_OUTPUTS + 5 + 3 * MAX_INPUTS;

pub const FOLD_BATCH: usize = 64;

const PARENT_OUTPUT_COMMITMENTS_START: usize = 0;
const PARENT_ANCHOR_SIZE: usize = MAX_OUTPUTS;
const PARENT_ANCHOR_BOARD_ROOT: usize = MAX_OUTPUTS + 1;
const PARENT_ANCHOR_NULLIFIER_ROOT: usize = MAX_OUTPUTS + 2;
const PARENT_NULLIFIERS_START: usize = MAX_OUTPUTS + 3;
const PARENT_TAG_KEYS_START: usize = PARENT_NULLIFIERS_START + MAX_INPUTS;
const PARENT_WINDOW_HEADS_START: usize = PARENT_TAG_KEYS_START + MAX_INPUTS;
const PARENT_ORIGIN_VK_HASH: usize = SPEND_PUBLIC_INPUT_COUNT - 2;
const PARENT_VK_HASH: usize = SPEND_PUBLIC_INPUT_COUNT - 1;

pub fn pad_outputs(real: &[Fr]) -> [Fr; MAX_OUTPUTS] {
    let mut out = [Fr::from(0u64); MAX_OUTPUTS];
    out[..real.len()].copy_from_slice(real);
    out
}

pub fn pad_inputs(real: &[Fr]) -> [Fr; MAX_INPUTS] {
    let mut out = [Fr::from(0u64); MAX_INPUTS];
    out[..real.len()].copy_from_slice(real);
    out
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct StepStatement {
    pub public_values: SpendPublicValues,
    pub window_heads: [Fr; MAX_INPUTS],
    pub origin_vk_hash: Fr,
    pub vk_hash: Fr,
}

impl StepStatement {

    pub fn of_spend(public_values: SpendPublicValues, vk_hash: Fr) -> Self {
        Self { public_values, window_heads: [Fr::from(0u64); MAX_INPUTS], origin_vk_hash: Fr::from(0u64), vk_hash }
    }

    pub fn public_inputs(&self) -> [Fr; SPEND_PUBLIC_INPUT_COUNT] {
        spend_public_inputs(&self.public_values, &self.window_heads, self.origin_vk_hash, self.vk_hash)
    }

    pub fn folded(&self, input: usize, occurrences: &[Occurrence], fold_vk_hash: Fr) -> Self {
        let mut window_heads = self.window_heads;
        window_heads[input] = occurrences.iter().fold(window_heads[input], |head, o| o.link(head));
        let origin_vk_hash = if self.vk_hash == fold_vk_hash { self.origin_vk_hash } else { self.vk_hash };
        Self { public_values: self.public_values.clone(), window_heads, origin_vk_hash, vk_hash: fold_vk_hash }
    }
}

pub fn spend_public_inputs(
    pv: &SpendPublicValues,
    window_heads: &[Fr; MAX_INPUTS],
    origin_vk_hash: Fr,
    vk_hash: Fr,
) -> [Fr; SPEND_PUBLIC_INPUT_COUNT] {
    let mut out = pad_outputs(&pv.output_commitments).to_vec();
    out.push(Fr::from(pv.anchor.size));
    out.push(pv.anchor.board_root);
    out.push(pv.anchor.nullifier_root);
    out.extend(pad_inputs(&pv.nullifiers));
    out.extend(pad_inputs(&pv.tag_keys));
    out.extend(window_heads);
    out.push(origin_vk_hash);
    out.push(vk_hash);
    out.try_into().expect("the layout above has SPEND_PUBLIC_INPUT_COUNT values")
}

fn poseidon_hash_var(cs: ConstraintSystemRef<Fr>, inputs: &[Fp]) -> Result<Fp, SynthesisError> {
    let mut sponge = PoseidonSpongeVar::new(cs, &poseidon_params::mnt4_753_fr_poseidon_config());
    sponge.absorb(&inputs.to_vec())?;
    Ok(sponge.squeeze_field_elements(1)?.remove(0))
}

fn fold_bits_le_var(cs: ConstraintSystemRef<Fr>, bits: &[Boolean<Fr>]) -> Result<Fp, SynthesisError> {
    let chunks: Vec<Fp> = bits
        .chunks(248)
        .map(Boolean::le_bits_to_fp)
        .collect::<Result<_, _>>()?;
    poseidon_hash_var(cs, &chunks)
}

fn merkle_combine_var(cs: ConstraintSystemRef<Fr>, l: &Fp, r: &Fp) -> Result<Fp, SynthesisError> {
    poseidon_hash_var(cs, &[l.clone(), r.clone()])
}

fn compute_root_from_path_var(
    cs: ConstraintSystemRef<Fr>,
    leaf: &Fp,
    slot_bits_le: &[Boolean<Fr>],
    path: &[Fp],
) -> Result<Fp, SynthesisError> {
    let mut current = leaf.clone();
    for (bit, sibling) in slot_bits_le.iter().zip(path.iter()) {
        let left = Fp::conditionally_select(bit, sibling, &current)?;
        let right = Fp::conditionally_select(bit, &current, sibling)?;
        current = merkle_combine_var(cs.clone(), &left, &right)?;
    }
    Ok(current)
}

fn bits_msb_is_lt(a: &[Boolean<Fr>], b: &[Boolean<Fr>]) -> Result<Boolean<Fr>, SynthesisError> {
    assert_eq!(a.len(), b.len());
    let mut lt = Boolean::FALSE;
    let mut equal_so_far = Boolean::TRUE;
    for (x, y) in a.iter().zip(b) {
        lt = &lt | &(&equal_so_far & &(&!x.clone() & y));
        equal_so_far = &equal_so_far & &x.is_eq(y)?;
    }
    Ok(lt)
}

fn fp_is_lt(a: &Fp, b: &Fp) -> Result<Boolean<Fr>, SynthesisError> {
    let mut a_bits = a.to_bits_le()?;
    let mut b_bits = b.to_bits_le()?;
    a_bits.reverse();
    b_bits.reverse();
    bits_msb_is_lt(&a_bits, &b_bits)
}

fn alloc_fp(cs: ConstraintSystemRef<Fr>, value: Option<Fr>) -> Result<Fp, SynthesisError> {
    Fp::new_witness(cs, || Ok(value.unwrap_or(Fr::from(0u64))))
}

fn alloc_path(cs: ConstraintSystemRef<Fr>, path: Option<&Vec<Fr>>) -> Result<Vec<Fp>, SynthesisError> {
    (0..TREE_DEPTH).map(|i| alloc_fp(cs.clone(), path.map(|p| p[i]))).collect()
}

fn alloc_position_bits(cs: ConstraintSystemRef<Fr>, position: Option<u64>) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    let position = position.unwrap_or(0);
    (0..TREE_DEPTH).map(|i| Boolean::new_witness(cs.clone(), || Ok((position >> i) & 1 == 1))).collect()
}

struct IndexedLeafVar {
    value: Fp,
    next_value: Fp,
    next_index: Fp,
    occ: Fp,
}

impl IndexedLeafVar {
    fn hash(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        poseidon_hash_var(cs, &[self.value.clone(), self.next_value.clone(), self.next_index.clone(), self.occ.clone()])
    }

    fn new_witness(cs: ConstraintSystemRef<Fr>, leaf: Option<&IndexedLeaf>) -> Result<Self, SynthesisError> {
        Ok(Self {
            value: alloc_fp(cs.clone(), leaf.map(|l| l.value))?,
            next_value: alloc_fp(cs.clone(), leaf.map(|l| l.next_value))?,
            next_index: alloc_fp(cs.clone(), leaf.map(|l| Fr::from(l.next_index)))?,
            occ: alloc_fp(cs, leaf.map(|l| l.occ))?,
        })
    }

    fn brackets(&self, target: &Fp) -> Result<Boolean<Fr>, SynthesisError> {
        Ok(&fp_is_lt(&self.value, target)? & &fp_is_lt(target, &self.next_value)?)
    }
}

fn verify_nonmembership_var(
    cs: ConstraintSystemRef<Fr>,
    root: &Fp,
    target: &Fp,
    witness: Option<&NonMembershipWitness>,
) -> Result<Boolean<Fr>, SynthesisError> {
    let low_leaf = IndexedLeafVar::new_witness(cs.clone(), witness.map(|w| &w.low_leaf))?;
    let index_bits = alloc_position_bits(cs.clone(), witness.map(|w| w.low_leaf_index))?;
    let path = alloc_path(cs.clone(), witness.map(|w| &w.sibling_path))?;
    let leaf_hash = low_leaf.hash(cs.clone())?;
    let computed_root = compute_root_from_path_var(cs, &leaf_hash, &index_bits, &path)?;
    Ok(&low_leaf.brackets(target)? & &computed_root.is_eq(root)?)
}

fn opt<T: Clone>(o: &Option<T>) -> Result<T, SynthesisError> {
    o.clone().ok_or(SynthesisError::AssignmentMissing)
}

struct CoinVar {
    value: UInt64<Fr>,
    rand: Fp,
    owner_pk_x: Fp,
    owner_pk_y: Fp,
}

impl CoinVar {

    fn new_witness(cs: ConstraintSystemRef<Fr>, coin: &Option<Coin>) -> Result<Self, SynthesisError> {
        let owner_xy = coin.as_ref().map(|c| owner_pk_to_field_pair(&c.owner_pk));
        Ok(Self {
            value: UInt64::new_witness(cs.clone(), || Ok(coin.as_ref().map(|c| c.value).unwrap_or(0)))?,
            rand: alloc_fp(cs.clone(), coin.as_ref().map(|c| c.rand()))?,
            owner_pk_x: alloc_fp(cs.clone(), owner_xy.map(|(x, _)| x))?,
            owner_pk_y: alloc_fp(cs, owner_xy.map(|(_, y)| y))?,
        })
    }

    fn commitment(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        let value_fp = self.value.to_fp()?;
        poseidon_hash_var(cs, &[value_fp, self.rand.clone(), self.owner_pk_x.clone(), self.owner_pk_y.clone()])
    }

    fn value_or_zero(&self, is_active: &Boolean<Fr>) -> Result<Fp, SynthesisError> {
        Fp::conditionally_select(is_active, &self.value.to_fp()?, &Fp::zero())
    }
}

fn is_member(target: &Fp, list: &[Fp]) -> Result<Boolean<Fr>, SynthesisError> {
    let mut any = Boolean::FALSE;
    for item in list {
        any = &any | &target.is_eq(item)?;
    }
    Ok(any)
}

fn alloc_active_flags<const N: usize>(
    cs: ConstraintSystemRef<Fr>,
    present: &[bool; N],
) -> Result<[Boolean<Fr>; N], SynthesisError> {
    let mut out: [Boolean<Fr>; N] = std::array::from_fn(|_| Boolean::TRUE);
    for i in 1..N {
        out[i] = Boolean::new_witness(cs.clone(), || Ok(present[i]))?;
    }
    Ok(out)
}

fn gate(check: Boolean<Fr>, is_active: &Boolean<Fr>) -> Boolean<Fr> {
    &check | &!is_active.clone()
}

fn generator_var(cs: ConstraintSystemRef<Fr>) -> Result<G1Var, SynthesisError> {
    G1Var::new_constant(cs, ark_mnt6_753::G1Projective::generator())
}

fn coin_tag_var(cs: ConstraintSystemRef<Fr>, tag_key: &Fp, nullifier: &Fp, outputs_hash: &Fp) -> Result<Fp, SynthesisError> {
    poseidon_hash_var(
        cs,
        &[Fp::constant(Fr::from(TAG_DOMAIN)), tag_key.clone(), nullifier.clone(), outputs_hash.clone()],
    )
}

struct LeafOpeningVar {
    slot: Fp,
    slot_bits: Vec<Boolean<Fr>>,
    ciphertext_commitment: Fp,
    outputs_hash: Fp,
    nullifiers: Vec<Fp>,
    tags: Vec<Fp>,
    prev_board_root: Fp,
    prev_nullifier_root: Fp,
}

impl LeafOpeningVar {
    fn new_witness(cs: ConstraintSystemRef<Fr>, leaf: Option<&LeafOpening>) -> Result<Self, SynthesisError> {
        let slot_bits = alloc_position_bits(cs.clone(), leaf.map(|l| l.slot))?;
        let input = |i: usize| leaf.and_then(|l| l.inputs.get(i));
        Ok(Self {
            slot: Boolean::le_bits_to_fp(&slot_bits)?,
            slot_bits,
            ciphertext_commitment: alloc_fp(cs.clone(), leaf.map(|l| l.ciphertext_commitment))?,
            outputs_hash: alloc_fp(cs.clone(), leaf.map(|l| l.outputs_hash))?,
            nullifiers: (0..MAX_INPUTS)
                .map(|i| alloc_fp(cs.clone(), input(i).map(|p| p.nullifier)))
                .collect::<Result<_, _>>()?,
            tags: (0..MAX_INPUTS)
                .map(|i| alloc_fp(cs.clone(), input(i).map(|p| p.tag)))
                .collect::<Result<_, _>>()?,
            prev_board_root: alloc_fp(cs.clone(), leaf.map(|l| l.prev_board_root))?,
            prev_nullifier_root: alloc_fp(cs, leaf.map(|l| l.prev_nullifier_root))?,
        })
    }

    fn hash(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        let mut preimage = vec![self.slot.clone(), self.ciphertext_commitment.clone(), self.outputs_hash.clone()];
        for (nullifier, tag) in self.nullifiers.iter().zip(&self.tags) {
            preimage.extend([nullifier.clone(), tag.clone()]);
        }
        preimage.extend([self.prev_board_root.clone(), self.prev_nullifier_root.clone()]);
        poseidon_hash_var(cs, &preimage)
    }

    fn opens_to(
        &self,
        cs: ConstraintSystemRef<Fr>,
        path: Option<&Vec<Fr>>,
        root: &Fp,
    ) -> Result<Boolean<Fr>, SynthesisError> {
        let path = alloc_path(cs.clone(), path)?;
        let leaf = self.hash(cs.clone())?;
        compute_root_from_path_var(cs, &leaf, &self.slot_bits, &path)?.is_eq(root)
    }
}

fn occurrence_link_var(
    cs: ConstraintSystemRef<Fr>,
    previous: &Fp,
    outputs_hash: &Fp,
    tag: &Fp,
) -> Result<Fp, SynthesisError> {
    poseidon_hash_var(cs, &[previous.clone(), outputs_hash.clone(), tag.clone()])
}

fn window_opens(
    cs: ConstraintSystemRef<Fr>,
    root: &Fp,
    nullifier: &Fp,
    head: &Fp,
    witness: Option<&WindowWitness>,
) -> Result<Boolean<Fr>, SynthesisError> {
    let leaf = IndexedLeafVar::new_witness(cs.clone(), witness.map(|w| &w.leaf))?;
    let index_bits = alloc_position_bits(cs.clone(), witness.map(|w| w.leaf_index))?;
    let path = alloc_path(cs.clone(), witness.map(|w| &w.sibling_path))?;
    let leaf_hash = leaf.hash(cs.clone())?;
    let root_ok = compute_root_from_path_var(cs, &leaf_hash, &index_bits, &path)?.is_eq(root)?;

    let absent = leaf.brackets(nullifier)?;
    let member = &leaf.value.is_eq(nullifier)? & &leaf.occ.is_eq(head)?;
    let case_ok = Boolean::conditionally_select(&head.is_zero()?, &absent, &member)?;
    Ok(&root_ok & &case_ok)
}

struct FoldTarget {
    nullifier: Fp,
    tag_key: Fp,
    window_head: Fp,
}

impl FoldTarget {

    #[cfg(test)]
    fn input(pv: &ParentPublicVars, i: usize) -> Self {
        Self {
            nullifier: pv.nullifiers[i].clone(),
            tag_key: pv.tag_keys[i].clone(),
            window_head: pv.window_heads[i].clone(),
        }
    }

    fn select(pv: &ParentPublicVars, selector: &[Boolean<Fr>]) -> Result<Self, SynthesisError> {
        let pick = |values: &[Fp]| -> Result<Fp, SynthesisError> {
            let mut out = Fp::zero();
            for (bit, value) in selector.iter().zip(values) {
                out = Fp::conditionally_select(bit, value, &out)?;
            }
            Ok(out)
        };
        Ok(Self {
            nullifier: pick(&pv.nullifiers)?,
            tag_key: pick(&pv.tag_keys)?,
            window_head: pick(&pv.window_heads)?,
        })
    }
}

fn fold_batch(
    cs: ConstraintSystemRef<Fr>,
    occurrences: &[Occurrence],
    slots: usize,
    output_commitments: &[Fp],
    target: &FoldTarget,
) -> Result<(Boolean<Fr>, Fp), SynthesisError> {
    assert!(occurrences.len() <= slots, "more occurrences than slots");
    let mut all_ok = Boolean::TRUE;
    let outputs_hash = poseidon_hash_var(cs.clone(), output_commitments)?;

    let mut head = target.window_head.clone();
    let mut previous_active = Boolean::TRUE;
    for k in 0..slots {
        let occurrence = occurrences.get(k);
        let active = Boolean::new_witness(cs.clone(), || Ok(occurrence.is_some()))?;
        all_ok = &all_ok & &(&!active.clone() | &previous_active);
        previous_active = active.clone();

        let occ_outputs_hash = alloc_fp(cs.clone(), occurrence.map(|o| o.outputs_hash))?;
        let occ_tag = alloc_fp(cs.clone(), occurrence.map(|o| o.tag))?;

        let expected = coin_tag_var(cs.clone(), &target.tag_key, &target.nullifier, &occ_outputs_hash)?;
        let valid = occ_tag.is_eq(&expected)?;
        let harmless = &occ_outputs_hash.is_eq(&outputs_hash)? | &!valid;
        all_ok = &all_ok & &gate(harmless, &active);

        let linked = occurrence_link_var(cs.clone(), &head, &occ_outputs_hash, &occ_tag)?;
        head = Fp::conditionally_select(&active, &linked, &head)?;
    }
    Ok((all_ok, head))
}

struct ParentPublicVars {
    output_commitments: Vec<Fp>,
    anchor_size: Fp,
    anchor_board_root: Fp,
    anchor_nullifier_root: Fp,
    nullifiers: Vec<Fp>,
    tag_keys: Vec<Fp>,
    window_heads: Vec<Fp>,
    origin_vk_hash: Fp,
    vk_hash: Fp,
}

impl ParentPublicVars {

    fn from_values(values: &[Fp]) -> Self {
        let run = |start: usize, len: usize| values[start..start + len].to_vec();
        Self {
            output_commitments: run(PARENT_OUTPUT_COMMITMENTS_START, MAX_OUTPUTS),
            anchor_size: values[PARENT_ANCHOR_SIZE].clone(),
            anchor_board_root: values[PARENT_ANCHOR_BOARD_ROOT].clone(),
            anchor_nullifier_root: values[PARENT_ANCHOR_NULLIFIER_ROOT].clone(),
            nullifiers: run(PARENT_NULLIFIERS_START, MAX_INPUTS),
            tag_keys: run(PARENT_TAG_KEYS_START, MAX_INPUTS),
            window_heads: run(PARENT_WINDOW_HEADS_START, MAX_INPUTS),
            origin_vk_hash: values[PARENT_ORIGIN_VK_HASH].clone(),
            vk_hash: values[PARENT_VK_HASH].clone(),
        }
    }

    fn statement(&self) -> Vec<Fp> {
        let mut out = self.output_commitments.clone();
        out.extend([self.anchor_size.clone(), self.anchor_board_root.clone(), self.anchor_nullifier_root.clone()]);
        out.extend(self.nullifiers.iter().cloned());
        out.extend(self.tag_keys.iter().cloned());
        out
    }
}

fn parent_checks(
    cs: ConstraintSystemRef<Fr>,
    witness: Option<&ParentWitness>,
    pv: &ParentPublicVars,
    commitment: &Fp,
    anchor_board_root: &Fp,
) -> Result<Boolean<Fr>, SynthesisError> {
    let leaf = LeafOpeningVar::new_witness(cs.clone(), witness.map(|w| &w.leaf))?;
    let leaf_in_anchor = leaf.opens_to(cs.clone(), witness.map(|w| &w.leaf_path), anchor_board_root)?;

    let outputs_hash = poseidon_hash_var(cs.clone(), &pv.output_commitments)?;
    let mut proof_matches_entry = outputs_hash.is_eq(&leaf.outputs_hash)?;
    for (theirs, posted) in pv.nullifiers.iter().zip(&leaf.nullifiers) {
        proof_matches_entry = &proof_matches_entry & &theirs.is_eq(posted)?;
    }
    let creates_coin = is_member(commitment, &pv.output_commitments)?;

    let anchor_leaf = LeafOpeningVar::new_witness(cs.clone(), witness.map(|w| &w.anchor_leaf))?;
    let anchor_leaf_in_anchor =
        anchor_leaf.opens_to(cs.clone(), witness.map(|w| &w.anchor_leaf_path), anchor_board_root)?;
    let msb_first = |bits: &[Boolean<Fr>]| bits.iter().rev().cloned().collect::<Vec<_>>();
    let anchor_precedes_parent = !bits_msb_is_lt(&msb_first(&leaf.slot_bits), &msb_first(&anchor_leaf.slot_bits))?;
    let anchor_real = Boolean::kary_and(&[
        anchor_leaf.slot.is_eq(&pv.anchor_size)?,
        anchor_leaf.prev_board_root.is_eq(&pv.anchor_board_root)?,
        anchor_leaf.prev_nullifier_root.is_eq(&pv.anchor_nullifier_root)?,
        anchor_precedes_parent,
    ])?;

    let mut all_ok =
        Boolean::kary_and(&[leaf_in_anchor, proof_matches_entry, creates_coin, anchor_leaf_in_anchor, anchor_real])?;

    for i in 0..MAX_INPUTS {
        let used = !leaf.nullifiers[i].is_zero()?;

        let expected = coin_tag_var(cs.clone(), &pv.tag_keys[i], &leaf.nullifiers[i], &leaf.outputs_hash)?;
        let tag_ok = leaf.tags[i].is_eq(&expected)?;

        let window_ok = window_opens(
            cs.clone(),
            &leaf.prev_nullifier_root,
            &leaf.nullifiers[i],
            &pv.window_heads[i],
            witness.and_then(|w| w.windows.get(i)),
        )?;

        let input_ok = &tag_ok & &window_ok;
        all_ok = &all_ok & &gate(input_ok, &used);
    }
    Ok(all_ok)
}

#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct SpendCoreWitness {

    pub output_commitments: Option<[Fr; MAX_OUTPUTS]>,
    pub anchor: Option<Anchor>,
    pub nullifiers: Option<[Fr; MAX_INPUTS]>,
    pub tag_keys: Option<[Fr; MAX_INPUTS]>,

    pub vk_hash: Option<Fr>,

    pub pk_p: Option<OwnerPk>,
    pub sk_p: Option<OwnerScalar>,

    pub input_coins: [Option<Coin>; MAX_INPUTS],

    pub output_coins: [Option<Coin>; MAX_OUTPUTS],

    pub own_nullifier_nonmembership: [Option<NonMembershipWitness>; MAX_INPUTS],
}

impl SpendCoreWitness {

    pub fn new(
        sk: OwnerScalar,
        input_coins: &[Coin],
        output_coins: &[Coin],
        anchor: Anchor,
        nonmemberships: &[NonMembershipWitness],
        vk_hash: Fr,
    ) -> Self {
        assert!((1..=MAX_INPUTS).contains(&input_coins.len()), "1 to MAX_INPUTS inputs");
        assert_eq!(nonmemberships.len(), input_coins.len());
        let commitments: Vec<Fr> = input_coins.iter().map(Coin::commitment).collect();
        let real_outputs: Vec<Fr> = output_coins.iter().map(Coin::commitment).collect();
        let nullifiers: Vec<Fr> = commitments.iter().map(|cm| derive_nullifier(*cm, &sk)).collect();
        let tag_keys: Vec<Fr> = commitments.iter().map(|cm| derive_tag_key(&sk, *cm)).collect();
        Self {
            output_commitments: Some(pad_outputs(&real_outputs)),
            anchor: Some(anchor),
            nullifiers: Some(pad_inputs(&nullifiers)),
            tag_keys: Some(pad_inputs(&tag_keys)),
            vk_hash: Some(vk_hash),
            pk_p: Some(input_coins[0].owner_pk),
            sk_p: Some(sk),
            input_coins: std::array::from_fn(|i| input_coins.get(i).cloned()),
            output_coins: std::array::from_fn(|i| output_coins.get(i).cloned()),
            own_nullifier_nonmembership: std::array::from_fn(|i| nonmemberships.get(i).cloned()),
        }
    }

    pub fn public_values(&self) -> Option<SpendPublicValues> {
        let used = self.input_coins.iter().filter(|c| c.is_some()).count();
        Some(SpendPublicValues {
            output_commitments: self.output_commitments?.to_vec(),
            anchor: self.anchor.clone()?,
            nullifiers: self.nullifiers?[..used].to_vec(),
            tag_keys: self.tag_keys?[..used].to_vec(),
        })
    }
}

struct SpendCoreVars {
    vk_hash: Fp,
    pk_p_x: Fp,
    pk_p_y: Fp,
    anchor_board_root: Fp,
    input_commitments: Vec<Fp>,
    input_active: [Boolean<Fr>; MAX_INPUTS],
}

fn synthesize_core(cs: ConstraintSystemRef<Fr>, w: &SpendCoreWitness) -> Result<SpendCoreVars, SynthesisError> {

    let output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
        .map(|i| Fp::new_input(cs.clone(), || opt(&w.output_commitments.map(|a| a[i]))))
        .collect::<Result<_, _>>()?;
    let anchor = w.anchor.as_ref();
    let _anchor_size = Fp::new_input(cs.clone(), || opt(&anchor.map(|a| Fr::from(a.size))))?;
    let anchor_board_root = Fp::new_input(cs.clone(), || opt(&anchor.map(|a| a.board_root)))?;
    let anchor_nullifier_root = Fp::new_input(cs.clone(), || opt(&anchor.map(|a| a.nullifier_root)))?;
    let nullifiers: Vec<Fp> = (0..MAX_INPUTS)
        .map(|i| Fp::new_input(cs.clone(), || opt(&w.nullifiers.map(|a| a[i]))))
        .collect::<Result<_, _>>()?;
    let tag_keys: Vec<Fp> = (0..MAX_INPUTS)
        .map(|i| Fp::new_input(cs.clone(), || opt(&w.tag_keys.map(|a| a[i]))))
        .collect::<Result<_, _>>()?;

    for _ in 0..MAX_INPUTS {
        Fp::new_input(cs.clone(), || Ok(Fr::from(0u64)))?.enforce_equal(&Fp::zero())?;
    }
    let origin_vk_hash = Fp::new_input(cs.clone(), || Ok(Fr::from(0u64)))?;
    let vk_hash = Fp::new_input(cs.clone(), || opt(&w.vk_hash))?;
    origin_vk_hash.enforce_equal(&Fp::zero())?;

    let pk_xy = w.pk_p.as_ref().map(owner_pk_to_field_pair);
    let pk_p_x = alloc_fp(cs.clone(), pk_xy.map(|(x, _)| x))?;
    let pk_p_y = alloc_fp(cs.clone(), pk_xy.map(|(_, y)| y))?;

    let sk_bit_values: Option<Vec<bool>> = w.sk_p.map(|sk| sk.into_bigint().to_bits_le());
    let sk_bit_len = OwnerScalar::MODULUS_BIT_SIZE as usize;
    let sk_bits: Vec<Boolean<Fr>> = (0..sk_bit_len)
        .map(|i| Boolean::new_witness(cs.clone(), || opt(&sk_bit_values.as_ref().map(|b| b[i]))))
        .collect::<Result<_, _>>()?;

    let mut modulus_minus_one = OwnerScalar::MODULUS.0.to_vec();
    modulus_minus_one[0] -= 1;
    Boolean::enforce_smaller_or_equal_than_le(&sk_bits, modulus_minus_one)?;

    let pk_p_computed = generator_var(cs.clone())?.scalar_mul_le(sk_bits.iter())?.to_affine()?;
    pk_p_computed.x.enforce_equal(&pk_p_x)?;
    pk_p_computed.y.enforce_equal(&pk_p_y)?;

    let sk_folded = fold_bits_le_var(cs.clone(), &sk_bits)?;

    let input_present: [bool; MAX_INPUTS] = std::array::from_fn(|i| w.input_coins[i].is_some());
    let input_active = alloc_active_flags(cs.clone(), &input_present)?;
    for i in 1..MAX_INPUTS {
        gate(input_active[i - 1].clone(), &input_active[i]).enforce_equal(&Boolean::TRUE)?;
    }
    let mut input_commitments = Vec::with_capacity(MAX_INPUTS);
    let mut total_in = Fp::zero();
    for i in 0..MAX_INPUTS {
        let coin = CoinVar::new_witness(cs.clone(), &w.input_coins[i])?;
        let owner_ok = &coin.owner_pk_x.is_eq(&pk_p_x)? & &coin.owner_pk_y.is_eq(&pk_p_y)?;
        gate(owner_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

        let commitment = coin.commitment(cs.clone())?;

        let own_nullifier = poseidon_hash_var(cs.clone(), &[commitment.clone(), sk_folded.clone()])?;
        let tag_key = poseidon_hash_var(
            cs.clone(),
            &[Fp::constant(Fr::from(TAG_KEY_DOMAIN)), commitment.clone(), sk_folded.clone()],
        )?;
        let published_nullifier = Fp::conditionally_select(&input_active[i], &own_nullifier, &Fp::zero())?;
        let published_tag_key = Fp::conditionally_select(&input_active[i], &tag_key, &Fp::zero())?;
        published_nullifier.enforce_equal(&nullifiers[i])?;
        published_tag_key.enforce_equal(&tag_keys[i])?;

        for earlier in &nullifiers[..i] {
            gate(!earlier.is_eq(&nullifiers[i])?, &input_active[i]).enforce_equal(&Boolean::TRUE)?;
        }

        let nonmembership_ok = verify_nonmembership_var(
            cs.clone(),
            &anchor_nullifier_root,
            &own_nullifier,
            w.own_nullifier_nonmembership[i].as_ref(),
        )?;
        gate(nonmembership_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

        total_in += coin.value_or_zero(&input_active[i])?;
        input_commitments.push(commitment);
    }

    let output_present: [bool; MAX_OUTPUTS] = std::array::from_fn(|i| w.output_coins[i].is_some());
    let output_active = alloc_active_flags(cs.clone(), &output_present)?;
    let mut total_out = Fp::zero();
    for j in 0..MAX_OUTPUTS {
        let coin = CoinVar::new_witness(cs.clone(), &w.output_coins[j])?;
        let expected = Fp::conditionally_select(&output_active[j], &coin.commitment(cs.clone())?, &Fp::zero())?;
        expected.enforce_equal(&output_commitments[j])?;
        total_out += coin.value_or_zero(&output_active[j])?;
    }

    total_in.enforce_equal(&total_out)?;

    Ok(SpendCoreVars { vk_hash, pk_p_x, pk_p_y, anchor_board_root, input_commitments, input_active })
}

#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct GenesisSpendCircuit {
    pub core: SpendCoreWitness,
}

impl ConstraintSynthesizer<Fr> for GenesisSpendCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let core = synthesize_core(cs, &self.core)?;

        let (genesis_x, genesis_y) = owner_pk_to_field_pair(&genesis_pk());
        core.pk_p_x.enforce_equal(&Fp::constant(genesis_x))?;
        core.pk_p_y.enforce_equal(&Fp::constant(genesis_y))?;
        Ok(())
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SpendStepCircuit {
    pub core: SpendCoreWitness,

    pub wrap_vk: VerifyingKey<MNT6_753>,

    pub genesis_vk_hash: Fr,

    pub fold_vk_hash: Fr,

    pub input_parent_proofs: [Option<Proof<MNT6_753>>; MAX_INPUTS],

    pub input_parent_statements: [Option<StepStatement>; MAX_INPUTS],

    pub input_parents: [Option<ParentWitness>; MAX_INPUTS],
}

impl SpendStepCircuit {

    pub fn dummy_wrap_proof() -> Proof<MNT6_753> {
        Proof {
            a: ark_mnt6_753::G1Projective::generator().into_affine(),
            b: ark_mnt6_753::G2Projective::generator().into_affine(),
            c: ark_mnt6_753::G1Projective::generator().into_affine(),
        }
    }
}

fn verify_wrapped(
    cs: ConstraintSystemRef<Fr>,
    pvk: &PreparedVerifyingKeyVar<MNT6_753, MNT6PairingVar>,
    statement: Option<&StepStatement>,
    proof: Option<&Proof<MNT6_753>>,
) -> Result<(Boolean<Fr>, ParentPublicVars), SynthesisError> {
    let cpv = chunks_per_value();
    let public_len = SPEND_PUBLIC_INPUT_COUNT * cpv;
    let chunks: Vec<Fr6> = statement
        .map(|statement| public_input_chunks(&statement.public_inputs()))
        .unwrap_or_else(|| vec![Fr6::from(0u64); public_len]);
    let mut per_chunk_bits: Vec<Vec<Boolean<Fr>>> = Vec::with_capacity(public_len);
    for chunk in &chunks {
        let value_bits: Vec<bool> = chunk.into_bigint().to_bits_le();
        let bits: Vec<Boolean<Fr>> = (0..CHUNK_BITS)
            .map(|j| Boolean::new_witness(cs.clone(), || Ok(value_bits[j])))
            .collect::<Result<_, _>>()?;
        per_chunk_bits.push(bits);
    }
    let input_var = BooleanInputVar::<Fr6, Fr>::new(per_chunk_bits.clone());
    let proof_native = proof.cloned().unwrap_or_else(SpendStepCircuit::dummy_wrap_proof);
    let proof_var = ProofVar::<MNT6_753, MNT6PairingVar>::new_witness(cs, || Ok(proof_native))?;
    let ok = VerifierGadget::<MNT6_753, MNT6PairingVar>::verify_with_processed_vk(pvk, &input_var, &proof_var)?;

    let values: Vec<Fp> = per_chunk_bits.chunks(cpv).map(combine_chunks_var).collect::<Result<_, _>>()?;
    Ok((ok, ParentPublicVars::from_values(&values)))
}

impl ConstraintSynthesizer<Fr> for SpendStepCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let core = synthesize_core(cs.clone(), &self.core)?;

        let wrap_vk_var = VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), &self.wrap_vk)?;
        let pvk = wrap_vk_var.prepare()?;
        let genesis_vk_hash = Fp::constant(self.genesis_vk_hash);

        for i in 0..MAX_INPUTS {
            let is_active = &core.input_active[i];

            let (recursive_ok, pv) = verify_wrapped(
                cs.clone(),
                &pvk,
                self.input_parent_statements[i].as_ref(),
                self.input_parent_proofs[i].as_ref(),
            )?;
            gate(recursive_ok, is_active).enforce_equal(&Boolean::TRUE)?;

            let spend_key =
                |hash: &Fp| -> Result<Boolean<Fr>, SynthesisError> { Ok(&hash.is_eq(&genesis_vk_hash)? | &hash.is_eq(&core.vk_hash)?) };
            let from_fold = &pv.vk_hash.is_eq(&Fp::constant(self.fold_vk_hash))? & &spend_key(&pv.origin_vk_hash)?;
            gate(&spend_key(&pv.vk_hash)? | &from_fold, is_active).enforce_equal(&Boolean::TRUE)?;

            let parent_ok =
                parent_checks(cs.clone(), self.input_parents[i].as_ref(), &pv, &core.input_commitments[i], &core.anchor_board_root)?;
            gate(parent_ok, is_active).enforce_equal(&Boolean::TRUE)?;
        }

        Ok(())
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct FoldCircuit {

    pub wrap_vk: VerifyingKey<MNT6_753>,

    pub previous: Option<StepStatement>,

    pub previous_proof: Option<Proof<MNT6_753>>,

    pub input: usize,

    pub occurrences: Vec<Occurrence>,

    pub vk_hash: Option<Fr>,
}

impl FoldCircuit {

    pub fn statement(&self) -> Option<StepStatement> {
        Some(self.previous.as_ref()?.folded(self.input, &self.occurrences, self.vk_hash?))
    }
}

impl ConstraintSynthesizer<Fr> for FoldCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {

        let mine = self.statement().map(|statement| statement.public_inputs());
        let inputs: Vec<Fp> = (0..SPEND_PUBLIC_INPUT_COUNT)
            .map(|i| Fp::new_input(cs.clone(), || opt(&mine.map(|m| m[i]))))
            .collect::<Result<_, _>>()?;
        let my_vk_hash = &inputs[PARENT_VK_HASH];

        let wrap_vk_var = VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), &self.wrap_vk)?;
        let pvk = wrap_vk_var.prepare()?;
        let (recursive_ok, pv) = verify_wrapped(cs.clone(), &pvk, self.previous.as_ref(), self.previous_proof.as_ref())?;
        recursive_ok.enforce_equal(&Boolean::TRUE)?;

        for (mine, theirs) in inputs.iter().zip(pv.statement()) {
            mine.enforce_equal(&theirs)?;
        }

        let continues = pv.vk_hash.is_eq(my_vk_hash)?;
        let origin = Fp::conditionally_select(&continues, &pv.origin_vk_hash, &pv.vk_hash)?;
        origin.enforce_equal(&inputs[PARENT_ORIGIN_VK_HASH])?;

        let selector: Vec<Boolean<Fr>> = (0..MAX_INPUTS)
            .map(|i| Boolean::new_witness(cs.clone(), || Ok(i == self.input)))
            .collect::<Result<_, _>>()?;
        let chosen = selector.iter().fold(Ok(Fp::zero()), |sum: Result<Fp, SynthesisError>, bit| Ok(sum? + Fp::from(bit.clone())))?;
        chosen.enforce_equal(&Fp::one())?;
        let target = FoldTarget::select(&pv, &selector)?;

        let (folds_ok, head) =
            fold_batch(cs, &self.occurrences, FOLD_BATCH, &pv.output_commitments, &target)?;
        folds_ok.enforce_equal(&Boolean::TRUE)?;
        for (i, bit) in selector.iter().enumerate() {
            let expected = Fp::conditionally_select(bit, &head, &pv.window_heads[i])?;
            expected.enforce_equal(&inputs[PARENT_WINDOW_HEADS_START + i])?;
        }
        Ok(())
    }
}

pub fn setup_fold<R: RngCore + CryptoRng>(
    wrap_vk: VerifyingKey<MNT6_753>,
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    let circuit = FoldCircuit {
        wrap_vk,
        previous: None,

        previous_proof: Some(SpendStepCircuit::dummy_wrap_proof()),
        input: 0,
        occurrences: Vec::new(),
        vk_hash: None,
    };
    Snark::<MNT4_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove_fold<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: FoldCircuit,
    rng: &mut R,
) -> Result<Proof<MNT4_753>, SynthesisError> {
    Snark::<MNT4_753>::prove(pk, circuit, rng)
}

pub fn setup_non_genesis<R: RngCore + CryptoRng>(
    wrap_vk: VerifyingKey<MNT6_753>,
    genesis_vk_hash: Fr,
    fold_vk_hash: Fr,
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    let circuit = SpendStepCircuit {
        core: SpendCoreWitness::default(),
        wrap_vk,
        genesis_vk_hash,
        fold_vk_hash,

        input_parent_proofs: std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof())),
        input_parent_statements: std::array::from_fn(|_| None),
        input_parents: std::array::from_fn(|_| None),
    };
    Snark::<MNT4_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove_non_genesis<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: SpendStepCircuit,
    rng: &mut R,
) -> Result<Proof<MNT4_753>, SynthesisError> {
    Snark::<MNT4_753>::prove(pk, circuit, rng)
}

pub fn verify_non_genesis(
    vk: &VerifyingKey<MNT4_753>,
    public_inputs: &[Fr],
    proof: &Proof<MNT4_753>,
) -> Result<bool, SynthesisError> {
    Snark::<MNT4_753>::verify(vk, public_inputs, proof)
}

pub fn setup<R: RngCore + CryptoRng>(
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    Snark::<MNT4_753>::circuit_specific_setup(GenesisSpendCircuit::default(), rng)
}

pub fn prove<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: GenesisSpendCircuit,
    rng: &mut R,
) -> Result<Proof<MNT4_753>, SynthesisError> {
    Snark::<MNT4_753>::prove(pk, circuit, rng)
}

pub fn verify(
    vk: &VerifyingKey<MNT4_753>,
    public_inputs: &[Fr],
    proof: &Proof<MNT4_753>,
) -> Result<bool, SynthesisError> {
    Snark::<MNT4_753>::verify(vk, public_inputs, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
    use cloakkchain_lib::{
        check_spend, coin_tag, encrypt_tx, genesis_sk, BoardEntry, History, Transaction,
    };

    fn owner(seed: u64) -> (OwnerScalar, OwnerPk) {
        let sk = OwnerScalar::from(seed + 100);
        (sk, cloakkchain_lib::derive_owner_pk(&sk))
    }

    fn coin(seed: u64, value: u64, owner_pk: OwnerPk) -> Coin {
        let mut bytes = [0u8; 32];
        bytes[..8].copy_from_slice(&seed.to_le_bytes());
        Coin { value, seed: bytes, owner_pk }
    }

    #[derive(Clone)]
    struct Posted {
        entry: BoardEntry,
        pv: SpendPublicValues,
        core: SpendCoreWitness,
    }

    fn post(
        history: &History,
        sk: OwnerScalar,
        input: &Coin,
        outputs: &[Coin],
        anchor_size: usize,
        parent: Option<&ParentWitness>,
        id: u8,
    ) -> Posted {
        let parents: Vec<ParentWitness> = parent.into_iter().cloned().collect();
        post_inputs(history, sk, std::slice::from_ref(input), outputs, anchor_size, &parents, id)
    }

    fn post_inputs(
        history: &History,
        sk: OwnerScalar,
        inputs: &[Coin],
        outputs: &[Coin],
        anchor_size: usize,
        parents: &[ParentWitness],
        id: u8,
    ) -> Posted {
        let anchor = history.anchor_at(anchor_size).unwrap();
        let cms: Vec<Fr> = inputs.iter().map(Coin::commitment).collect();
        let tree = history.nullifier_tree_at(anchor_size);
        let nonmemberships: Vec<NonMembershipWitness> =
            cms.iter().map(|cm| tree.prove_non_membership(derive_nullifier(*cm, &sk))).collect();
        let real: Vec<Fr> = outputs.iter().map(Coin::commitment).collect();
        let padded = pad_outputs(&real);
        let pv = check_spend(&sk, inputs, outputs, &padded, &anchor, &nonmemberships, parents).unwrap();
        let tx = Transaction {
            note_encs: vec![],
            tag_keys: cms.iter().map(|cm| derive_tag_key(&sk, *cm)).collect(),
            anchor_size: anchor.size,
            spend_proof: vec![],
        };
        let entry = encrypt_tx(&tx, &padded, &cms, &sk, &[[9u8; 32]], [id; 32]);
        let core = SpendCoreWitness::new(sk, inputs, outputs, anchor, &nonmemberships, Fr::from(0u64));
        assert_eq!(core.public_values().as_ref(), Some(&pv), "circuit and oracle must agree on the statement");
        Posted { entry, pv, core }
    }

    fn junk_copy(nullifier: Fr, seed: u64) -> BoardEntry {
        BoardEntry {
            ciphertext: vec![seed as u8; 40],
            ek_pk: [seed as u8; 32],
            key_encs: vec![[seed as u8; 32]],
            nullifiers: vec![nullifier],
            output_commitments: vec![Fr::from(seed)],
            tags: vec![Fr::from(seed)],
        }
    }

    struct World {
        history: History,
        genesis: Posted,
        alice_coin: Coin,
        alice_sk: OwnerScalar,
        bob_coin: Coin,
        bob_sk: OwnerScalar,
    }

    fn world() -> World {
        let (alice_sk, alice_pk) = owner(1);
        let (bob_sk, bob_pk) = owner(2);
        let alice_coin = coin(2, 100, alice_pk);
        let mut history = History::new();
        let genesis = post(&history, genesis_sk(), &coin(1, 100, genesis_pk()), &[alice_coin.clone()], 0, None, 0);
        history.append(&genesis.entry);
        World { history, genesis, alice_coin, alice_sk, bob_coin: coin(3, 100, bob_pk), bob_sk }
    }

    impl World {
        fn alice_spends(&self, output: &Coin, id: u8) -> Posted {
            let parent = self.history.parent_witness(0, &self.genesis.pv, 1);
            post(&self.history, self.alice_sk, &self.alice_coin, std::slice::from_ref(output), 1, Some(&parent), id)
        }

        fn alice_nullifier(&self) -> Fr {
            derive_nullifier(self.alice_coin.commitment(), &self.alice_sk)
        }

        fn witness_for(&self, slot: usize, carrier: &Posted) -> (ParentWitness, Fr) {
            let size = self.history.len();
            let witness = self.history.parent_witness(slot, &carrier.pv, size);
            (witness, self.history.anchor_at(size).unwrap().board_root)
        }
    }

    fn certified_heads(witness: &ParentWitness) -> [Fr; MAX_INPUTS] {
        std::array::from_fn(|i| match witness.windows.get(i) {
            Some(window) if !window.occurrences.is_empty() => window.leaf.occ,
            _ => Fr::from(0u64),
        })
    }

    fn parent_public_vars(cs: ConstraintSystemRef<Fr>, statement: &StepStatement) -> ParentPublicVars {
        let vars: Vec<Fp> =
            statement.public_inputs().iter().map(|v| Fp::new_witness(cs.clone(), || Ok(*v)).unwrap()).collect();
        ParentPublicVars::from_values(&vars)
    }

    fn parent_checks_result(witness: &ParentWitness, commitment: Fr, anchor_board_root: Fr) -> bool {
        parent_checks_with_heads(witness, certified_heads(witness), commitment, anchor_board_root)
    }

    fn parent_checks_with_head(witness: &ParentWitness, head: Fr, commitment: Fr, anchor_board_root: Fr) -> bool {
        let mut heads = certified_heads(witness);
        heads[0] = head;
        parent_checks_with_heads(witness, heads, commitment, anchor_board_root)
    }

    fn parent_checks_with_heads(
        witness: &ParentWitness,
        window_heads: [Fr; MAX_INPUTS],
        commitment: Fr,
        anchor_board_root: Fr,
    ) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let statement = StepStatement { window_heads, ..StepStatement::of_spend(witness.public_values.clone(), Fr::from(0u64)) };
        let pv = parent_public_vars(cs.clone(), &statement);
        let commitment = Fp::new_witness(cs.clone(), || Ok(commitment)).unwrap();
        let root = Fp::new_witness(cs.clone(), || Ok(anchor_board_root)).unwrap();
        let ok = parent_checks(cs.clone(), Some(witness), &pv, &commitment, &root).unwrap();
        assert!(cs.is_satisfied().unwrap(), "must evaluate to false, never become unsatisfiable");
        ok.value().unwrap()
    }

    fn fold_result(statement: &StepStatement, occurrences: &[Occurrence], slots: usize) -> (bool, Fr) {
        fold_input_result(statement, 0, occurrences, slots)
    }

    fn fold_input_result(
        statement: &StepStatement,
        input: usize,
        occurrences: &[Occurrence],
        slots: usize,
    ) -> (bool, Fr) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let pv = parent_public_vars(cs.clone(), statement);
        let target = FoldTarget::input(&pv, input);
        let (ok, head) = fold_batch(cs.clone(), occurrences, slots, &pv.output_commitments, &target).unwrap();
        assert!(cs.is_satisfied().unwrap(), "must evaluate to false, never become unsatisfiable");
        let head = head.value().unwrap();
        let native = statement.folded(input, occurrences, Fr::from(0u64)).window_heads[input];
        assert_eq!(head, native, "gadget and native links must agree");
        (ok.value().unwrap(), head)
    }

    fn fold_input_in_batches(witness: &ParentWitness, input: usize, batch: usize) -> (bool, Fr) {
        let mut statement = StepStatement::of_spend(witness.public_values.clone(), Fr::from(0u64));
        let mut all_ok = true;
        for chunk in witness.windows[input].occurrences.chunks(batch) {
            let (ok, head) = fold_input_result(&statement, input, chunk, batch);
            all_ok &= ok;
            statement.window_heads[input] = head;
        }
        (all_ok, statement.window_heads[input])
    }

    fn fold_window_in_batches(witness: &ParentWitness, batch: usize) -> (bool, Fr) {
        fold_input_in_batches(witness, 0, batch)
    }

    fn fold_window(witness: &ParentWitness) -> (bool, Fr) {
        fold_window_in_batches(witness, 2)
    }

    #[test]
    fn fp_is_lt_is_numeric() {
        let values = [
            Fr::from(0u64),
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(u64::MAX),
            -Fr::from(2u64),
            -Fr::from(1u64),
            cloakkchain_lib::poseidon_hash(&[Fr::from(1u64)]),
            cloakkchain_lib::poseidon_hash(&[Fr::from(2u64)]),
        ];
        let cs = ConstraintSystem::<Fr>::new_ref();
        for a in values {
            for b in values {
                let a_var = Fp::new_witness(cs.clone(), || Ok(a)).unwrap();
                let b_var = Fp::new_witness(cs.clone(), || Ok(b)).unwrap();
                assert_eq!(fp_is_lt(&a_var, &b_var).unwrap().value().unwrap(), a < b, "{a} < {b}");
            }
        }
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn nonmembership_rejects_a_member_through_any_leaf() {
        let member = cloakkchain_lib::poseidon_hash(&[Fr::from(1u64)]);
        let mut history = History::new();
        history.append(&junk_copy(member, 1));
        for seed in 2..6u64 {
            history.append(&junk_copy(cloakkchain_lib::poseidon_hash(&[Fr::from(seed)]), seed));
        }
        let tree = history.nullifier_tree_at(history.len());
        let root = tree.root();

        let others: Vec<Fr> = (2..6u64).map(|seed| cloakkchain_lib::poseidon_hash(&[Fr::from(seed)])).collect();
        let mut leaves = vec![tree.prove_non_membership(member)];
        leaves.extend(others.iter().map(|o| tree.prove_non_membership(*o)));
        leaves.push(tree.prove_non_membership(-Fr::from(2u64)));
        for w in &leaves {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let root_var = Fp::new_witness(cs.clone(), || Ok(root)).unwrap();
            let target = Fp::new_witness(cs.clone(), || Ok(member)).unwrap();
            let ok = verify_nonmembership_var(cs.clone(), &root_var, &target, Some(w)).unwrap();
            assert!(cs.is_satisfied().unwrap());
            assert!(!ok.value().unwrap(), "a member must not pass via leaf {}", w.low_leaf.value);
        }

        let absent = Fr::from(12345u64);
        let cs = ConstraintSystem::<Fr>::new_ref();
        let root_var = Fp::new_witness(cs.clone(), || Ok(root)).unwrap();
        let target = Fp::new_witness(cs.clone(), || Ok(absent)).unwrap();
        let w = tree.prove_non_membership(absent);
        assert!(verify_nonmembership_var(cs, &root_var, &target, Some(&w)).unwrap().value().unwrap());
    }

    #[test]
    fn posted_outputs_need_no_padding() {
        let a = Fr::from(7u64);
        assert_eq!(cloakkchain_lib::poseidon_hash(&[a]), cloakkchain_lib::poseidon_hash(&pad_outputs(&[a])));

        let mut w = world();
        let mut alice = w.alice_spends(&w.bob_coin, 1);
        let tx = Transaction {
            note_encs: vec![],
            tag_keys: alice.pv.tag_keys.clone(),
            anchor_size: alice.pv.anchor.size,
            spend_proof: vec![],
        };
        alice.entry = encrypt_tx(
            &tx,
            &[w.bob_coin.commitment()],
            &[w.alice_coin.commitment()],
            &w.alice_sk,
            &[[9u8; 32]],
            [1u8; 32],
        );
        assert_eq!(alice.entry.output_commitments.len(), 1);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn tag_gadget_matches_native() {
        let (sk, pk) = owner(1);
        let cm = coin(1, 5, pk).commitment();
        let (tk, sn, oh) = (derive_tag_key(&sk, cm), Fr::from(7u64), Fr::from(8u64));
        let cs = ConstraintSystem::<Fr>::new_ref();
        let var = |x: Fr| Fp::new_witness(cs.clone(), || Ok(x)).unwrap();
        let tag = coin_tag_var(cs.clone(), &var(tk), &var(sn), &var(oh)).unwrap();
        assert_eq!(tag.value().unwrap(), coin_tag(tk, sn, oh));
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn hash_gadgets_match_native() {
        let w = world();
        let opening = w.history.opening(0).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let var = LeafOpeningVar::new_witness(cs.clone(), Some(opening)).unwrap();
        assert_eq!(var.hash(cs.clone()).unwrap().value().unwrap(), opening.hash());
    }

    #[test]
    fn clean_parent_passes_with_an_empty_window() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert!(witness.windows[0].occurrences.is_empty());
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn any_number_of_junk_copies_folds_and_passes() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        for seed in 0..5 {
            w.history.append(&junk_copy(w.alice_nullifier(), seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert_eq!(witness.windows[0].occurrences.len(), 5);
        let (folds_ok, head) = fold_window(&witness);
        assert!(folds_ok);
        assert_eq!(head, witness.windows[0].leaf.occ);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn honest_re_prove_in_the_window_folds() {
        let mut w = world();
        let first = w.alice_spends(&w.bob_coin, 1);
        let second = w.alice_spends(&w.bob_coin, 2);
        w.history.append(&first.entry);
        let slot = w.history.append(&second.entry);
        let (witness, root) = w.witness_for(slot, &second);
        assert!(fold_window(&witness).0);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn validly_signed_spend_in_the_window_cannot_be_folded() {
        let mut w = world();
        let (_, carol_pk) = owner(3);
        let carol_coin = coin(4, 100, carol_pk);
        let to_bob = w.alice_spends(&w.bob_coin, 1);
        let to_carol = w.alice_spends(&carol_coin, 2);
        let bob_slot = w.history.append(&to_bob.entry);
        let carol_slot = w.history.append(&to_carol.entry);

        let (witness, root) = w.witness_for(bob_slot, &to_bob);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root), "the first spend stands");
        let (witness, _) = w.witness_for(carol_slot, &to_carol);
        assert!(!fold_window(&witness).0, "the second's window holds a double-spend");
    }

    #[test]
    fn fold_needs_the_parents_own_key() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        let slot = w.history.append(&alice.entry);
        let (witness, _) = w.witness_for(slot, &alice);
        let statement = StepStatement::of_spend(witness.public_values.clone(), Fr::from(0u64));
        let occurrences = &witness.windows[0].occurrences;
        assert!(fold_result(&statement, occurrences, 1).0);

        let double = Occurrence {
            outputs_hash: Fr::from(9u64),
            tag: coin_tag(witness.public_values.tag_keys[0], w.alice_nullifier(), Fr::from(9u64)),
        };
        assert!(!fold_result(&statement, &[double.clone()], 1).0);

        let mut other_key = statement.clone();
        other_key.public_values.tag_keys[0] = Fr::from(7u64);
        assert!(fold_result(&other_key, &[double], 1).0);
    }

    #[test]
    fn fold_is_total_on_junk() {
        let w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let statement = StepStatement::of_spend(alice.pv.clone(), Fr::from(0u64));
        for tag in [Fr::from(0u64), -Fr::from(1u64), Fr::from(1u64)] {
            let occurrence = LeafOpening::new(
                0,
                &BoardEntry { tags: vec![tag], ..junk_copy(w.alice_nullifier(), 1) },
                Fr::from(0u64),
                Fr::from(0u64),
            )
            .occurrence(0);
            assert!(fold_result(&statement, &[occurrence], 2).0);
        }
    }

    #[test]
    fn batch_size_does_not_change_the_head() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        for seed in 0..5 {
            w.history.append(&junk_copy(w.alice_nullifier(), seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let (witness, _) = w.witness_for(slot, &alice);
        for batch in [1, 2, 3, 5, 6] {
            assert_eq!(fold_window_in_batches(&witness, batch), (true, witness.windows[0].leaf.occ), "batch {batch}");
        }
    }

    #[test]
    fn window_head_must_cover_every_occurrence() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        w.history.append(&junk_copy(w.alice_nullifier(), 2));
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        let commitment = w.bob_coin.commitment();
        assert!(parent_checks_result(&witness, commitment, root));

        let mut hiding = witness.clone();
        hiding.windows[0] = w.history.nullifier_tree_at(1).prove_window(w.alice_nullifier());
        assert!(!parent_checks_with_head(&hiding, Fr::from(0u64), commitment, root));

        assert!(!parent_checks_with_head(&witness, Fr::from(0u64), commitment, root));

        let partial = witness.windows[0].occurrences[0].link(Fr::from(0u64));
        assert!(!parent_checks_with_head(&witness, partial, commitment, root));
    }

    #[test]
    fn invalid_parent_tag_fails() {
        let mut w = world();
        let mut alice = w.alice_spends(&w.bob_coin, 1);
        alice.entry.tags[0] = Fr::from(1u64);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert!(!parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn fake_parent_tag_key_fails() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        let (mut witness, root) = w.witness_for(slot, &alice);
        witness.public_values.tag_keys[0] = Fr::from(7u64);
        assert!(!parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn parent_anchor_must_be_real_and_precede_the_parent() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        w.history.append(&junk_copy(Fr::from(5u64), 1));
        let (parent, root) = w.witness_for(slot, &alice);
        let commitment = w.bob_coin.commitment();
        assert!(parent_checks_result(&parent, commitment, root));

        let mut fake_root = parent.clone();
        fake_root.public_values.anchor.nullifier_root += Fr::from(1u64);
        assert!(!parent_checks_result(&fake_root, commitment, root));

        let mut wrong_leaf = parent.clone();
        wrong_leaf.anchor_leaf = w.history.opening(0).unwrap().clone();
        wrong_leaf.anchor_leaf_path = w.history.board_path(0, w.history.len());
        assert!(!parent_checks_result(&wrong_leaf, commitment, root));

        let mut later = parent;
        later.public_values.anchor = w.history.anchor_at(2).unwrap();
        later.anchor_leaf = w.history.opening(2).unwrap().clone();
        later.anchor_leaf_path = w.history.board_path(2, w.history.len());
        assert!(!parent_checks_result(&later, commitment, root));
    }

    #[test]
    fn parent_must_be_under_the_anchor_and_create_the_coin() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        let commitment = w.bob_coin.commitment();

        let earlier_root = w.history.anchor_at(1).unwrap().board_root;
        assert!(!parent_checks_result(&witness, commitment, earlier_root));
        assert!(!parent_checks_result(&witness, commitment + Fr::from(1u64), root));

        let mut lying = witness;
        lying.public_values.nullifiers[0] += Fr::from(1u64);
        assert!(!parent_checks_result(&lying, commitment, root));
    }

    #[cfg(feature = "two-inputs")]
    fn two_coins(w: &mut World) -> (Posted, Coin, Posted) {
        let second_coin = coin(5, 50, owner(1).1);
        let mint = post(&w.history, genesis_sk(), &coin(6, 50, genesis_pk()), &[second_coin.clone()], 1, None, 7);
        w.history.append(&mint.entry);
        let parents = [
            w.history.parent_witness(0, &w.genesis.pv, 2),
            w.history.parent_witness(1, &mint.pv, 2),
        ];
        let both = [w.alice_coin.clone(), second_coin.clone()];
        let alice = post_inputs(&w.history, w.alice_sk, &both, &[coin(3, 150, owner(2).1)], 2, &parents, 1);
        (alice, second_coin, mint)
    }

    #[cfg(feature = "two-inputs")]
    fn two_input_genesis_circuit() -> GenesisSpendCircuit {
        let inputs = [coin(1, 100, genesis_pk()), coin(7, 50, genesis_pk())];
        let posted = post_inputs(&History::new(), genesis_sk(), &inputs, &[coin(2, 150, owner(1).1)], 0, &[], 0);
        GenesisSpendCircuit { core: posted.core }
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn two_input_spend_satisfies_constraints() {
        assert!(satisfied(two_input_genesis_circuit()));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn the_same_coin_twice_fails() {
        let mut c = two_input_genesis_circuit();
        let core = &mut c.core;
        core.input_coins[1] = core.input_coins[0].clone();
        core.own_nullifier_nonmembership[1] = core.own_nullifier_nonmembership[0].clone();
        let (sns, tks) = (core.nullifiers.unwrap(), core.tag_keys.unwrap());
        core.nullifiers = Some([sns[0], sns[0]]);
        core.tag_keys = Some([tks[0], tks[0]]);
        let value = core.input_coins[0].as_ref().unwrap().value;
        let mut doubled = core.output_coins[0].clone().unwrap();
        doubled.value = 2 * value;
        core.output_commitments = Some(pad_outputs(&[doubled.commitment()]));
        core.output_coins[0] = Some(doubled);
        assert!(!satisfied(c));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn an_unused_input_slot_must_publish_zeros() {
        assert!(satisfied(genesis_circuit()));
        let mut sn = genesis_circuit();
        sn.core.nullifiers.as_mut().unwrap()[1] = Fr::from(5u64);
        assert!(!satisfied(sn));
        let mut tk = genesis_circuit();
        tk.core.tag_keys.as_mut().unwrap()[1] = Fr::from(7u64);
        assert!(!satisfied(tk));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn every_input_of_a_two_input_parent_is_checked() {
        let mut w = world();
        let (alice, _, _) = two_coins(&mut w);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        let commitment = coin(3, 150, owner(2).1).commitment();
        assert!(parent_checks_result(&witness, commitment, root));

        let mut wrong_key = witness.clone();
        wrong_key.public_values.tag_keys[1] = Fr::from(7u64);
        assert!(!parent_checks_result(&wrong_key, commitment, root));

        let mut one_input = witness.clone();
        one_input.public_values.nullifiers.truncate(1);
        one_input.public_values.tag_keys.truncate(1);
        assert!(!parent_checks_result(&one_input, commitment, root));

        let mut broken = alice.clone();
        broken.entry.tags[1] = Fr::from(1u64);
        let broken_slot = w.history.append(&broken.entry);
        let (witness, root) = w.witness_for(broken_slot, &broken);
        assert!(!parent_checks_result(&witness, commitment, root));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn copies_of_the_second_input_fold_into_its_own_head() {
        let mut w = world();
        let (alice, second_coin, _) = two_coins(&mut w);
        let second_sn = derive_nullifier(second_coin.commitment(), &w.alice_sk);
        for seed in 0..3 {
            w.history.append(&junk_copy(second_sn, seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert!(witness.windows[0].occurrences.is_empty());
        assert_eq!(witness.windows[1].occurrences.len(), 3);

        assert_eq!(fold_input_in_batches(&witness, 1, 2), (true, witness.windows[1].leaf.occ));
        let commitment = coin(3, 150, owner(2).1).commitment();
        assert!(parent_checks_result(&witness, commitment, root));

        assert!(!parent_checks_with_heads(&witness, [Fr::from(0u64); MAX_INPUTS], commitment, root));

        assert!(!parent_checks_with_heads(&witness, [witness.windows[1].leaf.occ, Fr::from(0u64)], commitment, root));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn double_spend_of_the_second_input_cannot_be_folded() {
        let mut w = world();
        let (alice, second_coin, mint) = two_coins(&mut w);
        let second_mint_witness = w.history.parent_witness(1, &mint.pv, 2);
        let alone = post(&w.history, w.alice_sk, &second_coin, &[coin(8, 50, owner(3).1)], 2, Some(&second_mint_witness), 2);
        w.history.append(&alone.entry);
        let slot = w.history.append(&alice.entry);
        let (witness, _) = w.witness_for(slot, &alice);
        assert!(witness.windows[0].occurrences.is_empty());
        assert!(!fold_input_in_batches(&witness, 1, 2).0, "the second input's window holds a double-spend");
    }

    fn genesis_circuit() -> GenesisSpendCircuit {
        let (_, alice_pk) = owner(1);
        let history = History::new();
        let posted = post(&history, genesis_sk(), &coin(1, 100, genesis_pk()), &[coin(2, 100, alice_pk)], 0, None, 0);
        GenesisSpendCircuit { core: posted.core }
    }

    fn satisfied(circuit: GenesisSpendCircuit) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn valid_genesis_witness_satisfies_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        genesis_circuit().generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "valid genesis witness should satisfy every constraint");
        println!("genesis constraint count: {}", cs.num_constraints());
    }

    #[test]
    #[cfg(not(feature = "single-output"))]
    fn two_real_outputs_with_conservation_satisfies_constraints() {
        let (_, bob_pk) = owner(2);
        let outputs = [coin(4, 40, bob_pk), coin(6, 60, genesis_pk())];
        let posted = post(&History::new(), genesis_sk(), &coin(1, 100, genesis_pk()), &outputs, 0, None, 0);
        assert!(satisfied(GenesisSpendCircuit { core: posted.core }));
    }

    #[test]
    fn wrong_secret_key_fails() {
        let mut c = genesis_circuit();
        c.core.sk_p = Some(OwnerScalar::from(2u64));
        assert!(!satisfied(c));
    }

    #[test]
    fn non_genesis_key_cannot_mint() {
        let (alice_sk, alice_pk) = owner(1);
        let input = coin(1, 100, alice_pk);
        let output = coin(2, 100, alice_pk);
        let history = History::new();
        let anchor = history.anchor_at(0).unwrap();
        let nonmembership = history
            .nullifier_tree_at(0)
            .prove_non_membership(derive_nullifier(input.commitment(), &alice_sk));
        let core = SpendCoreWitness::new(alice_sk, &[input], &[output], anchor, &[nonmembership], Fr::from(0u64));
        assert!(!satisfied(GenesisSpendCircuit { core }));
    }

    #[test]
    fn serial_number_and_tag_key_must_be_correctly_derived() {
        let mut wrong_sn = genesis_circuit();
        wrong_sn.core.nullifiers = Some(pad_inputs(&[Fr::from(1u64)]));
        assert!(!satisfied(wrong_sn));

        let mut wrong_tk = genesis_circuit();
        wrong_tk.core.tag_keys = Some(pad_inputs(&[Fr::from(7u64)]));
        assert!(!satisfied(wrong_tk));
    }

    #[test]
    fn nullifier_already_at_the_anchor_fails() {

        let mut c = genesis_circuit();
        let sn = c.core.nullifiers.unwrap()[0];
        let mut history = History::new();
        history.append(&junk_copy(sn, 1));
        c.core.anchor = history.anchor_at(1);
        c.core.own_nullifier_nonmembership[0] = Some(history.nullifier_tree_at(1).prove_non_membership(sn));
        assert!(!satisfied(c));
    }

    #[test]
    fn value_must_be_conserved() {
        let mut c = genesis_circuit();
        let mut bigger = c.core.output_coins[0].clone().unwrap();
        bigger.value += 1;
        c.core.output_commitments = Some(pad_outputs(&[bigger.commitment()]));
        c.core.output_coins[0] = Some(bigger);
        assert!(!satisfied(c));
    }

    #[test]
    #[cfg(not(feature = "single-output"))]
    fn phantom_commitment_in_an_inactive_output_slot_fails() {
        let mut c = genesis_circuit();
        assert!(c.core.output_coins[1].is_none());
        let real = c.core.output_commitments.unwrap()[0];
        let phantom = coin(9, 1000, owner(9).1).commitment();
        c.core.output_commitments = Some([real, phantom]);
        assert!(!satisfied(c));
    }

    #[test]
    fn marking_a_real_valued_slot_inactive_cannot_mint_value() {

        let phantom = CoinVar {
            value: UInt64::constant(50),
            rand: Fp::constant(Fr::from(9u64)),
            owner_pk_x: Fp::constant(Fr::from(0u64)),
            owner_pk_y: Fp::constant(Fr::from(0u64)),
        };
        let cs = ConstraintSystem::<Fr>::new_ref();
        let contribution = phantom.value_or_zero(&Boolean::constant(false)).unwrap();
        contribution.enforce_equal(&Fp::constant(Fr::from(0u64))).unwrap();
        assert!(cs.is_satisfied().unwrap(), "inactive slot's value must be forced to zero");
    }

    #[test]
    fn constraint_shape_does_not_depend_on_the_witness() {
        fn count<C: ConstraintSynthesizer<Fr>>(circuit: C, setup: bool) -> usize {
            let cs = if setup { setup_mode_cs() } else { ConstraintSystem::<Fr>::new_ref() };
            circuit.generate_constraints(cs.clone()).unwrap();
            cs.num_constraints()
        }

        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        for seed in 0..3 {
            w.history.append(&junk_copy(w.alice_nullifier(), seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let (witness, _) = w.witness_for(slot, &alice);
        let previous = StepStatement::of_spend(alice.pv.clone(), Fr::from(0u64));

        let spend = SpendStepCircuit {
            core: alice.core.clone(),
            input_parent_statements: std::array::from_fn(|i| (i == 0).then(|| previous.clone())),
            input_parents: std::array::from_fn(|i| (i == 0).then(|| witness.clone())),
            ..step_circuit_for_counting()
        };
        assert_eq!(count(spend, false), count(step_circuit_for_counting(), true), "spend");

        let expected = count(fold_circuit_for_counting(), true);
        for (occurrences, input) in [0, 3].into_iter().flat_map(|n| (0..MAX_INPUTS).map(move |i| (n, i))) {
            let fold = FoldCircuit {
                previous: Some(previous.clone()),
                input,
                occurrences: witness.windows[0].occurrences[..occurrences].to_vec(),
                vk_hash: Some(Fr::from(1u64)),
                ..fold_circuit_for_counting()
            };
            assert_eq!(count(fold, false), expected, "fold of {occurrences} for input {input}");
        }

        assert_eq!(count(genesis_circuit(), false), count(GenesisSpendCircuit::default(), true), "genesis");
    }

    fn shaped_wrap_vk() -> VerifyingKey<MNT6_753> {
        cloakkchain_circuit_wrap::snark::shaped_vk::<MNT6_753>(SPEND_PUBLIC_INPUT_COUNT * chunks_per_value())
    }

    fn step_circuit_for_counting() -> SpendStepCircuit {
        SpendStepCircuit {
            core: SpendCoreWitness::default(),
            wrap_vk: shaped_wrap_vk(),
            genesis_vk_hash: Fr::from(0u64),
            fold_vk_hash: Fr::from(0u64),
            input_parent_proofs: std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof())),
            input_parent_statements: std::array::from_fn(|_| None),
            input_parents: std::array::from_fn(|_| None),
        }
    }

    fn fold_circuit_for_counting() -> FoldCircuit {
        FoldCircuit {
            wrap_vk: shaped_wrap_vk(),
            previous: None,
            previous_proof: Some(SpendStepCircuit::dummy_wrap_proof()),
            input: 0,
            occurrences: Vec::new(),
            vk_hash: None,
        }
    }

    fn setup_mode_cs() -> ConstraintSystemRef<Fr> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        cs
    }

    #[test]
    fn report_constraint_costs() {
        let cs = setup_mode_cs();
        let msg = Fp::new_witness(cs.clone(), || Ok(Fr::from(0u64))).unwrap();
        let before = cs.num_constraints();
        let _ = coin_tag_var(cs.clone(), &msg, &msg, &msg).unwrap();
        let tag = cs.num_constraints() - before;

        let zero_pv = |cs: &ConstraintSystemRef<Fr>| {
            let zeros: Vec<Fp> = (0..SPEND_PUBLIC_INPUT_COUNT)
                .map(|_| Fp::new_witness(cs.clone(), || Ok(Fr::from(0u64))).unwrap())
                .collect();
            ParentPublicVars::from_values(&zeros)
        };
        let fold_pv = zero_pv(&cs);
        let batch_of = |slots: usize| {
            let cs = setup_mode_cs();
            let pv = zero_pv(&cs);
            let before = cs.num_constraints();
            let _ = fold_batch(cs.clone(), &[], slots, &pv.output_commitments, &FoldTarget::input(&pv, 0)).unwrap();
            cs.num_constraints() - before
        };
        let per_slot = batch_of(2) - batch_of(1);
        let _ = fold_pv;
        let before = cs.num_constraints();
        let _ = window_opens(cs.clone(), &msg, &msg, &msg, None).unwrap();
        let window = cs.num_constraints() - before;

        let parent_cs = setup_mode_cs();
        let pv = zero_pv(&parent_cs);
        let zero = || Fp::new_witness(parent_cs.clone(), || Ok(Fr::from(0u64))).unwrap();
        let root = zero();
        let before = parent_cs.num_constraints();
        let _ = parent_checks(parent_cs.clone(), None, &pv, &root, &root).unwrap();
        let parent = parent_cs.num_constraints() - before;

        let genesis_cs = setup_mode_cs();
        GenesisSpendCircuit::default().generate_constraints(genesis_cs.clone()).unwrap();

        let step_cs = setup_mode_cs();
        step_circuit_for_counting().generate_constraints(step_cs.clone()).unwrap();
        let fold_cs = setup_mode_cs();
        fold_circuit_for_counting().generate_constraints(fold_cs.clone()).unwrap();

        println!("one tag check:          {tag}");
        println!("one fold slot:          {per_slot}");
        println!("window opening:         {window}");
        println!("parent checks in total: {parent}");
        println!("GenesisSpendCircuit:    {}", genesis_cs.num_constraints());
        println!("SpendStepCircuit:       {}", step_cs.num_constraints());
        println!("FoldCircuit ({FOLD_BATCH} slots): {}", fold_cs.num_constraints());
        println!("public inputs:          {SPEND_PUBLIC_INPUT_COUNT}");
    }

    #[test]
    fn report_spend_density() {
        fn report(name: &str, build: impl FnOnce(ConstraintSystemRef<Fr>)) {
            let cs = setup_mode_cs();
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
        report("poseidon, 2 elements", |cs| {
            let xs: Vec<Fp> = (0..2).map(|_| Fp::new_witness(cs.clone(), || Ok(Fr::from(1u64))).unwrap()).collect();
            let _ = poseidon_hash_var(cs, &xs).unwrap();
        });
        report("GenesisSpendCircuit", |cs| GenesisSpendCircuit::default().generate_constraints(cs).unwrap());
        report("SpendStepCircuit", |cs| step_circuit_for_counting().generate_constraints(cs).unwrap());
    }

    #[test]
    fn report_fold_density() {
        for (name, cs) in [
            ("SpendStepCircuit", {
                let cs = setup_mode_cs();
                step_circuit_for_counting().generate_constraints(cs.clone()).unwrap();
                cs
            }),
            ("FoldCircuit", {
                let cs = setup_mode_cs();
                fold_circuit_for_counting().generate_constraints(cs.clone()).unwrap();
                cs
            }),
        ] {
            cs.finalize();
            let m = cs.to_matrices().unwrap();
            println!(
                "{name:<17} constraints {:>8}  nonzeros A {:>9} B {:>9} C {:>8}  total {:>9}",
                cs.num_constraints(),
                m.a_num_non_zero,
                m.b_num_non_zero,
                m.c_num_non_zero,
                m.a_num_non_zero + m.b_num_non_zero + m.c_num_non_zero,
            );
        }
    }

    #[test]
    fn report_verifier_costs() {
        use ark_crypto_primitives::snark::SNARKGadget;
        use ark_r1cs_std::alloc::AllocationMode;
        let chunks = SPEND_PUBLIC_INPUT_COUNT * chunks_per_value();
        for witness_vk in [false, true] {
            for bits_per_chunk in [Fr6::MODULUS_BIT_SIZE as usize, cloakkchain_circuit_wrap::CHUNK_BITS] {
                let cs = setup_mode_cs();
                let vk = if witness_vk {
                    VerifierGadget::<MNT6_753, MNT6PairingVar>::new_verification_key_unchecked(
                        cs.clone(),
                        || Ok(shaped_wrap_vk()),
                        AllocationMode::Witness,
                    )
                    .unwrap()
                } else {
                    VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), shaped_wrap_vk()).unwrap()
                };
                let after_vk = cs.num_constraints();
                let pvk = vk.prepare().unwrap();
                let after_prepare = cs.num_constraints();
                let bits: Vec<Vec<Boolean<Fr>>> = (0..chunks)
                    .map(|_| (0..bits_per_chunk).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect())
                    .collect();
                let input = BooleanInputVar::<Fr6, Fr>::new(bits);
                let proof = ProofVar::<MNT6_753, MNT6PairingVar>::new_witness(cs.clone(), || {
                    Ok(SpendStepCircuit::dummy_wrap_proof())
                })
                .unwrap();
                let before_verify = cs.num_constraints();
                let _ = VerifierGadget::<MNT6_753, MNT6PairingVar>::verify_with_processed_vk(&pvk, &input, &proof)
                    .unwrap();
                println!(
                    "vk {:<8} {:>3}-bit chunks: alloc {:>7}  prepare {:>7}  verify {:>8}  total {:>8}",
                    if witness_vk { "witness" } else { "constant" },
                    bits_per_chunk,
                    after_vk,
                    after_prepare - after_vk,
                    cs.num_constraints() - before_verify,
                    cs.num_constraints(),
                );
            }
        }
    }

    struct Wrapped {
        proof: Proof<MNT6_753>,
    }

    fn wrap<R: RngCore + CryptoRng>(
        wrap_pk: &ProvingKey<MNT6_753>,
        inner_vk: VerifyingKey<MNT4_753>,
        inner_proof: Proof<MNT4_753>,
        public_inputs: [Fr; SPEND_PUBLIC_INPUT_COUNT],
        rng: &mut R,
    ) -> Wrapped {
        let proof = cloakkchain_circuit_wrap::prove::<SPEND_PUBLIC_INPUT_COUNT, _>(
            wrap_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT> {
                inner_vk,
                inner_proof: Some(inner_proof),
                inner_public_inputs: Some(public_inputs),
            },
            rng,
        )
        .unwrap();
        Wrapped { proof }
    }

    #[test]
    fn proving_genesis_round_trip() {

        use ark_std::rand::{rngs::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, vk) = setup(&mut rng).unwrap();

        let c = genesis_circuit();
        let public_inputs = StepStatement::of_spend(c.core.public_values().unwrap(), Fr::from(0u64)).public_inputs();
        let proof = prove(&pk, c, &mut rng).unwrap();
        assert!(verify(&vk, &public_inputs, &proof).unwrap(), "a genuinely valid genesis-mint proof must verify");

        let mut tampered = public_inputs;
        tampered[0] += Fr::from(1u64);
        assert!(!verify(&vk, &tampered, &proof).unwrap(), "a proof must not verify against the wrong public inputs");
    }

    #[test]
    fn proving_chain_survives_copied_serial_numbers() {
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        use cloakkchain_circuit_wrap::inner_vk_hash;
        const COPIES: u64 = 3;
        let mut rng = StdRng::seed_from_u64(20260919);

        let (genesis_pk_data, genesis_vk) = setup(&mut rng).unwrap();
        let (wrap_pk, wrap_vk) = cloakkchain_circuit_wrap::setup::<SPEND_PUBLIC_INPUT_COUNT, _>(&mut rng).unwrap();
        let (fold_pk, fold_vk) = setup_fold(wrap_vk.clone(), &mut rng).unwrap();
        let genesis_vk_hash = inner_vk_hash(&genesis_vk);
        let fold_vk_hash = inner_vk_hash(&fold_vk);
        let (step_pk, step_vk) = setup_non_genesis(wrap_vk.clone(), genesis_vk_hash, fold_vk_hash, &mut rng).unwrap();
        let step_vk_hash = inner_vk_hash(&step_vk);

        fn satisfied<C: ConstraintSynthesizer<Fr> + Clone>(circuit: &C) -> bool {
            let cs = ConstraintSystem::<Fr>::new_ref();
            circuit.clone().generate_constraints(cs.clone()).unwrap();
            cs.is_satisfied().unwrap()
        }

        let mut w = world();
        let mut genesis_core = w.genesis.core.clone();
        genesis_core.vk_hash = Some(genesis_vk_hash);
        let genesis_statement = StepStatement::of_spend(w.genesis.pv.clone(), genesis_vk_hash);
        let genesis_proof = prove(&genesis_pk_data, GenesisSpendCircuit { core: genesis_core }, &mut rng).unwrap();
        assert!(verify(&genesis_vk, &genesis_statement.public_inputs(), &genesis_proof).unwrap());
        let wrap_genesis = wrap(&wrap_pk, genesis_vk, genesis_proof, genesis_statement.public_inputs(), &mut rng);

        let alice = w.alice_spends(&w.bob_coin, 1);
        let mut alice_core = alice.core.clone();
        alice_core.vk_hash = Some(step_vk_hash);
        let alice_statement = StepStatement::of_spend(alice.pv.clone(), step_vk_hash);
        let alice_circuit = SpendStepCircuit {
            core: alice_core,
            wrap_vk: wrap_vk.clone(),
            genesis_vk_hash,
            fold_vk_hash,
            input_parent_proofs: std::array::from_fn(|_| Some(wrap_genesis.proof.clone())),
            input_parent_statements: std::array::from_fn(|i| (i == 0).then(|| genesis_statement.clone())),
            input_parents: std::array::from_fn(|i| (i == 0).then(|| w.history.parent_witness(0, &w.genesis.pv, 1))),
        };

        let mut wrong_genesis = alice_circuit.clone();
        wrong_genesis.genesis_vk_hash += Fr::from(1u64);
        assert!(!satisfied(&wrong_genesis), "a parent under an unexpected VK must fail");
        assert!(satisfied(&alice_circuit), "Alice's witness should satisfy every constraint");
        let alice_proof = prove_non_genesis(&step_pk, alice_circuit, &mut rng).unwrap();
        assert!(verify_non_genesis(&step_vk, &alice_statement.public_inputs(), &alice_proof).unwrap());
        let mut latest = wrap(&wrap_pk, step_vk.clone(), alice_proof, alice_statement.public_inputs(), &mut rng);
        let mut latest_statement = alice_statement;

        for seed in 0..COPIES {
            w.history.append(&junk_copy(w.alice_nullifier(), seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let parent = w.history.parent_witness(slot, &alice.pv, size);
        assert_eq!(parent.windows[0].occurrences.len() as u64, COPIES);

        for batch in parent.windows[0].occurrences.chunks(2) {
            let fold = FoldCircuit {
                wrap_vk: wrap_vk.clone(),
                previous: Some(latest_statement.clone()),
                previous_proof: Some(latest.proof.clone()),
                input: 0,
                occurrences: batch.to_vec(),
                vk_hash: Some(fold_vk_hash),
            };
            assert!(satisfied(&fold), "the fold's witness should satisfy every constraint");
            let next = fold.statement().unwrap();
            assert_eq!(next.origin_vk_hash, step_vk_hash, "the chain's origin is Alice's spend key");
            let proof = prove_fold(&fold_pk, fold, &mut rng).unwrap();
            assert!(verify(&fold_vk, &next.public_inputs(), &proof).unwrap());
            latest = wrap(&wrap_pk, fold_vk.clone(), proof, next.public_inputs(), &mut rng);
            latest_statement = next;
        }
        assert_eq!(latest_statement.window_heads[0], parent.windows[0].leaf.occ);

        let (_, carol_pk) = owner(3);
        let bob = post(&w.history, w.bob_sk, &w.bob_coin, &[coin(4, 100, carol_pk)], size, Some(&parent), 2);
        let mut bob_core = bob.core.clone();
        bob_core.vk_hash = Some(step_vk_hash);
        let bob_statement = StepStatement::of_spend(bob.pv.clone(), step_vk_hash);
        let bob_circuit = SpendStepCircuit {
            core: bob_core,
            wrap_vk,
            genesis_vk_hash,
            fold_vk_hash,
            input_parent_proofs: std::array::from_fn(|_| Some(latest.proof.clone())),
            input_parent_statements: std::array::from_fn(|i| (i == 0).then(|| latest_statement.clone())),
            input_parents: std::array::from_fn(|i| (i == 0).then(|| parent.clone())),
        };

        let mut unfolded = bob_circuit.clone();
        unfolded.input_parent_statements[0].as_mut().unwrap().window_heads[0] = Fr::from(0u64);
        assert!(!satisfied(&unfolded), "a window head that misses copies must fail");

        assert!(satisfied(&bob_circuit), "Bob's witness should satisfy every constraint");
        let bob_proof = prove_non_genesis(&step_pk, bob_circuit, &mut rng).unwrap();
        assert!(verify_non_genesis(&step_vk, &bob_statement.public_inputs(), &bob_proof).unwrap());
        let mut tampered = bob_statement.public_inputs();
        tampered[0] += Fr::from(1u64);
        assert!(!verify_non_genesis(&step_vk, &tampered, &bob_proof).unwrap());
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn proving_two_input_chain_survives_copies_of_the_second_input() {
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        use cloakkchain_circuit_wrap::inner_vk_hash;
        let mut rng = StdRng::seed_from_u64(20261105);

        let (genesis_pk_data, genesis_vk) = setup(&mut rng).unwrap();
        let (wrap_pk, wrap_vk) = cloakkchain_circuit_wrap::setup::<SPEND_PUBLIC_INPUT_COUNT, _>(&mut rng).unwrap();
        let (fold_pk, fold_vk) = setup_fold(wrap_vk.clone(), &mut rng).unwrap();
        let genesis_vk_hash = inner_vk_hash(&genesis_vk);
        let fold_vk_hash = inner_vk_hash(&fold_vk);
        let (step_pk, step_vk) = setup_non_genesis(wrap_vk.clone(), genesis_vk_hash, fold_vk_hash, &mut rng).unwrap();
        let step_vk_hash = inner_vk_hash(&step_vk);

        fn satisfied<C: ConstraintSynthesizer<Fr> + Clone>(circuit: &C) -> bool {
            let cs = ConstraintSystem::<Fr>::new_ref();
            circuit.clone().generate_constraints(cs.clone()).unwrap();
            cs.is_satisfied().unwrap()
        }
        let prove_genesis = |posted: &Posted, rng: &mut StdRng| {
            let mut core = posted.core.clone();
            core.vk_hash = Some(genesis_vk_hash);
            let statement = StepStatement::of_spend(posted.pv.clone(), genesis_vk_hash);
            let proof = prove(&genesis_pk_data, GenesisSpendCircuit { core }, rng).unwrap();
            assert!(verify(&genesis_vk, &statement.public_inputs(), &proof).unwrap());
            let wrapped = wrap(&wrap_pk, genesis_vk.clone(), proof, statement.public_inputs(), rng);
            (statement, wrapped)
        };

        let mut w = world();
        let (alice, second_coin, second_mint) = two_coins(&mut w);
        let mints = [(prove_genesis(&w.genesis, &mut rng), 0usize, &w.genesis), (prove_genesis(&second_mint, &mut rng), 1, &second_mint)];
        let mut alice_core = alice.core.clone();
        alice_core.vk_hash = Some(step_vk_hash);
        let alice_statement = StepStatement::of_spend(alice.pv.clone(), step_vk_hash);
        let alice_circuit = SpendStepCircuit {
            core: alice_core,
            wrap_vk: wrap_vk.clone(),
            genesis_vk_hash,
            fold_vk_hash,
            input_parent_proofs: std::array::from_fn(|i| Some(mints[i].0 .1.proof.clone())),
            input_parent_statements: std::array::from_fn(|i| Some(mints[i].0 .0.clone())),
            input_parents: std::array::from_fn(|i| {
                Some(w.history.parent_witness(mints[i].1, &mints[i].2.pv, 2))
            }),
        };

        let mut swapped = alice_circuit.clone();
        swapped.input_parent_proofs.swap(0, 1);
        swapped.input_parent_statements.swap(0, 1);
        swapped.input_parents.swap(0, 1);
        assert!(!satisfied(&swapped), "each input must be created by its own parent");
        assert!(satisfied(&alice_circuit), "Alice's two-input witness should satisfy every constraint");
        let alice_proof = prove_non_genesis(&step_pk, alice_circuit, &mut rng).unwrap();
        assert!(verify_non_genesis(&step_vk, &alice_statement.public_inputs(), &alice_proof).unwrap());
        let mut latest = wrap(&wrap_pk, step_vk.clone(), alice_proof, alice_statement.public_inputs(), &mut rng);
        let mut latest_statement = alice_statement;

        let second_sn = derive_nullifier(second_coin.commitment(), &w.alice_sk);
        for seed in 0..2 {
            w.history.append(&junk_copy(second_sn, seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let parent = w.history.parent_witness(slot, &alice.pv, size);
        assert!(parent.windows[0].occurrences.is_empty());
        assert_eq!(parent.windows[1].occurrences.len(), 2);

        let fold = FoldCircuit {
            wrap_vk: wrap_vk.clone(),
            previous: Some(latest_statement.clone()),
            previous_proof: Some(latest.proof.clone()),
            input: 1,
            occurrences: parent.windows[1].occurrences.clone(),
            vk_hash: Some(fold_vk_hash),
        };

        let mut wrong_input = fold.clone();
        wrong_input.input = 0;
        assert!(!satisfied(&wrong_input), "copies must be folded under their own input's key");
        assert!(satisfied(&fold), "the fold's witness should satisfy every constraint");
        let next = fold.statement().unwrap();
        assert_eq!(next.window_heads, [Fr::from(0u64), parent.windows[1].leaf.occ]);
        let proof = prove_fold(&fold_pk, fold, &mut rng).unwrap();
        assert!(verify(&fold_vk, &next.public_inputs(), &proof).unwrap());
        latest = wrap(&wrap_pk, fold_vk.clone(), proof, next.public_inputs(), &mut rng);
        latest_statement = next;

        let bob_coin = coin(3, 150, owner(2).1);
        let bob = post(&w.history, w.bob_sk, &bob_coin, &[coin(4, 150, owner(3).1)], size, Some(&parent), 2);
        let mut bob_core = bob.core.clone();
        bob_core.vk_hash = Some(step_vk_hash);
        let bob_statement = StepStatement::of_spend(bob.pv.clone(), step_vk_hash);
        let bob_circuit = SpendStepCircuit {
            core: bob_core,
            wrap_vk,
            genesis_vk_hash,
            fold_vk_hash,
            input_parent_proofs: std::array::from_fn(|_| Some(latest.proof.clone())),
            input_parent_statements: std::array::from_fn(|i| (i == 0).then(|| latest_statement.clone())),
            input_parents: std::array::from_fn(|i| (i == 0).then(|| parent.clone())),
        };
        assert!(satisfied(&bob_circuit), "Bob's witness should satisfy every constraint");
        let bob_proof = prove_non_genesis(&step_pk, bob_circuit, &mut rng).unwrap();
        assert!(verify_non_genesis(&step_vk, &bob_statement.public_inputs(), &bob_proof).unwrap());
    }
}
