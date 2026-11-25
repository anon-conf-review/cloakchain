use std::collections::{BTreeMap, HashMap};

use ark_crypto_primitives::sponge::{
    poseidon::PoseidonSponge, CryptographicSponge, FieldBasedCryptographicSponge,
};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use serde::{Deserialize, Serialize};

mod field_serde {
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S, T>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: CanonicalSerialize,
    {
        let mut bytes = Vec::new();
        value
            .serialize_compressed(&mut bytes)
            .map_err(serde::ser::Error::custom)?;
        bytes.serialize(serializer)
    }

    pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: CanonicalDeserialize,
    {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        T::deserialize_compressed(&bytes[..]).map_err(serde::de::Error::custom)
    }
}
use sha2::{Digest, Sha256};
use x25519_dalek::{PublicKey as X25519PublicKey, StaticSecret as X25519Secret};

pub mod poseidon_params;

pub type Fr = ark_mnt4_753::Fr;

pub type OwnerPk = ark_mnt6_753::G1Affine;
pub type OwnerScalar = ark_mnt6_753::Fr;

fn poseidon_sponge() -> PoseidonSponge<Fr> {
    PoseidonSponge::new(&poseidon_params::mnt4_753_fr_poseidon_config())
}

pub fn poseidon_hash(inputs: &[Fr]) -> Fr {
    let mut sponge = poseidon_sponge();
    sponge.absorb(&inputs.to_vec());
    sponge.squeeze_native_field_elements(1)[0]
}

pub fn poseidon_hash_bytes(bytes: &[u8]) -> Fr {
    if bytes.is_empty() {
        return poseidon_hash(&[Fr::from(0u64)]);
    }
    let elems: Vec<Fr> = bytes
        .chunks(31)
        .map(Fr::from_le_bytes_mod_order)
        .collect();
    poseidon_hash(&elems)
}

pub fn fold_owner_scalar(sk: &OwnerScalar) -> Fr {
    fold_bits_le(&sk.into_bigint().to_bits_le())
}

fn fold_bits_le(bits: &[bool]) -> Fr {
    let chunks: Vec<Fr> = bits.chunks(248).map(bits_le_to_fr).collect();
    poseidon_hash(&chunks)
}

fn bits_le_to_fr(bits: &[bool]) -> Fr {
    let mut acc = Fr::from(0u64);
    let mut place = Fr::from(1u64);
    for &b in bits {
        if b {
            acc += place;
        }
        place *= Fr::from(2u64);
    }
    acc
}

pub fn owner_pk_to_field_pair(pk: &OwnerPk) -> (Fr, Fr) {

    match pk.xy() {
        Some((x, y)) => (x, y),
        None => (Fr::from(0u64), Fr::from(0u64)),
    }
}

pub fn genesis_sk() -> OwnerScalar {
    OwnerScalar::from(1u64)
}

pub fn genesis_pk() -> OwnerPk {
    derive_owner_pk(&genesis_sk())
}

pub fn derive_owner_pk(sk: &OwnerScalar) -> OwnerPk {
    (ark_mnt6_753::G1Projective::generator() * sk).into_affine()
}

pub fn derive_nullifier(coin_commitment: Fr, sk: &OwnerScalar) -> Fr {
    poseidon_hash(&[coin_commitment, fold_owner_scalar(sk)])
}

pub const TAG_KEY_DOMAIN: u64 = u64::from_be_bytes(*b"CLOAKTGK");

pub const TAG_DOMAIN: u64 = u64::from_be_bytes(*b"CLOAKTAG");

pub fn derive_tag_key(sk: &OwnerScalar, coin_commitment: Fr) -> Fr {
    poseidon_hash(&[Fr::from(TAG_KEY_DOMAIN), coin_commitment, fold_owner_scalar(sk)])
}

pub fn coin_tag(tag_key: Fr, nullifier: Fr, outputs_hash: Fr) -> Fr {
    poseidon_hash(&[Fr::from(TAG_DOMAIN), tag_key, nullifier, outputs_hash])
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct Coin {
    pub value: u64,
    pub seed: [u8; 32],
    #[serde(with = "field_serde")]
    pub owner_pk: OwnerPk,
}

const COIN_RAND_DOMAIN: [u8; 8] = *b"CLOAKCR1";

pub fn coin_rand(seed: &[u8; 32]) -> Fr {
    let mut bytes = Vec::with_capacity(96);
    for block in 0u8..3 {
        let mut h = Sha256::new();
        h.update(COIN_RAND_DOMAIN);
        h.update([block]);
        h.update(seed);
        bytes.extend_from_slice(&h.finalize());
    }
    Fr::from_le_bytes_mod_order(&bytes)
}

impl Coin {
    pub fn rand(&self) -> Fr {
        coin_rand(&self.seed)
    }

    pub fn commitment(&self) -> Fr {
        let (px, py) = owner_pk_to_field_pair(&self.owner_pk);
        poseidon_hash(&[Fr::from(self.value), self.rand(), px, py])
    }
}

fn compact() -> impl bincode::Options {
    bincode::DefaultOptions::new()
}

#[cfg(not(feature = "two-inputs"))]
pub const MAX_INPUTS: usize = 1;
#[cfg(feature = "two-inputs")]
pub const MAX_INPUTS: usize = 2;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {

    pub note_encs: Vec<Vec<u8>>,

    #[serde(with = "field_serde")]
    pub tag_keys: Vec<Fr>,

    pub anchor_size: u64,
    pub spend_proof: Vec<u8>,
}

impl Transaction {
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::Options::serialize(compact(), self).expect("Transaction is always serializable")
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        bincode::Options::deserialize(compact(), bytes).ok()
    }
}

const MAGIC_TAG: [u8; 8] = *b"CLOAKTX1";

pub const EK_SALT: [u8; 8] = *b"CLOAKEK1";

const DH_SALT: [u8; 8] = *b"CLOAKDH1";

const NOTE_SALT: [u8; 8] = *b"CLOAKNT2";

pub fn derive_enc_pk(enc_sk: &[u8; 32]) -> [u8; 32] {
    *X25519PublicKey::from(&X25519Secret::from(*enc_sk)).as_bytes()
}

fn xor_with_keystream(key: &[u8; 32], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(data.len());
    let mut counter: u64 = 0;
    while out.len() < data.len() {
        let mut h = Sha256::new();
        h.update(key);
        h.update(counter.to_le_bytes());
        out.extend_from_slice(&h.finalize());
        counter += 1;
    }
    out.truncate(data.len());
    for (o, d) in out.iter_mut().zip(data.iter()) {
        *o ^= d;
    }
    out
}

fn ek_secret(session_key: &[u8; 32]) -> X25519Secret {
    let mut h = Sha256::new();
    h.update(session_key);
    h.update(EK_SALT);
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&h.finalize());
    X25519Secret::from(bytes)
}

fn wrapping_key(shared: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(shared);
    h.update(DH_SALT);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoardEntry {

    pub ciphertext: Vec<u8>,

    pub ek_pk: [u8; 32],

    pub key_encs: Vec<[u8; 32]>,

    #[serde(with = "field_serde")]
    pub nullifiers: Vec<Fr>,

    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,

    #[serde(with = "field_serde")]
    pub tags: Vec<Fr>,
}

impl BoardEntry {
    pub fn outputs_hash(&self) -> Fr {
        poseidon_hash(&self.output_commitments)
    }

    pub fn receives_coin(&self, cn: &Fr) -> bool {
        self.output_commitments.contains(cn)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::Options::serialize(compact(), self).expect("BoardEntry is always serializable")
    }

    pub fn posted_inputs(&self) -> Vec<PostedInput> {
        self.nullifiers
            .iter()
            .take(MAX_INPUTS)
            .enumerate()
            .map(|(i, sn)| PostedInput { nullifier: *sn, tag: self.tags.get(i).copied().unwrap_or_default() })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct PostedInput {
    #[serde(with = "field_serde")]
    pub nullifier: Fr,
    #[serde(with = "field_serde")]
    pub tag: Fr,
}

pub fn encrypt_tx(
    tx: &Transaction,
    output_commitments: &[Fr],
    input_commitments: &[Fr],
    sender_sk: &OwnerScalar,
    recipient_pks: &[[u8; 32]],
    session_key: [u8; 32],
) -> BoardEntry {
    debug_assert!(input_commitments.iter().map(|cm| derive_tag_key(sender_sk, *cm)).eq(tx.tag_keys.iter().copied()));

    let ek_sk = ek_secret(&session_key);
    let ek_pk = *X25519PublicKey::from(&ek_sk).as_bytes();

    let mut plaintext = MAGIC_TAG.to_vec();
    plaintext.extend_from_slice(&tx.to_bytes());
    let ciphertext = xor_with_keystream(&session_key, &plaintext);

    let key_encs: Vec<[u8; 32]> = recipient_pks.iter().map(|rpk| {
        let recipient_pub = X25519PublicKey::from(*rpk);
        let shared = *ek_sk.diffie_hellman(&recipient_pub).as_bytes();
        let wk = wrapping_key(&shared);
        let mut enc = [0u8; 32];
        for (e, (w, s)) in enc.iter_mut().zip(wk.iter().zip(session_key.iter())) {
            *e = w ^ s;
        }
        enc
    }).collect();

    let outputs_hash = poseidon_hash(output_commitments);
    let nullifiers: Vec<Fr> = input_commitments.iter().map(|cm| derive_nullifier(*cm, sender_sk)).collect();
    let tags = input_commitments
        .iter()
        .zip(&nullifiers)
        .map(|(cm, sn)| coin_tag(derive_tag_key(sender_sk, *cm), *sn, outputs_hash))
        .collect();

    BoardEntry {
        ciphertext,
        ek_pk,
        key_encs,
        nullifiers,
        output_commitments: output_commitments.to_vec(),
        tags,
    }
}

pub fn scan_entry(
    owner_sk: &[u8; 32],
    entry: &BoardEntry,
) -> Option<Transaction> {
    let owner_secret = X25519Secret::from(*owner_sk);
    let ek_pub = X25519PublicKey::from(entry.ek_pk);
    let shared = *owner_secret.diffie_hellman(&ek_pub).as_bytes();
    let wk = wrapping_key(&shared);

    for key_enc in &entry.key_encs {
        let mut session_key = [0u8; 32];
        for (s, (w, e)) in session_key.iter_mut().zip(wk.iter().zip(key_enc.iter())) {
            *s = w ^ e;
        }
        if entry.ciphertext.len() <= 8 { continue; }
        let tx_bytes = xor_with_keystream(&session_key, &entry.ciphertext);
        if tx_bytes[..8] != MAGIC_TAG { continue; }
        if let Some(tx) = Transaction::from_bytes(&tx_bytes[8..]) {
            return Some(tx);
        }
    }
    None
}

pub fn recover_session_key(owner_sk: &[u8; 32], entry: &BoardEntry) -> Option<[u8; 32]> {
    let owner_secret = X25519Secret::from(*owner_sk);
    let ek_pub = X25519PublicKey::from(entry.ek_pk);
    let shared = *owner_secret.diffie_hellman(&ek_pub).as_bytes();
    let wk = wrapping_key(&shared);
    for key_enc in &entry.key_encs {
        let mut session_key = [0u8; 32];
        for (s, (w, e)) in session_key.iter_mut().zip(wk.iter().zip(key_enc.iter())) {
            *s = w ^ e;
        }

        if entry.ciphertext.len() > 8 {
            let tx_bytes = xor_with_keystream(&session_key, &entry.ciphertext);
            if tx_bytes[..8] == MAGIC_TAG {
                return Some(session_key);
            }
        }
    }
    None
}

pub const NOTE_LEN: usize = 8 + 32;

fn note_key(session_key: &[u8; 32], index: usize) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(session_key);
    h.update((index as u64).to_le_bytes());
    h.update(NOTE_SALT);
    let mut key = [0u8; 32];
    key.copy_from_slice(&h.finalize());
    key
}

pub fn build_note_enc(session_key: &[u8; 32], index: usize, coin: &Coin) -> Vec<u8> {
    let mut payload = coin.value.to_le_bytes().to_vec();
    payload.extend_from_slice(&coin.seed);
    xor_with_keystream(&note_key(session_key, index), &payload)
}

pub fn decrypt_note(
    session_key: &[u8; 32],
    index: usize,
    note_enc: &[u8],
    owner_pk: &OwnerPk,
    commitment: Fr,
) -> Option<Coin> {
    if note_enc.len() != NOTE_LEN {
        return None;
    }
    let dec = xor_with_keystream(&note_key(session_key, index), note_enc);
    let coin = Coin {
        value: u64::from_le_bytes(dec[..8].try_into().ok()?),
        seed: dec[8..].try_into().ok()?,
        owner_pk: *owner_pk,
    };
    (coin.commitment() == commitment).then_some(coin)
}

pub const TREE_DEPTH: usize = 32;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct LeafOpening {
    pub slot: u64,
    #[serde(with = "field_serde")]
    pub ciphertext_commitment: Fr,
    #[serde(with = "field_serde")]
    pub outputs_hash: Fr,

    pub inputs: Vec<PostedInput>,
    #[serde(with = "field_serde")]
    pub prev_board_root: Fr,
    #[serde(with = "field_serde")]
    pub prev_nullifier_root: Fr,
}

impl LeafOpening {
    pub fn new(slot: usize, entry: &BoardEntry, prev_board_root: Fr, prev_nullifier_root: Fr) -> Self {
        Self {
            slot: slot as u64,
            ciphertext_commitment: entry_ciphertext_commitment(entry),
            outputs_hash: entry.outputs_hash(),
            inputs: entry.posted_inputs(),
            prev_board_root,
            prev_nullifier_root,
        }
    }

    pub fn nullifier(&self, i: usize) -> Fr {
        self.inputs.get(i).map_or(Fr::from(0u64), |input| input.nullifier)
    }

    pub fn nullifiers(&self) -> [Fr; MAX_INPUTS] {
        std::array::from_fn(|i| self.nullifier(i))
    }

    pub fn hash(&self) -> Fr {
        let mut preimage = vec![Fr::from(self.slot), self.ciphertext_commitment, self.outputs_hash];
        for i in 0..MAX_INPUTS {
            let tag = self.inputs.get(i).map_or(Fr::from(0u64), |input| input.tag);
            preimage.extend([self.nullifier(i), tag]);
        }
        preimage.extend([self.prev_board_root, self.prev_nullifier_root]);
        poseidon_hash(&preimage)
    }

    pub fn occurrence(&self, i: usize) -> Occurrence {
        Occurrence { outputs_hash: self.outputs_hash, tag: self.inputs[i].tag }
    }

    pub fn occurrences_of(&self, nullifier: Fr) -> impl Iterator<Item = Occurrence> + '_ {
        (0..self.inputs.len()).filter(move |&i| self.inputs[i].nullifier == nullifier).map(|i| self.occurrence(i))
    }

    pub fn tag_valid(&self, i: usize, tag_key: Fr) -> bool {
        self.occurrence(i).tag_valid(self.inputs[i].nullifier, tag_key)
    }
}

pub fn merkle_leaf(slot: usize, entry: &BoardEntry, prev_board_root: Fr, prev_nullifier_root: Fr) -> Fr {
    LeafOpening::new(slot, entry, prev_board_root, prev_nullifier_root).hash()
}

pub fn entry_ciphertext_commitment(entry: &BoardEntry) -> Fr {
    ciphertext_commitment(&entry.ciphertext, &entry.ek_pk, &entry.key_encs)
}

fn ciphertext_commitment(ciphertext: &[u8], ek_pk: &[u8; 32], key_encs: &[[u8; 32]]) -> Fr {
    let key_encs_bytes: Vec<u8> = key_encs.iter().flatten().copied().collect();
    poseidon_hash(&[
        poseidon_hash_bytes(ciphertext),
        poseidon_hash_bytes(ek_pk),
        poseidon_hash_bytes(&key_encs_bytes),
    ])
}

fn merkle_combine(l: &Fr, r: &Fr) -> Fr {
    poseidon_hash(&[*l, *r])
}

fn zero_hashes() -> &'static [Fr] {
    static ZERO_HASHES: std::sync::OnceLock<Vec<Fr>> = std::sync::OnceLock::new();
    ZERO_HASHES.get_or_init(|| {
        let mut out = vec![Fr::from(0u64)];
        for _ in 0..TREE_DEPTH {
            let prev = *out.last().unwrap();
            out.push(merkle_combine(&prev, &prev));
        }
        out
    })
}

pub fn empty_root() -> Fr {
    zero_hashes()[TREE_DEPTH]
}

pub fn compute_root_from_path(leaf: Fr, slot: usize, path: &[Fr]) -> Fr {
    let mut current = leaf;
    let mut idx = slot;
    for sibling in path {
        current = if idx % 2 == 0 {
            merkle_combine(&current, sibling)
        } else {
            merkle_combine(sibling, &current)
        };
        idx >>= 1;
    }
    current
}

fn merkle_path_for_index(leaf_hashes: &[Fr], target_idx: usize) -> Vec<Fr> {
    let zeros = zero_hashes();
    let mut path = Vec::with_capacity(TREE_DEPTH);
    let mut level: Vec<Fr> = leaf_hashes.to_vec();
    let mut idx = target_idx;
    for d in 0..TREE_DEPTH {
        let sibling_idx = idx ^ 1;
        let sibling = if sibling_idx < level.len() {
            level[sibling_idx]
        } else {
            zeros[d]
        };
        path.push(sibling);

        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut i = 0;
        while i < level.len() {
            let left = level[i];
            let right = if i + 1 < level.len() { level[i + 1] } else { zeros[d] };
            next.push(merkle_combine(&left, &right));
            i += 2;
        }
        level = next;
        idx >>= 1;
    }
    path
}

#[derive(Clone, Debug)]
struct IncrementalTree {

    nodes: Vec<HashMap<usize, Fr>>,
}

impl IncrementalTree {
    fn new() -> Self {
        Self { nodes: vec![HashMap::new(); TREE_DEPTH + 1] }
    }

    fn set_leaf(&mut self, idx: usize, hash: Fr) {
        let zeros = zero_hashes();
        let mut cur_idx = idx;
        let mut cur_hash = hash;
        for d in 0..TREE_DEPTH {
            self.nodes[d].insert(cur_idx, cur_hash);
            let sibling_idx = cur_idx ^ 1;
            let sibling = self.nodes[d].get(&sibling_idx).copied().unwrap_or(zeros[d]);
            cur_hash = if cur_idx % 2 == 0 { merkle_combine(&cur_hash, &sibling) } else { merkle_combine(&sibling, &cur_hash) };
            cur_idx >>= 1;
        }
        self.nodes[TREE_DEPTH].insert(cur_idx, cur_hash);
    }

    fn root(&self) -> Fr {
        self.nodes[TREE_DEPTH].get(&0).copied().unwrap_or_else(empty_root)
    }

    fn path_for(&self, idx: usize) -> Vec<Fr> {
        let zeros = zero_hashes();
        let mut path = Vec::with_capacity(TREE_DEPTH);
        let mut cur_idx = idx;
        for d in 0..TREE_DEPTH {
            let sibling_idx = cur_idx ^ 1;
            path.push(self.nodes[d].get(&sibling_idx).copied().unwrap_or(zeros[d]));
            cur_idx >>= 1;
        }
        path
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexedLeaf {
    #[serde(with = "field_serde")]
    pub value: Fr,
    #[serde(with = "field_serde")]
    pub next_value: Fr,
    pub next_index: u64,

    #[serde(with = "field_serde")]
    pub occ: Fr,
}

fn max_nullifier() -> Fr {
    -Fr::from(1u64)
}

impl IndexedLeaf {
    fn hash(&self) -> Fr {
        poseidon_hash(&[self.value, self.next_value, Fr::from(self.next_index), self.occ])
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct Occurrence {
    #[serde(with = "field_serde")]
    pub outputs_hash: Fr,
    #[serde(with = "field_serde")]
    pub tag: Fr,
}

impl Occurrence {

    pub fn link(&self, occ_prev: Fr) -> Fr {
        poseidon_hash(&[occ_prev, self.outputs_hash, self.tag])
    }

    pub fn tag_valid(&self, nullifier: Fr, tag_key: Fr) -> bool {
        self.tag == coin_tag(tag_key, nullifier, self.outputs_hash)
    }

    pub fn is_harmless(&self, nullifier: Fr, tag_key: Fr, outputs_hash: Fr) -> bool {
        self.outputs_hash == outputs_hash || !self.tag_valid(nullifier, tag_key)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct NonMembershipWitness {
    pub low_leaf: IndexedLeaf,
    pub low_leaf_index: u64,
    #[serde(with = "field_serde")]
    pub sibling_path: Vec<Fr>,
}

pub fn verify_nonmembership(root: Fr, target: Fr, witness: &NonMembershipWitness) -> bool {
    if !(witness.low_leaf.value < target && target < witness.low_leaf.next_value) {
        return false;
    }
    let leaf_hash = witness.low_leaf.hash();
    compute_root_from_path(leaf_hash, witness.low_leaf_index as usize, &witness.sibling_path) == root
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct WindowWitness {
    pub leaf: IndexedLeaf,
    pub leaf_index: u64,
    #[serde(with = "field_serde")]
    pub sibling_path: Vec<Fr>,

    pub occurrences: Vec<Occurrence>,
}

pub fn verify_occurrences(root: Fr, target: Fr, witness: &WindowWitness) -> bool {
    let occ = witness.occurrences.iter().fold(Fr::from(0u64), |prev, o| o.link(prev));
    !witness.occurrences.is_empty()
        && witness.leaf.value == target
        && witness.leaf.occ == occ
        && compute_root_from_path(witness.leaf.hash(), witness.leaf_index as usize, &witness.sibling_path) == root
}

pub fn check_window(root: Fr, nullifier: Fr, tag_key: Fr, outputs_hash: Fr, witness: &WindowWitness) -> bool {
    if witness.occurrences.is_empty() {
        witness.leaf.value < nullifier
            && nullifier < witness.leaf.next_value
            && compute_root_from_path(witness.leaf.hash(), witness.leaf_index as usize, &witness.sibling_path) == root
    } else {
        verify_occurrences(root, nullifier, witness)
            && witness.occurrences.iter().all(|o| o.is_harmless(nullifier, tag_key, outputs_hash))
    }
}

#[derive(Clone, Debug)]
pub struct NullifierTree {
    leaves: Vec<IndexedLeaf>,

    index_of: BTreeMap<Fr, usize>,
    tree: IncrementalTree,

    chains: BTreeMap<Fr, Vec<Occurrence>>,
}

impl NullifierTree {

    pub fn new() -> Self {
        let sentinel = IndexedLeaf {
            value: Fr::from(0u64),
            next_value: max_nullifier(),
            next_index: 0,
            occ: Fr::from(0u64),
        };
        let mut tree = Self {
            leaves: vec![sentinel.clone()],
            index_of: BTreeMap::new(),
            tree: IncrementalTree::new(),
            chains: BTreeMap::new(),
        };
        tree.index_of.insert(sentinel.value, 0);
        tree.tree.set_leaf(0, sentinel.hash());
        tree
    }

    pub fn root(&self) -> Fr {
        self.tree.root()
    }

    pub fn contains(&self, value: Fr) -> bool {
        self.index_of.contains_key(&value)
    }

    fn find_low_leaf_index(&self, target: Fr) -> usize {
        *self.index_of.range(..target).next_back().map(|(_, idx)| idx)
            .expect("no matching leaf — target is 0 or tree invariant violated")
    }

    pub fn insert(&mut self, value: Fr, occurrence: &Occurrence) -> Fr {
        if let Some(&idx) = self.index_of.get(&value) {
            self.leaves[idx].occ = occurrence.link(self.leaves[idx].occ);
            self.tree.set_leaf(idx, self.leaves[idx].hash());
        } else {
            let low_idx = self.find_low_leaf_index(value);
            let low = self.leaves[low_idx].clone();
            let new_index = self.leaves.len();
            let updated_low = IndexedLeaf { next_value: value, next_index: new_index as u64, ..low.clone() };
            let new_leaf = IndexedLeaf {
                value,
                next_value: low.next_value,
                next_index: low.next_index,
                occ: occurrence.link(Fr::from(0u64)),
            };

            self.leaves[low_idx] = updated_low.clone();
            self.leaves.push(new_leaf.clone());
            self.index_of.insert(value, new_index);

            self.tree.set_leaf(low_idx, updated_low.hash());
            self.tree.set_leaf(new_index, new_leaf.hash());
        }
        self.chains.entry(value).or_default().push(occurrence.clone());
        self.root()
    }

    pub fn prove_non_membership(&self, target: Fr) -> NonMembershipWitness {
        let low_idx = self.find_low_leaf_index(target);
        NonMembershipWitness {
            low_leaf: self.leaves[low_idx].clone(),
            low_leaf_index: low_idx as u64,
            sibling_path: self.tree.path_for(low_idx),
        }
    }

    pub fn prove_occurrences(&self, target: Fr) -> Option<WindowWitness> {
        let idx = *self.index_of.get(&target)?;
        Some(WindowWitness {
            leaf: self.leaves[idx].clone(),
            leaf_index: idx as u64,
            sibling_path: self.tree.path_for(idx),
            occurrences: self.chains.get(&target).cloned().unwrap_or_default(),
        })
    }

    pub fn prove_window(&self, target: Fr) -> WindowWitness {
        self.prove_occurrences(target).unwrap_or_else(|| {
            let low_idx = self.find_low_leaf_index(target);
            WindowWitness {
                leaf: self.leaves[low_idx].clone(),
                leaf_index: low_idx as u64,
                sibling_path: self.tree.path_for(low_idx),
                occurrences: Vec::new(),
            }
        })
    }
}

impl Default for NullifierTree {
    fn default() -> Self {
        Self::new()
    }
}

fn insert_inputs(tree: &mut NullifierTree, opening: &LeafOpening) {
    for i in 0..opening.inputs.len() {
        tree.insert(opening.inputs[i].nullifier, &opening.occurrence(i));
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct Anchor {
    pub size: u64,
    #[serde(with = "field_serde")]
    pub board_root: Fr,
    #[serde(with = "field_serde")]
    pub nullifier_root: Fr,
}

#[derive(Clone, Debug)]
pub struct History {
    board: IncrementalTree,
    occurrences: NullifierTree,
    openings: Vec<LeafOpening>,
    leaves: Vec<Fr>,

    board_roots: Vec<Fr>,
    nullifier_roots: Vec<Fr>,
    slots_by_nullifier: BTreeMap<Fr, Vec<usize>>,
}

impl History {
    pub fn new() -> Self {
        let board = IncrementalTree::new();
        let occurrences = NullifierTree::new();
        let board_roots = vec![board.root()];
        let nullifier_roots = vec![occurrences.root()];
        Self {
            board,
            occurrences,
            openings: Vec::new(),
            leaves: Vec::new(),
            board_roots,
            nullifier_roots,
            slots_by_nullifier: BTreeMap::new(),
        }
    }

    pub fn append(&mut self, entry: &BoardEntry) -> usize {
        let slot = self.openings.len();
        let opening = LeafOpening::new(slot, entry, self.board.root(), self.occurrences.root());
        let leaf = opening.hash();
        self.board.set_leaf(slot, leaf);
        insert_inputs(&mut self.occurrences, &opening);
        for input in &opening.inputs {
            let slots = self.slots_by_nullifier.entry(input.nullifier).or_default();
            if slots.last() != Some(&slot) {
                slots.push(slot);
            }
        }
        self.openings.push(opening);
        self.leaves.push(leaf);
        self.board_roots.push(self.board.root());
        self.nullifier_roots.push(self.occurrences.root());
        slot
    }

    pub fn from_entries(entries: &[BoardEntry]) -> Self {
        let mut history = Self::new();
        for entry in entries {
            history.append(entry);
        }
        history
    }

    pub fn len(&self) -> usize {
        self.openings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.openings.is_empty()
    }

    pub fn anchor_at(&self, size: usize) -> Option<Anchor> {
        Some(Anchor {
            size: size as u64,
            board_root: *self.board_roots.get(size)?,
            nullifier_root: *self.nullifier_roots.get(size)?,
        })
    }

    pub fn opening(&self, slot: usize) -> Option<&LeafOpening> {
        self.openings.get(slot)
    }

    pub fn board_path(&self, slot: usize, size: usize) -> Vec<Fr> {
        merkle_path_for_index(&self.leaves[..size], slot)
    }

    pub fn nullifier_tree_at(&self, size: usize) -> NullifierTree {
        let mut tree = NullifierTree::new();
        for opening in &self.openings[..size] {
            insert_inputs(&mut tree, opening);
        }
        tree
    }

    pub fn occurrences_between(&self, nullifier: Fr, from_size: usize, before_slot: usize) -> Vec<Occurrence> {
        self.slots_by_nullifier
            .get(&nullifier)
            .into_iter()
            .flatten()
            .filter(|&&slot| from_size <= slot && slot < before_slot)
            .flat_map(|&slot| self.openings[slot].occurrences_of(nullifier))
            .collect()
    }

    pub fn parent_witness(&self, parent_slot: usize, public_values: &SpendPublicValues, size: usize) -> ParentWitness {
        let leaf = self.openings[parent_slot].clone();
        let anchor_slot = public_values.anchor.size as usize;
        let before = self.nullifier_tree_at(parent_slot);
        ParentWitness {
            public_values: public_values.clone(),
            windows: leaf.inputs.iter().map(|input| before.prove_window(input.nullifier)).collect(),
            leaf,
            leaf_path: self.board_path(parent_slot, size),
            anchor_leaf: self.openings[anchor_slot].clone(),
            anchor_leaf_path: self.board_path(anchor_slot, size),
        }
    }
}

impl Default for History {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct SpendPublicValues {
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    pub anchor: Anchor,
    #[serde(with = "field_serde")]
    pub nullifiers: Vec<Fr>,
    #[serde(with = "field_serde")]
    pub tag_keys: Vec<Fr>,
}

impl SpendPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("SpendPublicValues is always serializable")
    }
}

pub fn check_receipt(
    history: &History,
    slot: usize,
    entry: &BoardEntry,
    tx: &Transaction,
    verify_proof: impl FnOnce(&SpendPublicValues, &[u8]) -> bool,
) -> Result<SpendPublicValues, &'static str> {
    let opening = history.opening(slot).ok_or("carrier's slot is not in this history")?;
    if *opening != LeafOpening::new(slot, entry, opening.prev_board_root, opening.prev_nullifier_root) {
        return Err("carrier does not match this history's entry at that slot");
    }

    let size = tx.anchor_size as usize;
    let anchor = match history.anchor_at(size) {
        Some(anchor) if size <= slot => anchor,
        _ => return Err("anchor is not a real state preceding the carrier"),
    };

    if opening.inputs.is_empty() || tx.tag_keys.len() != opening.inputs.len() {
        return Err("carrier must have one key per posted input");
    }

    let public_values = SpendPublicValues {
        output_commitments: entry.output_commitments.clone(),
        anchor,
        nullifiers: opening.inputs.iter().map(|input| input.nullifier).collect(),
        tag_keys: tx.tag_keys.clone(),
    };
    if !verify_proof(&public_values, &tx.spend_proof) {
        return Err("spend proof does not verify");
    }

    for (i, (input, &tag_key)) in opening.inputs.iter().zip(&tx.tag_keys).enumerate() {
        if !opening.tag_valid(i, tag_key) {
            return Err("carrier's tag does not verify under its tag key");
        }
        let window = history.occurrences_between(input.nullifier, size, slot);
        if window.iter().any(|o| !o.is_harmless(input.nullifier, tag_key, opening.outputs_hash)) {
            return Err("double-spend: a validly tagged spend of different outputs came first");
        }
    }

    Ok(public_values)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct ParentWitness {

    pub public_values: SpendPublicValues,
    pub leaf: LeafOpening,
    #[serde(with = "field_serde")]
    pub leaf_path: Vec<Fr>,

    pub anchor_leaf: LeafOpening,
    #[serde(with = "field_serde")]
    pub anchor_leaf_path: Vec<Fr>,

    pub windows: Vec<WindowWitness>,
}

pub fn check_spend(
    sk: &OwnerScalar,
    input_coins: &[Coin],
    output_coins: &[Coin],
    output_commitments: &[Fr],
    anchor: &Anchor,
    nonmemberships: &[NonMembershipWitness],
    parents: &[ParentWitness],
) -> Result<SpendPublicValues, &'static str> {
    if input_coins.is_empty() || input_coins.len() > MAX_INPUTS || nonmemberships.len() != input_coins.len() {
        return Err("a spend has 1 to MAX_INPUTS inputs, each with a non-membership witness");
    }
    let pk = derive_owner_pk(sk);
    if input_coins.iter().any(|coin| coin.owner_pk != pk) {
        return Err("input coin's owner does not match the spender");
    }

    let commitments: Vec<Fr> = input_coins.iter().map(Coin::commitment).collect();
    let nullifiers: Vec<Fr> = commitments.iter().map(|cm| derive_nullifier(*cm, sk)).collect();

    if (1..nullifiers.len()).any(|k| nullifiers[..k].contains(&nullifiers[k])) {
        return Err("a spend cannot consume the same coin twice");
    }

    if nullifiers.iter().zip(nonmemberships).any(|(sn, w)| !verify_nonmembership(anchor.nullifier_root, *sn, w)) {
        return Err("nullifier is already present at this anchor");
    }

    if output_coins.len() > output_commitments.len() {
        return Err("more output_coins than output_commitments");
    }
    for (coin, cn) in output_coins.iter().zip(output_commitments.iter()) {
        if &coin.commitment() != cn {
            return Err("output coin does not match its commitment");
        }
    }

    if output_commitments[output_coins.len()..].iter().any(|cn| *cn != Fr::from(0u64)) {
        return Err("unused output slots must hold a zero commitment");
    }

    let total_in: u128 = input_coins.iter().map(|c| c.value as u128).sum();
    let total_out: u128 = output_coins.iter().map(|c| c.value as u128).sum();
    if total_in != total_out {
        return Err("transaction violates value conservation: sum(inputs) must equal sum(outputs)");
    }

    if parents.is_empty() {

        if pk != genesis_pk() {
            return Err("only the genesis key may mint without provenance");
        }
    } else if parents.len() != input_coins.len() {
        return Err("every input needs its own parent");
    } else {
        for (parent, commitment) in parents.iter().zip(&commitments) {
            check_parent(parent, *commitment, anchor)?;
        }
    }

    Ok(SpendPublicValues {
        output_commitments: output_commitments.to_vec(),
        anchor: anchor.clone(),
        nullifiers,
        tag_keys: commitments.iter().map(|cm| derive_tag_key(sk, *cm)).collect(),
    })
}

fn check_parent(parent: &ParentWitness, commitment: Fr, anchor: &Anchor) -> Result<(), &'static str> {
    let pv = &parent.public_values;
    let leaf = &parent.leaf;

    if compute_root_from_path(leaf.hash(), leaf.slot as usize, &parent.leaf_path) != anchor.board_root {
        return Err("parent entry is not in this spend's anchor state");
    }

    let padded = |real: &[Fr]| -> Option<[Fr; MAX_INPUTS]> {
        let mut out = [Fr::from(0u64); MAX_INPUTS];
        out.get_mut(..real.len())?.copy_from_slice(real);
        Some(out)
    };
    if padded(&pv.nullifiers) != Some(leaf.nullifiers()) || poseidon_hash(&pv.output_commitments) != leaf.outputs_hash
    {
        return Err("parent proof disagrees with the parent entry");
    }
    if !pv.output_commitments.contains(&commitment) {
        return Err("parent does not create the input coin");
    }

    let anchor_leaf = &parent.anchor_leaf;
    if compute_root_from_path(anchor_leaf.hash(), anchor_leaf.slot as usize, &parent.anchor_leaf_path)
        != anchor.board_root
    {
        return Err("parent's anchor leaf is not in this spend's anchor state");
    }
    if anchor_leaf.slot != pv.anchor.size
        || anchor_leaf.prev_board_root != pv.anchor.board_root
        || anchor_leaf.prev_nullifier_root != pv.anchor.nullifier_root
        || pv.anchor.size > leaf.slot
    {
        return Err("parent's anchor is not a real state preceding it");
    }

    for i in (0..leaf.inputs.len()).filter(|&i| leaf.inputs[i].nullifier != Fr::from(0u64)) {
        let (Some(&tag_key), Some(window)) = (pv.tag_keys.get(i), parent.windows.get(i)) else {
            return Err("parent needs one tag key and one window per parent input");
        };

        if !leaf.tag_valid(i, tag_key) {
            return Err("parent's tag does not verify");
        }
        if !check_window(leaf.prev_nullifier_root, leaf.inputs[i].nullifier, tag_key, leaf.outputs_hash, window) {
            return Err("parent's window is not clean");
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn enc_party(seed: u8) -> ([u8; 32], [u8; 32]) {
        let mut sk = [0u8; 32];
        sk[1] = seed;

        let secret = X25519Secret::from(sk);
        let pk = *X25519PublicKey::from(&secret).as_bytes();
        (sk, pk)
    }

    fn owner_party(seed: u8) -> (OwnerScalar, OwnerPk) {
        let sk = OwnerScalar::from((seed as u64) + 100);
        (sk, derive_owner_pk(&sk))
    }

    fn coin(seed: u8, value: u64, owner_pk: OwnerPk) -> Coin {
        Coin { value, seed: [seed; 32], owner_pk }
    }

    struct Spend {
        entry: BoardEntry,
        tx: Transaction,
        pv: SpendPublicValues,
    }

    fn proof_ok(pv: &SpendPublicValues, proof: &[u8]) -> bool {
        pv.encode() == proof
    }

    fn spend(
        history: &History,
        sk: OwnerScalar,
        input: &Coin,
        outputs: &[Coin],
        anchor_size: usize,
        parent: Option<&ParentWitness>,
        id: u64,
    ) -> Result<Spend, &'static str> {
        let parents: Vec<ParentWitness> = parent.into_iter().cloned().collect();
        spend_inputs(history, sk, std::slice::from_ref(input), outputs, anchor_size, &parents, id)
    }

    fn spend_inputs(
        history: &History,
        sk: OwnerScalar,
        inputs: &[Coin],
        outputs: &[Coin],
        anchor_size: usize,
        parents: &[ParentWitness],
        id: u64,
    ) -> Result<Spend, &'static str> {
        let anchor = history.anchor_at(anchor_size).unwrap();
        let commitments: Vec<Fr> = inputs.iter().map(Coin::commitment).collect();
        let tree = history.nullifier_tree_at(anchor_size);
        let nonmemberships: Vec<NonMembershipWitness> =
            commitments.iter().map(|cm| tree.prove_non_membership(derive_nullifier(*cm, &sk))).collect();
        let output_commitments: Vec<Fr> = outputs.iter().map(Coin::commitment).collect();
        let pv = check_spend(&sk, inputs, outputs, &output_commitments, &anchor, &nonmemberships, parents)?;

        let session_key = {
            let mut h = Sha256::new();
            h.update(id.to_le_bytes());
            h.update(EK_SALT);
            let mut out = [0u8; 32];
            out.copy_from_slice(&h.finalize());
            out
        };
        let tx = Transaction {
            note_encs: outputs.iter().enumerate().map(|(i, c)| build_note_enc(&session_key, i, c)).collect(),
            tag_keys: commitments.iter().map(|cm| derive_tag_key(&sk, *cm)).collect(),
            anchor_size: anchor.size,
            spend_proof: pv.encode(),
        };
        let entry = encrypt_tx(&tx, &output_commitments, &commitments, &sk, &[enc_party(9).1], session_key);
        Ok(Spend { entry, tx, pv })
    }

    fn junk_copy(nullifier: Fr, seed: u8) -> BoardEntry {
        BoardEntry {
            ciphertext: vec![seed; 40],
            ek_pk: [seed; 32],
            key_encs: vec![[seed; 32]],
            nullifiers: vec![nullifier],
            output_commitments: vec![Fr::from(seed as u64)],
            tags: vec![Fr::from(seed as u64)],
        }
    }

    struct World {
        history: History,
        genesis: Spend,
        alice_coin: Coin,
        alice_sk: OwnerScalar,
        bob_coin: Coin,
        carol_coin: Coin,
    }

    fn world() -> World {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);
        let alice_coin = coin(0xA2, 100, alice_pk);
        let mut history = History::new();
        let genesis_input = coin(0xA1, 100, genesis_pk());
        let genesis =
            spend(&history, genesis_sk(), &genesis_input, &[alice_coin.clone()], 0, None, 0).unwrap();
        history.append(&genesis.entry);
        World {
            history,
            genesis,
            alice_coin,
            alice_sk,
            bob_coin: coin(0xB1, 100, bob_pk),
            carol_coin: coin(0xC1, 100, carol_pk),
        }
    }

    impl World {
        fn parent_is_genesis(&self, anchor_size: usize) -> ParentWitness {
            self.history.parent_witness(0, &self.genesis.pv, anchor_size)
        }

        fn alice_spends(&self, output: &Coin, anchor_size: usize, id: u64) -> Result<Spend, &'static str> {
            let parent = self.parent_is_genesis(anchor_size);
            spend(&self.history, self.alice_sk, &self.alice_coin, std::slice::from_ref(output), anchor_size, Some(&parent), id)
        }

        fn alice_nullifier(&self) -> Fr {
            derive_nullifier(self.alice_coin.commitment(), &self.alice_sk)
        }

        fn receipt(&self, slot: usize, s: &Spend) -> Result<SpendPublicValues, &'static str> {
            check_receipt(&self.history, slot, &s.entry, &s.tx, proof_ok)
        }

        fn bob_spends_onward(&self, slot: usize, carrier: &Spend) -> Result<Spend, &'static str> {
            let (bob_sk, _) = owner_party(2);
            let size = self.history.len();
            let parent = self.history.parent_witness(slot, &carrier.pv, size);
            spend(&self.history, bob_sk, &self.bob_coin, std::slice::from_ref(&self.carol_coin), size, Some(&parent), 100)
        }
    }

    #[test]
    fn tag_key_is_per_coin_and_unrelated_to_the_nullifier() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (bob_sk, _) = owner_party(2);
        let cm = coin(1, 5, alice_pk).commitment();
        let other_cm = coin(2, 5, alice_pk).commitment();

        assert_eq!(derive_tag_key(&alice_sk, cm), derive_tag_key(&alice_sk, cm));
        assert_ne!(derive_tag_key(&alice_sk, cm), derive_tag_key(&alice_sk, other_cm));
        assert_ne!(derive_tag_key(&alice_sk, cm), derive_tag_key(&bob_sk, cm));
        assert_ne!(derive_tag_key(&alice_sk, cm), derive_nullifier(cm, &alice_sk));
    }

    #[test]
    fn tag_covers_nullifier_and_outputs_only() {
        let w = world();
        let s = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let tk = s.tx.tag_keys[0];
        let valid = |e: &BoardEntry| e.tags[0] == coin_tag(tk, e.nullifiers[0], e.outputs_hash());
        assert!(valid(&s.entry));

        let tampered = |edit: &dyn Fn(&mut BoardEntry)| {
            let mut e = s.entry.clone();
            edit(&mut e);
            valid(&e)
        };
        assert!(!tampered(&|e| e.nullifiers[0] += Fr::from(1u64)));
        assert!(!tampered(&|e| e.output_commitments[0] += Fr::from(1u64)));
        assert!(!tampered(&|e| e.tags[0] += Fr::from(1u64)));

        assert!(tampered(&|e| e.ciphertext[0] ^= 1));

        assert!(s.entry.tags[0] != coin_tag(tk + Fr::from(1u64), s.entry.nullifiers[0], s.entry.outputs_hash()));
    }

    #[test]
    fn posted_bytes_contain_no_roots_or_tag_key() {
        let mut w = world();
        let s = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&s.entry);
        let opening = w.history.opening(1).unwrap();

        let posted = s.entry.to_bytes();
        let contains = |needle: Vec<u8>| posted.windows(needle.len()).any(|window| window == needle);
        let fr_bytes = |x: Fr| {
            let mut out = Vec::new();
            x.serialize_compressed(&mut out).unwrap();
            out
        };
        assert!(contains(fr_bytes(s.entry.nullifiers[0])), "sanity: the encoding under test is the right one");
        assert!(!contains(fr_bytes(opening.prev_board_root)));
        assert!(!contains(fr_bytes(opening.prev_nullifier_root)));
        assert!(!contains(fr_bytes(s.tx.tag_keys[0])));
    }

    #[test]
    fn encrypt_decrypt_round_trips_for_participants_and_rejects_outsiders() {
        let w = world();
        let s = w.alice_spends(&w.bob_coin, 1, 1).unwrap();

        assert_eq!(scan_entry(&enc_party(9).0, &s.entry), Some(s.tx.clone()));
        assert_eq!(scan_entry(&enc_party(2).0, &s.entry), None);
        assert_eq!(scan_entry(&enc_party(3).0, &s.entry), None);

        let session_key = recover_session_key(&enc_party(9).0, &s.entry).unwrap();
        let (bob_pk, cm) = (w.bob_coin.owner_pk, s.entry.output_commitments[0]);
        assert_eq!(decrypt_note(&session_key, 0, &s.tx.note_encs[0], &bob_pk, cm), Some(w.bob_coin.clone()));
        assert_eq!(decrypt_note(&session_key, 1, &s.tx.note_encs[0], &bob_pk, cm), None);

        assert_eq!(decrypt_note(&session_key, 0, &s.tx.note_encs[0], &owner_party(3).1, cm), None);
    }

    #[test]
    fn hidden_payload_repeats_nothing_the_recipient_has() {
        let w = world();
        let s = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        assert_eq!(s.tx.note_encs[0].len(), NOTE_LEN);
        let plaintext = s.tx.to_bytes();
        let fr_bytes = |x: Fr| {
            let mut out = Vec::new();
            x.serialize_compressed(&mut out).unwrap();
            out
        };
        let contains = |needle: Vec<u8>| plaintext.windows(needle.len()).any(|window| window == needle);
        assert!(contains(fr_bytes(s.tx.tag_keys[0])), "sanity: the encoding under test is the right one");
        assert!(!contains(fr_bytes(s.entry.output_commitments[0])));
        assert!(!contains(fr_bytes(s.pv.anchor.board_root)));
        assert!(!contains(fr_bytes(s.pv.anchor.nullifier_root)));
        assert_eq!(Transaction::from_bytes(&plaintext), Some(s.tx.clone()));
    }

    #[test]
    fn multi_output_tx_each_recipient_sees_only_own_note() {
        let (_, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let bob_coin = coin(0xB1, 40, bob_pk);
        let alice_change = coin(0xB2, 60, alice_pk);
        let session_key = [7u8; 32];

        let bob_note = build_note_enc(&session_key, 0, &bob_coin);
        let change_note = build_note_enc(&session_key, 1, &alice_change);

        let (bob_cm, change_cm) = (bob_coin.commitment(), alice_change.commitment());
        assert_eq!(decrypt_note(&session_key, 0, &bob_note, &bob_pk, bob_cm), Some(bob_coin));
        assert_eq!(decrypt_note(&session_key, 1, &change_note, &alice_pk, change_cm), Some(alice_change));
        assert_eq!(decrypt_note(&session_key, 1, &bob_note, &bob_pk, bob_cm), None);
        assert_eq!(decrypt_note(&session_key, 0, &change_note, &alice_pk, change_cm), None);

        assert_eq!(decrypt_note(&session_key, 1, &change_note, &bob_pk, change_cm), None);
    }

    #[test]
    fn history_tracks_roots_per_slot_and_opens_against_old_anchors() {
        let mut w = world();
        let sn = w.alice_nullifier();
        w.history.append(&junk_copy(sn, 1));
        w.history.append(&junk_copy(Fr::from(5u64), 2));

        for slot in 0..3 {
            let opening = w.history.opening(slot).unwrap();
            let before = w.history.anchor_at(slot).unwrap();
            assert_eq!(opening.prev_board_root, before.board_root);
            assert_eq!(opening.prev_nullifier_root, before.nullifier_root);

            for size in (slot + 1)..=3 {
                let path = w.history.board_path(slot, size);
                assert_eq!(
                    compute_root_from_path(opening.hash(), slot, &path),
                    w.history.anchor_at(size).unwrap().board_root,
                );
            }
        }
        assert!(w.history.anchor_at(3).is_some());
        assert!(w.history.anchor_at(4).is_none());

        assert_ne!(w.history.anchor_at(1).unwrap().nullifier_root, w.history.anchor_at(2).unwrap().nullifier_root);
        for size in 0..=3 {
            assert_eq!(
                w.history.nullifier_tree_at(size).root(),
                w.history.anchor_at(size).unwrap().nullifier_root,
            );
        }
    }

    #[test]
    fn replay_is_order_sensitive_so_wallets_must_agree_on_order() {
        let a = junk_copy(Fr::from(5u64), 1);
        let b = junk_copy(Fr::from(5u64), 2);
        assert_eq!(
            History::from_entries(&[a.clone(), b.clone()]).anchor_at(2),
            History::from_entries(&[a.clone(), b.clone()]).anchor_at(2),
        );
        assert_ne!(
            History::from_entries(&[a.clone(), b.clone()]).anchor_at(2),
            History::from_entries(&[b, a]).anchor_at(2),
        );
    }

    #[test]
    fn blind_replay_survives_adversarial_entries() {
        let empty = |nullifier| BoardEntry {
            ciphertext: vec![],
            ek_pk: [0; 32],
            key_encs: vec![],
            nullifiers: vec![nullifier],
            output_commitments: vec![],
            tags: vec![Fr::from(0u64)],
        };
        let sentinel_low = Fr::from(0u64);
        let sentinel_high = max_nullifier();
        let mut history = History::new();
        for nullifier in [sentinel_low, sentinel_high, sentinel_low, sentinel_high, Fr::from(5u64)] {
            history.append(&empty(nullifier));
        }

        let mut odd = empty(Fr::from(7u64));
        odd.nullifiers = vec![];
        history.append(&odd);
        odd.nullifiers = vec![Fr::from(8u64); MAX_INPUTS + 2];
        odd.tags = vec![];
        history.append(&odd);
        assert_eq!(history.opening(history.len() - 1).unwrap().inputs.len(), MAX_INPUTS);

        let tree = history.nullifier_tree_at(history.len());
        assert_eq!(tree.root(), history.anchor_at(history.len()).unwrap().nullifier_root);
        for member in [sentinel_low, sentinel_high, Fr::from(5u64)] {
            assert!(verify_occurrences(tree.root(), member, &tree.prove_occurrences(member).unwrap()));
        }
        let absent = Fr::from(6u64);
        assert!(verify_nonmembership(tree.root(), absent, &tree.prove_non_membership(absent)));
    }

    #[test]
    fn duplicate_insert_extends_the_chain_and_moves_the_root() {
        let sn = Fr::from(5u64);
        let first = LeafOpening::new(0, &junk_copy(sn, 1), Fr::from(0u64), Fr::from(0u64)).occurrence(0);
        let second = LeafOpening::new(0, &junk_copy(sn, 2), Fr::from(0u64), Fr::from(0u64)).occurrence(0);

        let mut tree = NullifierTree::new();
        let empty = tree.root();
        let w = tree.prove_non_membership(sn);
        assert!(verify_nonmembership(empty, sn, &w));
        assert!(tree.prove_occurrences(sn).is_none());

        let root1 = tree.insert(sn, &first);
        assert_ne!(root1, empty);
        let w1 = tree.prove_occurrences(sn).unwrap();
        assert_eq!(w1.occurrences, vec![first.clone()]);
        assert!(verify_occurrences(root1, sn, &w1));

        let root2 = tree.insert(sn, &second);
        assert_ne!(root2, root1, "a duplicate must not be a no-op any more");
        let w2 = tree.prove_occurrences(sn).unwrap();
        assert_eq!(w2.occurrences, vec![first.clone(), second.clone()]);
        assert!(verify_occurrences(root2, sn, &w2));

        assert!(!verify_nonmembership(root2, sn, &tree.prove_non_membership(sn)));

        for occurrences in [vec![second.clone()], vec![first.clone()], vec![second, first], vec![]] {
            let lying = WindowWitness { occurrences, ..w2.clone() };
            assert!(!verify_occurrences(root2, sn, &lying));
        }
        assert!(!verify_occurrences(root2, sn + Fr::from(1u64), &w2));
    }

    #[test]
    fn inserting_a_neighbour_keeps_a_chain_openable() {
        let sn = Fr::from(5u64);
        let occ = LeafOpening::new(0, &junk_copy(sn, 1), Fr::from(0u64), Fr::from(0u64)).occurrence(0);
        let mut tree = NullifierTree::new();
        tree.insert(sn, &occ);

        let root = tree.insert(Fr::from(6u64), &occ);
        assert_eq!(tree.prove_occurrences(sn).unwrap().occurrences, vec![occ]);
        assert!(verify_occurrences(root, sn, &tree.prove_occurrences(sn).unwrap()));
        let gap = Fr::from(1000u64);
        assert!(verify_nonmembership(root, gap, &tree.prove_non_membership(gap)));
    }

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        assert_eq!(w.receipt(slot, &alice).unwrap(), alice.pv);

        let bob = w.bob_spends_onward(slot, &alice).unwrap();
        let bob_slot = w.history.append(&bob.entry);
        assert_eq!(w.receipt(bob_slot, &bob).unwrap(), bob.pv);
    }

    #[test]
    fn unrelated_entries_landing_first_do_not_invalidate_a_proof() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&junk_copy(Fr::from(5u64), 1));
        w.history.append(&junk_copy(Fr::from(6u64), 2));
        let slot = w.history.append(&alice.entry);
        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    fn copied_serial_number_is_ignored() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        let slot = w.history.append(&alice.entry);

        w.receipt(slot, &alice).expect("Bob must accept despite the copy");
        let bob = w.bob_spends_onward(slot, &alice).expect("Bob must be able to spend despite the copy");
        let bob_slot = w.history.append(&bob.entry);
        w.receipt(bob_slot, &bob).unwrap();
    }

    #[test]
    fn copy_can_reuse_real_public_fields_and_still_is_just_junk() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();

        let mut copy = alice.entry.clone();
        copy.ciphertext = vec![1; 40];
        copy.output_commitments = vec![Fr::from(999u64)];
        w.history.append(&copy);
        let slot = w.history.append(&alice.entry);

        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    fn verbatim_replay_of_the_carrier_is_the_same_spend() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let first = w.history.append(&alice.entry);
        let second = w.history.append(&alice.entry);
        w.receipt(first, &alice).unwrap();
        w.receipt(second, &alice).unwrap();
        w.bob_spends_onward(second, &alice).unwrap();
    }

    #[test]
    fn anchor_after_a_copy_cannot_prove_freshness_but_the_original_can() {
        let mut w = world();
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        assert_eq!(
            w.alice_spends(&w.bob_coin, 2, 1).err(),
            Some("nullifier is already present at this anchor"),
        );
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        w.receipt(slot, &alice).unwrap();
    }

    #[test]
    fn honest_re_prove_is_the_same_spend() {
        let mut w = world();
        let first = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let second = w.alice_spends(&w.bob_coin, 1, 2).unwrap();
        assert_ne!(entry_ciphertext_commitment(&first.entry), entry_ciphertext_commitment(&second.entry));
        w.history.append(&first.entry);
        let slot = w.history.append(&second.entry);
        w.receipt(slot, &second).unwrap();
        w.bob_spends_onward(slot, &second).unwrap();
    }

    #[test]
    fn first_validly_tagged_spend_wins() {
        let mut w = world();
        let to_bob = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let to_carol = w.alice_spends(&w.carol_coin, 1, 2).unwrap();
        let bob_slot = w.history.append(&to_bob.entry);
        let carol_slot = w.history.append(&to_carol.entry);

        w.receipt(bob_slot, &to_bob).expect("first spend stands");
        assert_eq!(
            w.receipt(carol_slot, &to_carol).err(),
            Some("double-spend: a validly tagged spend of different outputs came first"),
        );

        w.bob_spends_onward(bob_slot, &to_bob).expect("first spend's coin stays spendable");

        let (carol_sk, _) = owner_party(3);
        let size = w.history.len();
        let parent = w.history.parent_witness(carol_slot, &to_carol.pv, size);
        let err = spend(&w.history, carol_sk, &w.carol_coin, &[coin(0xD1, 100, owner_party(4).1)], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent's window is not clean"));
    }

    #[test]
    fn spending_again_after_inclusion_fails_at_a_fresh_anchor() {
        let mut w = world();
        let to_bob = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&to_bob.entry);
        assert_eq!(
            w.alice_spends(&w.carol_coin, 2, 2).err(),
            Some("nullifier is already present at this anchor"),
        );
    }

    #[test]
    fn invalid_parent_tag_is_rejected() {
        let mut w = world();
        let mut alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        alice.entry.tags[0] = Fr::from(1u64);
        let slot = w.history.append(&alice.entry);

        assert_eq!(w.receipt(slot, &alice).err(), Some("carrier's tag does not verify under its tag key"));
        assert_eq!(w.bob_spends_onward(slot, &alice).err(), Some("parent's tag does not verify"));
    }

    #[test]
    fn fake_tag_key_is_rejected() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        let fake_tag_key = Fr::from(7u64);

        let mut lying_tx = alice.tx.clone();
        lying_tx.tag_keys = vec![fake_tag_key];
        assert_eq!(
            check_receipt(&w.history, slot, &alice.entry, &lying_tx, proof_ok).err(),
            Some("spend proof does not verify"),
        );

        let (bob_sk, _) = owner_party(2);
        let size = w.history.len();
        let mut parent = w.history.parent_witness(slot, &alice.pv, size);
        parent.public_values.tag_keys = vec![fake_tag_key];
        let err = spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent's tag does not verify"));
    }

    #[test]
    fn any_number_of_copies_is_tolerated() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        for i in 0..5 {
            w.history.append(&junk_copy(w.alice_nullifier(), i + 1));
        }
        let slot = w.history.append(&alice.entry);
        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    fn copies_after_the_carrier_do_not_count_against_it() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        for i in 0..3 {
            w.history.append(&junk_copy(w.alice_nullifier(), i as u8 + 1));
        }
        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    fn window_witness_must_match_the_state_before_the_parent() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let (bob_sk, _) = owner_party(2);
        let onward = |parent: &ParentWitness| {
            spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(parent), 3).err()
        };
        let parent = w.history.parent_witness(slot, &alice.pv, size);
        assert_eq!(onward(&parent), None);

        let mut hiding = parent.clone();
        hiding.windows[0] = w.history.nullifier_tree_at(1).prove_window(w.alice_nullifier());
        assert_eq!(onward(&hiding), Some("parent's window is not clean"));

        let mut dropping = parent;
        assert!(!dropping.windows[0].occurrences.is_empty());
        dropping.windows[0].occurrences.clear();
        assert_eq!(onward(&dropping), Some("parent's window is not clean"));
    }

    #[test]
    fn parent_anchor_must_be_real_and_precede_the_parent() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let (bob_sk, _) = owner_party(2);
        let onward = |parent: &ParentWitness| {
            spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(parent), 3).err()
        };

        let mut fake_root = w.history.parent_witness(slot, &alice.pv, size);
        fake_root.public_values.anchor.nullifier_root += Fr::from(1u64);
        assert_eq!(onward(&fake_root), Some("parent's anchor is not a real state preceding it"));

        let mut wrong_leaf = w.history.parent_witness(slot, &alice.pv, size);
        wrong_leaf.anchor_leaf = w.history.opening(0).unwrap().clone();
        wrong_leaf.anchor_leaf_path = w.history.board_path(0, size);
        assert_eq!(onward(&wrong_leaf), Some("parent's anchor is not a real state preceding it"));

        let later = junk_copy(Fr::from(5u64), 1);
        w.history.append(&later);
        let size = w.history.len();
        let mut parent = w.history.parent_witness(slot, &alice.pv, size);
        parent.public_values.anchor = w.history.anchor_at(2).unwrap();
        parent.anchor_leaf = w.history.opening(2).unwrap().clone();
        parent.anchor_leaf_path = w.history.board_path(2, size);
        let err = spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent's anchor is not a real state preceding it"));
    }

    #[test]
    fn parent_must_be_under_the_spends_anchor_and_create_the_coin() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let (bob_sk, _) = owner_party(2);

        let parent = w.history.parent_witness(slot, &alice.pv, size);
        let err = spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], slot, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent entry is not in this spend's anchor state"));

        let parent = w.history.parent_witness(slot, &alice.pv, size);
        let phantom = coin(0xEE, 100, owner_party(2).1);
        let err = spend(&w.history, bob_sk, &phantom, &[w.carol_coin.clone()], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent does not create the input coin"));
    }

    #[test]
    fn receipt_rejects_bad_anchor_proof_or_mismatched_carrier() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        const BAD_ANCHOR: &str = "anchor is not a real state preceding the carrier";

        let mut other_state = alice.tx.clone();
        other_state.anchor_size = 0;
        assert_eq!(
            check_receipt(&w.history, slot, &alice.entry, &other_state, proof_ok).err(),
            Some("spend proof does not verify"),
        );

        let mut after_carrier = alice.tx.clone();
        after_carrier.anchor_size = slot as u64 + 1;
        assert_eq!(check_receipt(&w.history, slot, &alice.entry, &after_carrier, proof_ok).err(), Some(BAD_ANCHOR));
        let mut beyond_history = alice.tx.clone();
        beyond_history.anchor_size = 99;
        assert_eq!(check_receipt(&w.history, slot, &alice.entry, &beyond_history, proof_ok).err(), Some(BAD_ANCHOR));

        assert_eq!(
            check_receipt(&w.history, slot, &alice.entry, &alice.tx, |_, _| false).err(),
            Some("spend proof does not verify"),
        );

        assert_eq!(
            check_receipt(&w.history, 0, &alice.entry, &alice.tx, proof_ok).err(),
            Some("carrier does not match this history's entry at that slot"),
        );
        assert_eq!(
            check_receipt(&w.history, 9, &alice.entry, &alice.tx, proof_ok).err(),
            Some("carrier's slot is not in this history"),
        );
    }

    #[test]
    fn rejects_wrong_secret_key() {
        let w = world();
        let (mallory_sk, _) = owner_party(5);
        let parent = w.parent_is_genesis(1);
        let err = spend(&w.history, mallory_sk, &w.alice_coin, &[w.bob_coin.clone()], 1, Some(&parent), 1);
        assert_eq!(err.err(), Some("input coin's owner does not match the spender"));
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let w = world();
        let err = spend(&w.history, w.alice_sk, &w.alice_coin, &[w.bob_coin.clone()], 1, None, 1);
        assert_eq!(err.err(), Some("only the genesis key may mint without provenance"));
    }

    #[test]
    fn rejects_a_phantom_commitment_in_an_unused_output_slot() {
        let w = world();
        let anchor = w.history.anchor_at(1).unwrap();
        let commitment = w.alice_coin.commitment();
        let nonmembership = w.history.nullifier_tree_at(1).prove_non_membership(w.alice_nullifier());
        let parent = w.parent_is_genesis(1);
        let check = |padding: Fr| {
            check_spend(
                &w.alice_sk,
                std::slice::from_ref(&w.alice_coin),
                std::slice::from_ref(&w.bob_coin),
                &[w.bob_coin.commitment(), padding],
                &anchor,
                std::slice::from_ref(&nonmembership),
                std::slice::from_ref(&parent),
            )
        };
        assert!(check(Fr::from(0u64)).is_ok());
        assert_eq!(check(commitment).err(), Some("unused output slots must hold a zero commitment"));
    }

    #[cfg(feature = "two-inputs")]
    struct TwoCoins {
        w: World,
        second_mint: Spend,
        second_coin: Coin,
    }

    #[cfg(feature = "two-inputs")]
    impl TwoCoins {
        fn new() -> Self {
            let mut w = world();
            let second_coin = coin(0xA3, 50, owner_party(1).1);
            let second_mint =
                spend(&w.history, genesis_sk(), &coin(0xA4, 50, genesis_pk()), &[second_coin.clone()], 1, None, 50)
                    .unwrap();
            w.history.append(&second_mint.entry);
            Self { w, second_mint, second_coin }
        }

        fn second_nullifier(&self) -> Fr {
            derive_nullifier(self.second_coin.commitment(), &self.w.alice_sk)
        }

        fn alice_spends_both(&self, output: &Coin, anchor_size: usize, id: u64) -> Result<Spend, &'static str> {
            let h = &self.w.history;
            let parents = [
                h.parent_witness(0, &self.w.genesis.pv, anchor_size),
                h.parent_witness(1, &self.second_mint.pv, anchor_size),
            ];
            let inputs = [self.w.alice_coin.clone(), self.second_coin.clone()];
            spend_inputs(h, self.w.alice_sk, &inputs, std::slice::from_ref(output), anchor_size, &parents, id)
        }

        fn bob_coin(&self) -> Coin {
            coin(0xB1, 150, owner_party(2).1)
        }

        fn bob_spends_onward(&self, slot: usize, carrier: &Spend) -> Result<Spend, &'static str> {
            let size = self.w.history.len();
            let parent = self.w.history.parent_witness(slot, &carrier.pv, size);
            let to_carol = coin(0xC1, 150, owner_party(3).1);
            spend(&self.w.history, owner_party(2).0, &self.bob_coin(), &[to_carol], size, Some(&parent), 100)
        }
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn two_input_spend_is_valid_end_to_end() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        assert_eq!(alice.entry.nullifiers.len(), 2);
        assert_eq!(alice.entry.tags.len(), 2);
        let slot = t.w.history.append(&alice.entry);
        assert_eq!(check_receipt(&t.w.history, slot, &alice.entry, &alice.tx, proof_ok).unwrap(), alice.pv);
        let bob = t.bob_spends_onward(slot, &alice).unwrap();
        let bob_slot = t.w.history.append(&bob.entry);
        check_receipt(&t.w.history, bob_slot, &bob.entry, &bob.tx, proof_ok).unwrap();
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn the_same_coin_twice_is_rejected() {
        let w = world();
        let parent = w.parent_is_genesis(1);
        let inputs = [w.alice_coin.clone(), w.alice_coin.clone()];
        let err = spend_inputs(&w.history, w.alice_sk, &inputs, &[coin(0xB1, 200, owner_party(2).1)], 1, &[parent.clone(), parent], 1);
        assert_eq!(err.err(), Some("a spend cannot consume the same coin twice"));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn every_input_needs_its_own_parent() {
        let t = TwoCoins::new();
        let h = &t.w.history;
        let only_one = [h.parent_witness(0, &t.w.genesis.pv, 2)];
        let inputs = [t.w.alice_coin.clone(), t.second_coin.clone()];
        let err = spend_inputs(h, t.w.alice_sk, &inputs, &[t.bob_coin()], 2, &only_one, 1);
        assert_eq!(err.err(), Some("every input needs its own parent"));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn double_spend_of_the_second_input_is_caught() {
        let mut t = TwoCoins::new();

        let both = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        let parent = t.w.history.parent_witness(1, &t.second_mint.pv, 2);
        let second_alone =
            spend(&t.w.history, t.w.alice_sk, &t.second_coin, &[coin(0xC2, 50, owner_party(3).1)], 2, Some(&parent), 2)
                .unwrap();
        t.w.history.append(&second_alone.entry);
        let slot = t.w.history.append(&both.entry);

        assert_eq!(
            check_receipt(&t.w.history, slot, &both.entry, &both.tx, proof_ok).err(),
            Some("double-spend: a validly tagged spend of different outputs came first"),
        );
        assert_eq!(t.bob_spends_onward(slot, &both).err(), Some("parent's window is not clean"));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn copies_of_the_second_inputs_serial_number_are_ignored() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        for seed in 0..3 {
            t.w.history.append(&junk_copy(t.second_nullifier(), seed + 1));
        }
        let slot = t.w.history.append(&alice.entry);
        check_receipt(&t.w.history, slot, &alice.entry, &alice.tx, proof_ok).unwrap();
        let bob = t.bob_spends_onward(slot, &alice).unwrap();
        let bob_slot = t.w.history.append(&bob.entry);
        check_receipt(&t.w.history, bob_slot, &bob.entry, &bob.tx, proof_ok).unwrap();
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn a_carrier_with_an_input_dropped_is_no_parent() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        let mut truncated = alice.entry.clone();
        truncated.nullifiers.truncate(1);
        truncated.tags.truncate(1);
        let copy_slot = t.w.history.append(&truncated);
        let slot = t.w.history.append(&alice.entry);

        assert_eq!(
            check_receipt(&t.w.history, copy_slot, &truncated, &alice.tx, proof_ok).err(),
            Some("carrier must have one key per posted input"),
        );
        assert_eq!(t.bob_spends_onward(copy_slot, &alice).err(), Some("parent proof disagrees with the parent entry"));
        check_receipt(&t.w.history, slot, &alice.entry, &alice.tx, proof_ok).unwrap();
        t.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn parent_witness_must_cover_every_parent_input() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        let slot = t.w.history.append(&alice.entry);
        let size = t.w.history.len();
        let onward = |parent: &ParentWitness| {
            let to_carol = coin(0xC1, 150, owner_party(3).1);
            spend(&t.w.history, owner_party(2).0, &t.bob_coin(), &[to_carol], size, Some(parent), 3).err()
        };
        let parent = t.w.history.parent_witness(slot, &alice.pv, size);

        let mut one_key = parent.clone();
        one_key.public_values.tag_keys.truncate(1);
        assert_eq!(onward(&one_key), Some("parent needs one tag key and one window per parent input"));

        let mut swapped = parent.clone();
        swapped.public_values.tag_keys.swap(0, 1);
        assert_eq!(onward(&swapped), Some("parent's tag does not verify"));

        let mut one_input = parent;
        one_input.public_values.nullifiers.truncate(1);
        assert_eq!(onward(&one_input), Some("parent proof disagrees with the parent entry"));
    }

    #[test]
    fn rejects_value_conservation_violation() {
        let w = world();
        let too_much = coin(0xB1, 101, owner_party(2).1);
        assert_eq!(
            w.alice_spends(&too_much, 1, 1).err(),
            Some("transaction violates value conservation: sum(inputs) must equal sum(outputs)"),
        );
    }

    #[test]
    fn nullifier_tree_insert_cost_does_not_grow_with_tree_size() {

        fn value(i: u32) -> Fr {
            Fr::from(i as u64 + 1)
        }
        let occ = LeafOpening::new(0, &junk_copy(value(0), 1), Fr::from(0u64), Fr::from(0u64)).occurrence(0);

        let mut tree = NullifierTree::new();
        let batch = 500u32;
        let t = std::time::Instant::now();
        for i in 0..batch {
            tree.insert(value(i), &occ);
        }
        let small_per_insert = t.elapsed() / batch;

        for i in batch..(batch * 8) {
            tree.insert(value(i), &occ);
        }
        let t = std::time::Instant::now();
        for i in (batch * 8)..(batch * 9) {
            tree.insert(value(i), &occ);
        }
        let large_per_insert = t.elapsed() / batch;

        assert!(
            large_per_insert.as_secs_f64() < small_per_insert.as_secs_f64() * 4.0 + 0.001,
            "insert cost grew from {small_per_insert:?}/insert at a small tree size to \
             {large_per_insert:?}/insert at 8x the size — looks non-incremental"
        );

        let absent = Fr::from(u64::MAX);
        let witness = tree.prove_non_membership(absent);
        assert!(verify_nonmembership(tree.root(), absent, &witness));

        let member = value(batch * 8);
        let w = tree.prove_non_membership(member);
        assert!(!verify_nonmembership(tree.root(), member, &w));
    }
}
