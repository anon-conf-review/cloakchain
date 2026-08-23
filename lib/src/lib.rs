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
    let elems: Vec<Fr> = bytes.chunks(31).map(Fr::from_le_bytes_mod_order).collect();
    poseidon_hash(&elems)
}

pub fn fold_owner_scalar(sk: &OwnerScalar) -> Fr {
    fold_bits_le(&sk.into_bigint().to_bits_le())
}

fn fold_bits_le(bits: &[bool]) -> Fr {
    let chunks: Vec<Fr> = bits
        .chunks(248)
        .map(|chunk| {
            let mut acc = Fr::from(0u64);
            let mut place = Fr::from(1u64);
            for &b in chunk {
                if b {
                    acc += place;
                }
                place *= Fr::from(2u64);
            }
            acc
        })
        .collect();
    poseidon_hash(&chunks)
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

#[derive(
    Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize,
)]
pub struct Coin {
    pub value: u64,
    #[serde(with = "field_serde")]
    pub rand: Fr,
    #[serde(with = "field_serde")]
    pub owner_pk: OwnerPk,
}

impl Coin {
    pub fn commitment(&self) -> Fr {
        let (px, py) = owner_pk_to_field_pair(&self.owner_pk);
        poseidon_hash(&[Fr::from(self.value), self.rand, px, py])
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    pub id: u64,
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    pub note_encs: Vec<Vec<u8>>,
    pub spend_proof: Vec<u8>,
}

impl Transaction {
    pub fn receives_coin(&self, cn: &Fr) -> bool {
        self.output_commitments.contains(cn)
    }
}

const MAGIC_TAG: [u8; 8] = *b"CLOAKTX1";
const NOTE_MAGIC: [u8; 8] = *b"CLOAKNT1";
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
    pub nullifier: Fr,
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
}

pub fn encrypt_tx(
    tx: &Transaction,
    input_commitment: Fr,
    sender_sk: &OwnerScalar,
    recipient_pks: &[[u8; 32]],
    session_key: [u8; 32],
) -> BoardEntry {
    let ek_sk = ek_secret(&session_key);
    let ek_pk = *X25519PublicKey::from(&ek_sk).as_bytes();

    let tx_bytes = bincode::serialize(tx).expect("Transaction is always serializable");
    let mut plaintext = MAGIC_TAG.to_vec();
    plaintext.extend_from_slice(&tx_bytes);
    let ciphertext = xor_with_keystream(&session_key, &plaintext);

    let key_encs = recipient_pks
        .iter()
        .map(|rpk| {
            let recipient_pub = X25519PublicKey::from(*rpk);
            let shared = *ek_sk.diffie_hellman(&recipient_pub).as_bytes();
            let wk = wrapping_key(&shared);
            let mut enc = [0u8; 32];
            for (e, (w, s)) in enc.iter_mut().zip(wk.iter().zip(session_key.iter())) {
                *e = w ^ s;
            }
            enc
        })
        .collect();

    let nullifier = poseidon_hash(&[input_commitment, fold_owner_scalar(sender_sk)]);

    BoardEntry {
        ciphertext,
        ek_pk,
        key_encs,
        nullifier,
        output_commitments: tx.output_commitments.clone(),
    }
}

pub fn scan_entry(owner_sk: &[u8; 32], entry: &BoardEntry) -> Option<Transaction> {
    let owner_secret = X25519Secret::from(*owner_sk);
    let ek_pub = X25519PublicKey::from(entry.ek_pk);
    let shared = *owner_secret.diffie_hellman(&ek_pub).as_bytes();
    let wk = wrapping_key(&shared);

    for key_enc in &entry.key_encs {
        let mut session_key = [0u8; 32];
        for (s, (w, e)) in session_key.iter_mut().zip(wk.iter().zip(key_enc.iter())) {
            *s = w ^ e;
        }
        if entry.ciphertext.len() <= 8 {
            continue;
        }
        let tx_bytes = xor_with_keystream(&session_key, &entry.ciphertext);
        if tx_bytes[..8] != MAGIC_TAG {
            continue;
        }
        if let Ok(tx) = bincode::deserialize::<Transaction>(&tx_bytes[8..]) {
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

pub fn build_note_enc(session_key: &[u8; 32], index: usize, coin: &Coin) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(session_key);
    h.update((index as u64).to_le_bytes());
    h.update(NOTE_SALT);
    let mut note_key = [0u8; 32];
    note_key.copy_from_slice(&h.finalize());
    let coin_bytes = bincode::serialize(coin).expect("Coin is always serializable");
    let mut payload = NOTE_MAGIC.to_vec();
    payload.extend_from_slice(&coin_bytes);
    xor_with_keystream(&note_key, &payload)
}

pub fn decrypt_note(session_key: &[u8; 32], index: usize, note_enc: &[u8]) -> Option<Coin> {
    let mut h = Sha256::new();
    h.update(session_key);
    h.update((index as u64).to_le_bytes());
    h.update(NOTE_SALT);
    let mut note_key = [0u8; 32];
    note_key.copy_from_slice(&h.finalize());
    let dec = xor_with_keystream(&note_key, note_enc);
    if dec.len() <= 8 || dec[..8] != NOTE_MAGIC {
        return None;
    }
    bincode::deserialize(&dec[8..]).ok()
}

pub const TREE_DEPTH: usize = 32;

pub fn merkle_leaf(slot: usize, entry: &BoardEntry) -> Fr {
    merkle_leaf_from_commitment(
        slot,
        entry.nullifier,
        &entry.output_commitments,
        entry_ciphertext_commitment(entry),
    )
}

pub fn entry_ciphertext_commitment(entry: &BoardEntry) -> Fr {
    let key_encs_bytes: Vec<u8> = entry.key_encs.iter().flatten().copied().collect();
    poseidon_hash(&[
        poseidon_hash_bytes(&entry.ciphertext),
        poseidon_hash_bytes(&entry.ek_pk),
        poseidon_hash_bytes(&key_encs_bytes),
    ])
}

pub fn merkle_leaf_from_commitment(
    slot: usize,
    nullifier: Fr,
    output_commitments: &[Fr],
    ciphertext_commitment: Fr,
) -> Fr {
    poseidon_hash(&[
        Fr::from(slot as u64),
        ciphertext_commitment,
        nullifier,
        poseidon_hash(output_commitments),
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

pub fn merkle_root_of(entries: &[BoardEntry]) -> Fr {
    if entries.is_empty() {
        return empty_root();
    }
    let last = entries.len() - 1;
    let path = append_proof_for(entries);
    compute_root_from_path(merkle_leaf(last, &entries[last]), last, &path)
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
            let right = if i + 1 < level.len() {
                level[i + 1]
            } else {
                zeros[d]
            };
            next.push(merkle_combine(&left, &right));
            i += 2;
        }
        level = next;
        idx >>= 1;
    }
    path
}

pub fn append_proof_for(entries: &[BoardEntry]) -> Vec<Fr> {
    let slot = entries.len() - 1;
    let hashes: Vec<Fr> = entries
        .iter()
        .enumerate()
        .map(|(i, e)| merkle_leaf(i, e))
        .collect();
    merkle_path_for_index(&hashes, slot)
}

pub fn append_path_for_next(entries: &[BoardEntry]) -> Vec<Fr> {
    let hashes: Vec<Fr> = entries
        .iter()
        .enumerate()
        .map(|(i, e)| merkle_leaf(i, e))
        .collect();
    merkle_path_for_index(&hashes, entries.len())
}

pub fn merkle_verify(root: Fr, slot: usize, entry: &BoardEntry, proof: &[Fr]) -> bool {
    compute_root_from_path(merkle_leaf(slot, entry), slot, proof) == root
}

#[derive(
    Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize,
)]
pub struct IndexedLeaf {
    #[serde(with = "field_serde")]
    pub value: Fr,
    #[serde(with = "field_serde")]
    pub next_value: Fr,
    pub next_index: u64,
}

fn max_nullifier() -> Fr {
    -Fr::from(1u64)
}

impl IndexedLeaf {
    fn hash(&self) -> Fr {
        poseidon_hash(&[self.value, self.next_value, Fr::from(self.next_index)])
    }
}

#[derive(
    Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize,
)]
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
    compute_root_from_path(
        leaf_hash,
        witness.low_leaf_index as usize,
        &witness.sibling_path,
    ) == root
}

#[derive(Clone, Debug)]
pub struct NullifierTree {
    leaves: Vec<IndexedLeaf>,
    index_of: BTreeMap<Fr, usize>,
    nodes: Vec<HashMap<usize, Fr>>,
}

impl NullifierTree {
    pub fn new() -> Self {
        let sentinel = IndexedLeaf {
            value: Fr::from(0u64),
            next_value: max_nullifier(),
            next_index: 0,
        };
        let mut tree = Self {
            leaves: vec![sentinel.clone()],
            index_of: BTreeMap::new(),
            nodes: vec![HashMap::new(); TREE_DEPTH + 1],
        };
        tree.index_of.insert(sentinel.value, 0);
        tree.set_leaf(0, sentinel.hash());
        tree
    }

    fn set_leaf(&mut self, idx: usize, hash: Fr) {
        let zeros = zero_hashes();
        let mut cur_idx = idx;
        let mut cur_hash = hash;
        for d in 0..TREE_DEPTH {
            self.nodes[d].insert(cur_idx, cur_hash);
            let sibling_idx = cur_idx ^ 1;
            let sibling = self.nodes[d].get(&sibling_idx).copied().unwrap_or(zeros[d]);
            cur_hash = if cur_idx % 2 == 0 {
                merkle_combine(&cur_hash, &sibling)
            } else {
                merkle_combine(&sibling, &cur_hash)
            };
            cur_idx >>= 1;
        }
        self.nodes[TREE_DEPTH].insert(cur_idx, cur_hash);
    }

    pub fn root(&self) -> Fr {
        self.nodes[TREE_DEPTH]
            .get(&0)
            .copied()
            .unwrap_or_else(|| zero_hashes()[TREE_DEPTH])
    }

    pub fn contains(&self, value: Fr) -> bool {
        self.index_of.contains_key(&value)
    }

    fn find_low_leaf_index(&self, target: Fr) -> usize {
        *self
            .index_of
            .range(..target)
            .next_back()
            .map(|(_, idx)| idx)
            .expect("no matching leaf — target is 0 or tree invariant violated")
    }

    pub fn insert(&mut self, value: Fr) -> Fr {
        if self.contains(value) {
            return self.root();
        }
        let low_idx = self.find_low_leaf_index(value);
        let low = self.leaves[low_idx].clone();
        let new_index = self.leaves.len();
        let updated_low = IndexedLeaf {
            value: low.value,
            next_value: value,
            next_index: new_index as u64,
        };
        let new_leaf = IndexedLeaf {
            value,
            next_value: low.next_value,
            next_index: low.next_index,
        };

        self.leaves[low_idx] = updated_low.clone();
        self.leaves.push(new_leaf.clone());
        self.index_of.insert(value, new_index);

        self.set_leaf(low_idx, updated_low.hash());
        self.set_leaf(new_index, new_leaf.hash());
        self.root()
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

    pub fn prove_non_membership(&self, target: Fr) -> NonMembershipWitness {
        let low_idx = self.find_low_leaf_index(target);
        NonMembershipWitness {
            low_leaf: self.leaves[low_idx].clone(),
            low_leaf_index: low_idx as u64,
            sibling_path: self.path_for(low_idx),
        }
    }

    pub fn replay(inserted: &[Fr], count: usize) -> Self {
        let mut tree = Self::new();
        for &n in &inserted[..count] {
            tree.insert(n);
        }
        tree
    }
}

impl Default for NullifierTree {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidPublicValues {
    pub vkey: [u32; 8],
    #[serde(with = "field_serde")]
    pub board_root: Fr,
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    #[serde(with = "field_serde")]
    pub nullifier_root: Fr,
}

impl ValidPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("ValidPublicValues is always serializable")
    }
}

pub fn check_coin_receipt(
    vkey: [u32; 8],
    owner_pk: OwnerPk,
    coin_commitment: Fr,
    entry_k: BoardEntry,
    received_slot: usize,
    append_path: Vec<Fr>,
    parent_nonmembership: NonMembershipWitness,
    nullifier_root_at_parent_slot: Fr,
    spend_pv: ValidPublicValues,
) -> Result<CoinReceiptPublicValues, &'static str> {
    if !verify_nonmembership(
        nullifier_root_at_parent_slot,
        entry_k.nullifier,
        &parent_nonmembership,
    ) {
        return Err("parent transaction's nullifier was already present on the board — it was a double-spend");
    }

    let leaf_k = merkle_leaf(received_slot, &entry_k);
    let board_root = compute_root_from_path(leaf_k, received_slot, &append_path);

    if !entry_k.output_commitments.contains(&coin_commitment) {
        return Err("entry_k does not create coin_commitment");
    }
    if !spend_pv.output_commitments.contains(&coin_commitment) {
        return Err("parent spend proof does not commit to this coin commitment");
    }

    Ok(CoinReceiptPublicValues {
        vkey,
        owner_pk,
        coin_commitment,
        board_root,
        received_at: received_slot as u64,
    })
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CoinReceiptPublicValues {
    pub vkey: [u32; 8],
    #[serde(with = "field_serde")]
    pub owner_pk: OwnerPk,
    #[serde(with = "field_serde")]
    pub coin_commitment: Fr,
    #[serde(with = "field_serde")]
    pub board_root: Fr,
    pub received_at: u64,
}

impl CoinReceiptPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("CoinReceiptPublicValues is always serializable")
    }
}

pub fn check_spend(
    vkey: [u32; 8],
    coin_proof_vkey: [u32; 8],
    sk_p: OwnerScalar,
    pk_p: OwnerPk,
    coin_commitment: Fr,
    entry_position: usize,
    append_path: Vec<Fr>,
    tx_star: Transaction,
    input_coins: Vec<Coin>,
    output_coins: Vec<Coin>,
    is_genesis: bool,
    coin_proof: Option<CoinReceiptPublicValues>,
    own_nullifier_nonmembership: NonMembershipWitness,
    current_nullifier_root: Fr,
) -> Result<ValidPublicValues, &'static str> {
    if derive_owner_pk(&sk_p) != pk_p {
        return Err("pk_P must be the public key for sk_P");
    }

    let board_root = compute_root_from_path(Fr::from(0u64), entry_position, &append_path);

    let own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&sk_p)]);

    if !verify_nonmembership(
        current_nullifier_root,
        own_nullifier,
        &own_nullifier_nonmembership,
    ) {
        return Err("P must not have spent this coin before (double spend)");
    }

    for coin in input_coins.iter() {
        if coin.owner_pk != pk_p {
            return Err("input coin's owner does not match the spender");
        }
    }

    if !input_coins
        .iter()
        .any(|c| c.commitment() == coin_commitment)
    {
        return Err("tx* does not spend the claimed coin");
    }

    if output_coins.len() != tx_star.output_commitments.len() {
        return Err("output_coins length does not match tx* output_commitments");
    }
    for (coin, cn) in output_coins.iter().zip(tx_star.output_commitments.iter()) {
        if &coin.commitment() != cn {
            return Err("output coin commitment does not match tx*");
        }
    }

    let total_in: u64 = input_coins.iter().map(|c| c.value).sum();
    let total_out: u64 = output_coins.iter().map(|c| c.value).sum();
    if total_in != total_out {
        return Err("transaction violates value conservation: sum(inputs) must equal sum(outputs)");
    }

    if is_genesis {
        if pk_p != genesis_pk() {
            return Err("only the genesis key may mint without provenance");
        }
    } else {
        let cp = coin_proof.ok_or("non-genesis spends require a coin-proof")?;
        if cp.vkey != coin_proof_vkey {
            return Err("coin-proof was produced under an unexpected vkey");
        }
        if cp.owner_pk != pk_p {
            return Err("coin-proof owner must be P");
        }
        if cp.coin_commitment != coin_commitment {
            return Err("coin-proof tracks a different coin");
        }
    }

    Ok(ValidPublicValues {
        vkey,
        board_root,
        output_commitments: tx_star.output_commitments.clone(),
        nullifier_root: current_nullifier_root,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_VKEY: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    const TEST_COIN_PROOF_VKEY: [u32; 8] = [9, 9, 9, 9, 9, 9, 9, 9];

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
        Coin {
            value,
            rand: Fr::from(seed as u64 + 1000),
            owner_pk,
        }
    }

    fn make_tx(
        id: u64,
        _sender_sk: OwnerScalar,
        sender_enc_sk: [u8; 32],
        _input_coins: &[Coin],
        outputs: &[(Coin, OwnerPk, [u8; 32])],
    ) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
        let recipient_enc_pks: Vec<[u8; 32]> = outputs.iter().map(|(_, _, rpk)| *rpk).collect();
        let output_commitments: Vec<Fr> = outputs.iter().map(|(c, _, _)| c.commitment()).collect();
        let session_key = {
            let mut h = Sha256::new();
            h.update(sender_enc_sk);
            h.update(id.to_le_bytes());
            h.update(EK_SALT);
            let mut out = [0u8; 32];
            out.copy_from_slice(&h.finalize());
            out
        };
        let note_encs: Vec<Vec<u8>> = outputs
            .iter()
            .enumerate()
            .map(|(i, (c, _, _))| build_note_enc(&session_key, i, c))
            .collect();
        let tx = Transaction {
            id,
            output_commitments,
            note_encs,
            spend_proof: vec![],
        };
        (tx, session_key, recipient_enc_pks)
    }

    fn enc(
        tx: &Transaction,
        input_commitment: Fr,
        sender_sk: &OwnerScalar,
        recipient_enc_pks: &[[u8; 32]],
        session_key: [u8; 32],
    ) -> BoardEntry {
        encrypt_tx(
            tx,
            input_commitment,
            sender_sk,
            recipient_enc_pks,
            session_key,
        )
    }

    fn make_receipt(
        owner_pk: OwnerPk,
        coin_commitment: Fr,
        entries: &[BoardEntry],
        received_slot: usize,
        spend_pv: ValidPublicValues,
    ) -> Result<CoinReceiptPublicValues, &'static str> {
        let ap = append_proof_for(&entries[..=received_slot]);
        let all_nullifiers: Vec<Fr> = entries.iter().map(|e| e.nullifier).collect();
        let tree = NullifierTree::replay(&all_nullifiers, received_slot);
        let parent_root = tree.root();
        let parent_witness = tree.prove_non_membership(entries[received_slot].nullifier);
        check_coin_receipt(
            TEST_COIN_PROOF_VKEY,
            owner_pk,
            coin_commitment,
            entries[received_slot].clone(),
            received_slot,
            ap,
            parent_witness,
            parent_root,
            spend_pv,
        )
    }

    fn spend(
        sk: OwnerScalar,
        pk: OwnerPk,
        coin_commitment: Fr,
        prior_entries: &[BoardEntry],
        tx_star: &Transaction,
        input_coins: &[Coin],
        output_coins: &[Coin],
        is_genesis: bool,
        coin_proof: Option<CoinReceiptPublicValues>,
    ) -> Result<ValidPublicValues, &'static str> {
        let ap = append_path_for_next(prior_entries);
        let all_nullifiers: Vec<Fr> = prior_entries.iter().map(|e| e.nullifier).collect();
        let tree = NullifierTree::replay(&all_nullifiers, prior_entries.len());
        let own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&sk)]);
        let witness = tree.prove_non_membership(own_nullifier);
        let root = tree.root();
        check_spend(
            TEST_VKEY,
            TEST_COIN_PROOF_VKEY,
            sk,
            pk,
            coin_commitment,
            prior_entries.len(),
            ap,
            tx_star.clone(),
            input_coins.to_vec(),
            output_coins.to_vec(),
            is_genesis,
            coin_proof,
            witness,
            root,
        )
    }

    #[test]
    fn encrypt_decrypt_round_trips_for_participants_and_rejects_outsiders() {
        let (alice_enc_sk, alice_enc_pk) = enc_party(1);
        let (bob_enc_sk, _) = enc_party(2);
        let (carol_enc_sk, _) = enc_party(3);
        let (_, alice_pk) = owner_party(1);

        let alice_coin = coin(0xA2, 100, alice_pk);
        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let (tx0, sk0, r0) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk, alice_enc_pk)],
        );
        let entry = enc(&tx0, genesis_coin.commitment(), &genesis_sk(), &r0, sk0);

        assert_eq!(scan_entry(&alice_enc_sk, &entry), Some(tx0.clone()));
        assert_eq!(scan_entry(&bob_enc_sk, &entry), None);
        assert_eq!(scan_entry(&carol_enc_sk, &entry), None);

        assert_eq!(decrypt_note(&sk0, 0, &tx0.note_encs[0]), Some(alice_coin));
        assert_eq!(decrypt_note(&sk0, 1, &tx0.note_encs[0]), None);
    }

    #[test]
    fn multi_output_tx_each_recipient_sees_only_own_note() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let (_, bob_enc_pk) = enc_party(2);
        let (_, alice_enc_pk) = enc_party(1);

        let alice_coin = coin(0xA1, 100, alice_pk);
        let bob_coin = coin(0xB1, 40, bob_pk);
        let alice_change = coin(0xB2, 60, alice_pk);

        let (tx1, sk1, _) = make_tx(
            1,
            alice_sk,
            [0u8; 32],
            &[alice_coin],
            &[
                (bob_coin.clone(), bob_pk, bob_enc_pk),
                (alice_change.clone(), alice_pk, alice_enc_pk),
            ],
        );

        assert_eq!(decrypt_note(&sk1, 0, &tx1.note_encs[0]), Some(bob_coin));
        assert_eq!(decrypt_note(&sk1, 1, &tx1.note_encs[1]), Some(alice_change));
        assert_eq!(decrypt_note(&sk1, 1, &tx1.note_encs[0]), None);
        assert_eq!(decrypt_note(&sk1, 0, &tx1.note_encs[1]), None);
    }

    #[test]
    fn scan_entry_finds_recipient_but_not_outsiders() {
        let (alice_enc_sk, alice_enc_pk) = enc_party(1);
        let (bob_enc_sk, _) = enc_party(2);
        let (carol_enc_sk, _) = enc_party(3);
        let (_, alice_pk) = owner_party(1);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let (tx0, sk0, r0) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(coin(0xA2, 100, alice_pk), alice_pk, alice_enc_pk)],
        );
        let entry = enc(&tx0, genesis_coin.commitment(), &genesis_sk(), &r0, sk0);

        assert_eq!(scan_entry(&alice_enc_sk, &entry), Some(tx0.clone()));
        assert_eq!(scan_entry(&bob_enc_sk, &entry), None);
        assert_eq!(scan_entry(&carol_enc_sk, &entry), None);
    }

    struct Chain {
        entries: Vec<BoardEntry>,
        tx0: Transaction,
        tx1: Transaction,
        tx2: Transaction,
        alice_coin: Coin,
        bob_coin: Coin,
        alice_change: Coin,
        carol_coin: Coin,
        genesis_coin: Coin,
        alice_sk: OwnerScalar,
        alice_pk: OwnerPk,
        bob_sk: OwnerScalar,
        bob_pk: OwnerPk,
        carol_pk: OwnerPk,
        pv0: ValidPublicValues,
    }

    fn build_chain() -> Chain {
        let (alice_sk, alice_pk) = owner_party(1);
        let (bob_sk, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);
        let (_, alice_enc_pk) = enc_party(1);
        let (_, bob_enc_pk) = enc_party(2);
        let (_, carol_enc_pk) = enc_party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin = coin(0xA2, 100, alice_pk);
        let bob_coin = coin(0xB1, 40, bob_pk);
        let alice_change = coin(0xB2, 60, alice_pk);
        let carol_coin = coin(0xC1, 40, carol_pk);

        let (tx0, sk0, r0) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk, alice_enc_pk)],
        );
        let (tx1, sk1, r1) = make_tx(
            1,
            alice_sk,
            [0u8; 32],
            &[alice_coin.clone()],
            &[
                (bob_coin.clone(), bob_pk, bob_enc_pk),
                (alice_change.clone(), alice_pk, alice_enc_pk),
            ],
        );
        let (tx2, sk2, r2) = make_tx(
            2,
            bob_sk,
            [0u8; 32],
            &[bob_coin.clone()],
            &[(carol_coin.clone(), carol_pk, carol_enc_pk)],
        );
        let entries = vec![
            enc(&tx0, genesis_coin.commitment(), &genesis_sk(), &r0, sk0),
            enc(&tx1, alice_coin.commitment(), &alice_sk, &r1, sk1),
            enc(&tx2, bob_coin.commitment(), &bob_sk, &r2, sk2),
        ];

        let pv0 = spend(
            genesis_sk(),
            genesis_pk(),
            genesis_coin.commitment(),
            &[],
            &tx0,
            &[genesis_coin.clone()],
            &[alice_coin.clone()],
            true,
            None,
        )
        .unwrap();

        Chain {
            entries,
            tx0,
            tx1,
            tx2,
            alice_coin,
            bob_coin,
            alice_change,
            carol_coin,
            genesis_coin,
            alice_sk,
            alice_pk,
            bob_sk,
            bob_pk,
            carol_pk,
            pv0,
        }
    }

    #[test]
    fn receipt_tracks_correct_received_slot() {
        let c = build_chain();
        let cn_alice = c.alice_coin.commitment();
        let cn_bob = c.bob_coin.commitment();

        let alice_receipt =
            make_receipt(c.alice_pk, cn_alice, &c.entries, 0, c.pv0.clone()).unwrap();
        assert_eq!(alice_receipt.received_at, 0);

        let alice_spend_pv = spend(
            c.alice_sk,
            c.alice_pk,
            cn_alice,
            &c.entries[..1],
            &c.tx1,
            &[c.alice_coin.clone()],
            &[c.bob_coin.clone(), c.alice_change.clone()],
            false,
            Some(alice_receipt),
        )
        .unwrap();

        let bob_receipt = make_receipt(c.bob_pk, cn_bob, &c.entries, 1, alice_spend_pv).unwrap();
        assert_eq!(bob_receipt.received_at, 1);
        let _ = c.tx2;
    }

    #[test]
    fn coin_proof_tracks_change_as_a_receipt() {
        let c = build_chain();
        let cn_change = c.alice_change.commitment();

        let alice_receipt = make_receipt(
            c.alice_pk,
            c.alice_coin.commitment(),
            &c.entries,
            0,
            c.pv0.clone(),
        )
        .unwrap();
        let alice_spend_pv = spend(
            c.alice_sk,
            c.alice_pk,
            c.alice_coin.commitment(),
            &c.entries[..1],
            &c.tx1,
            &[c.alice_coin.clone()],
            &[c.bob_coin.clone(), c.alice_change.clone()],
            false,
            Some(alice_receipt),
        )
        .unwrap();

        let receipt = make_receipt(c.alice_pk, cn_change, &c.entries, 1, alice_spend_pv).unwrap();
        assert_eq!(receipt.received_at, 1);
    }

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let c = build_chain();
        let cn_alice = c.alice_coin.commitment();
        let cn_bob = c.bob_coin.commitment();

        let alice_receipt = make_receipt(c.alice_pk, cn_alice, &c.entries, 0, c.pv0).unwrap();
        let pv1 = spend(
            c.alice_sk,
            c.alice_pk,
            cn_alice,
            &c.entries[..1],
            &c.tx1,
            &[c.alice_coin.clone()],
            &[c.bob_coin.clone(), c.alice_change.clone()],
            false,
            Some(alice_receipt),
        )
        .unwrap();

        let bob_receipt = make_receipt(c.bob_pk, cn_bob, &c.entries, 1, pv1).unwrap();
        spend(
            c.bob_sk,
            c.bob_pk,
            cn_bob,
            &c.entries[..2],
            &c.tx2,
            &[c.bob_coin.clone()],
            &[c.carol_coin.clone()],
            false,
            Some(bob_receipt),
        )
        .unwrap();
        let _ = (c.genesis_coin, c.tx0, c.carol_pk);
    }

    #[test]
    fn rejects_wrong_secret_key() {
        let (alice_sk, _) = owner_party(1);
        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin = coin(0xA2, 100, derive_owner_pk(&alice_sk));
        let (tx0, _, _) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(alice_coin.clone(), derive_owner_pk(&alice_sk), [0u8; 32])],
        );

        let err = spend(
            alice_sk,
            genesis_pk(),
            genesis_coin.commitment(),
            &[],
            &tx0,
            &[genesis_coin],
            &[alice_coin],
            true,
            None,
        )
        .unwrap_err();
        assert_eq!(err, "pk_P must be the public key for sk_P");
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let alice_coin = coin(0xA1, 100, alice_pk);
        let bob_coin = coin(0xB1, 100, bob_pk);
        let (tx0, _, _) = make_tx(
            0,
            alice_sk,
            [0u8; 32],
            &[alice_coin.clone()],
            &[(bob_coin.clone(), bob_pk, [0u8; 32])],
        );

        let err = spend(
            alice_sk,
            alice_pk,
            alice_coin.commitment(),
            &[],
            &tx0,
            &[alice_coin],
            &[bob_coin],
            true,
            None,
        )
        .unwrap_err();
        assert_eq!(err, "only the genesis key may mint without provenance");
    }

    #[test]
    fn rejects_building_a_receipt_for_a_coin_never_created() {
        let (_, alice_pk) = owner_party(1);
        let (_, carol_pk) = owner_party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin = coin(0xA2, 100, alice_pk);
        let carol_fake_input = coin(0xC1, 100, carol_pk);

        let (tx0, sk0, r0) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(alice_coin, alice_pk, [0u8; 32])],
        );
        let entries = vec![enc(
            &tx0,
            genesis_coin.commitment(),
            &genesis_sk(),
            &r0,
            sk0,
        )];
        let cn_carol = carol_fake_input.commitment();

        let pv0 = spend(
            genesis_sk(),
            genesis_pk(),
            genesis_coin.commitment(),
            &[],
            &tx0,
            &[genesis_coin],
            &[coin(0xA2, 100, alice_pk)],
            true,
            None,
        )
        .unwrap();

        let err = make_receipt(carol_pk, cn_carol, &entries, 0, pv0).unwrap_err();
        assert_eq!(err, "entry_k does not create coin_commitment");
    }

    #[test]
    fn rejects_receipt_when_creating_transaction_was_itself_a_double_spend() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin = coin(0xA2, 100, alice_pk);
        let bob_coin = coin(0xB1, 100, bob_pk);
        let carol_coin = coin(0xC1, 100, carol_pk);

        let (tx0, sk0, r0) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk, [0u8; 32])],
        );
        let (tx1, sk1, r1) = make_tx(
            1,
            alice_sk,
            [0u8; 32],
            &[alice_coin.clone()],
            &[(bob_coin, bob_pk, [0u8; 32])],
        );
        let (tx2, sk2, r2) = make_tx(
            2,
            alice_sk,
            [0u8; 32],
            &[alice_coin.clone()],
            &[(carol_coin.clone(), carol_pk, [0u8; 32])],
        );
        let entries = vec![
            enc(&tx0, genesis_coin.commitment(), &genesis_sk(), &r0, sk0),
            enc(&tx1, alice_coin.commitment(), &alice_sk, &r1, sk1),
            enc(&tx2, alice_coin.commitment(), &alice_sk, &r2, sk2),
        ];

        let pv0 = spend(
            genesis_sk(),
            genesis_pk(),
            genesis_coin.commitment(),
            &[],
            &tx0,
            &[genesis_coin],
            &[alice_coin],
            true,
            None,
        )
        .unwrap();

        let cn_carol = carol_coin.commitment();
        let err = make_receipt(carol_pk, cn_carol, &entries, 2, pv0).unwrap_err();
        assert_eq!(err, "parent transaction's nullifier was already present on the board — it was a double-spend");
    }

    #[test]
    fn rejects_double_spend() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (bob_sk, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin = coin(0xA2, 100, alice_pk);
        let bob_coin = coin(0xB1, 60, bob_pk);
        let alice_change = coin(0xB2, 40, alice_pk);
        let carol_coin = coin(0xC1, 100, carol_pk);

        let cn_alice = alice_coin.commitment();

        let (tx0, sk0, r0) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk, [0u8; 32])],
        );
        let (tx1, sk1, r1) = make_tx(
            1,
            alice_sk,
            [0u8; 32],
            &[alice_coin.clone()],
            &[
                (bob_coin.clone(), bob_pk, [0u8; 32]),
                (alice_change.clone(), alice_pk, [0u8; 32]),
            ],
        );
        let (tx1b, _, _) = make_tx(
            2,
            alice_sk,
            [0u8; 32],
            &[alice_coin.clone()],
            &[(carol_coin.clone(), carol_pk, [0u8; 32])],
        );
        let entries = vec![
            enc(&tx0, genesis_coin.commitment(), &genesis_sk(), &r0, sk0),
            enc(&tx1, alice_coin.commitment(), &alice_sk, &r1, sk1),
        ];

        let pv0 = spend(
            genesis_sk(),
            genesis_pk(),
            genesis_coin.commitment(),
            &[],
            &tx0,
            &[genesis_coin],
            &[alice_coin.clone()],
            true,
            None,
        )
        .unwrap();

        let alice_receipt = make_receipt(alice_pk, cn_alice, &entries, 0, pv0).unwrap();
        assert_eq!(alice_receipt.received_at, 0);

        spend(
            alice_sk,
            alice_pk,
            cn_alice,
            &entries[..1],
            &tx1,
            &[alice_coin.clone()],
            &[bob_coin, alice_change],
            false,
            Some(alice_receipt.clone()),
        )
        .unwrap();

        let err = spend(
            alice_sk,
            alice_pk,
            cn_alice,
            &entries,
            &tx1b,
            &[alice_coin],
            &[carol_coin],
            false,
            Some(alice_receipt),
        )
        .unwrap_err();
        assert_eq!(err, "P must not have spent this coin before (double spend)");
        let _ = bob_sk;
    }

    #[test]
    fn rejects_spend_using_a_receipt_for_a_different_coin() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin = coin(0xA2, 100, alice_pk);
        let bob_coin = coin(0xB1, 40, bob_pk);
        let alice_change = coin(0xB2, 60, alice_pk);

        let (tx0, sk0, r0) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk, [0u8; 32])],
        );
        let (tx1, sk1, r1) = make_tx(
            1,
            alice_sk,
            [0u8; 32],
            &[alice_coin.clone()],
            &[
                (bob_coin.clone(), bob_pk, [0u8; 32]),
                (alice_change.clone(), alice_pk, [0u8; 32]),
            ],
        );
        let entries = vec![
            enc(&tx0, genesis_coin.commitment(), &genesis_sk(), &r0, sk0),
            enc(&tx1, alice_coin.commitment(), &alice_sk, &r1, sk1),
        ];

        let cn_alice = alice_coin.commitment();
        let cn_change = alice_change.commitment();

        let pv0 = spend(
            genesis_sk(),
            genesis_pk(),
            genesis_coin.commitment(),
            &[],
            &tx0,
            &[genesis_coin],
            &[alice_coin.clone()],
            true,
            None,
        )
        .unwrap();
        let alice_receipt = make_receipt(alice_pk, cn_alice, &entries, 0, pv0).unwrap();

        let payout = coin(0xC1, 60, bob_pk);
        let (tx2, _, _) = make_tx(
            2,
            alice_sk,
            [0u8; 32],
            &[alice_change.clone()],
            &[(payout.clone(), bob_pk, [0u8; 32])],
        );
        let err = spend(
            alice_sk,
            alice_pk,
            cn_change,
            &entries,
            &tx2,
            &[alice_change],
            &[payout],
            false,
            Some(alice_receipt),
        )
        .unwrap_err();
        assert_eq!(err, "coin-proof tracks a different coin");
        let _ = (sk1, r1);
    }

    #[test]
    fn rejects_value_conservation_violation() {
        let (_, alice_pk) = owner_party(1);
        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin = coin(0xA2, 100, alice_pk);
        let extra_coin = coin(0xA3, 1, alice_pk);

        let (tx0, _, _) = make_tx(
            0,
            genesis_sk(),
            [0u8; 32],
            &[genesis_coin.clone()],
            &[
                (alice_coin.clone(), alice_pk, [0u8; 32]),
                (extra_coin.clone(), alice_pk, [0u8; 32]),
            ],
        );

        let err = spend(
            genesis_sk(),
            genesis_pk(),
            genesis_coin.commitment(),
            &[],
            &tx0,
            &[genesis_coin],
            &[alice_coin, extra_coin],
            true,
            None,
        )
        .unwrap_err();
        assert_eq!(
            err,
            "transaction violates value conservation: sum(inputs) must equal sum(outputs)"
        );
    }

    #[test]
    fn nullifier_tree_insert_cost_does_not_grow_with_tree_size() {
        fn value(i: u32) -> Fr {
            Fr::from(i as u64 + 1)
        }

        let mut tree = NullifierTree::new();
        let batch = 500u32;
        let t = std::time::Instant::now();
        for i in 0..batch {
            tree.insert(value(i));
        }
        let small_per_insert = t.elapsed() / batch;

        for i in batch..(batch * 8) {
            tree.insert(value(i));
        }
        let t = std::time::Instant::now();
        for i in (batch * 8)..(batch * 9) {
            tree.insert(value(i));
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
