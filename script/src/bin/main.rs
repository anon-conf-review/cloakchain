use std::time::Instant;

use ark_ec::pairing::Pairing;
use ark_gm17::{Proof, VerifyingKey};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use clap::Parser;
use cloakkchain_circuit_coinproof::ReceiptStepCircuit;
use cloakkchain_circuit_spend::{GenesisSpendCircuit, SpendStepCircuit, MAX_INPUTS, MAX_OUTPUTS};
use cloakkchain_circuit_wrap::WrapCircuit;
use cloakkchain_lib::{
    append_path_for_next, compute_root_from_path, derive_enc_pk, derive_owner_pk,
    entry_ciphertext_commitment, fold_owner_scalar, genesis_pk, genesis_sk, merkle_leaf,
    owner_pk_to_field_pair, poseidon_hash, scan_entry, BoardEntry, Coin, Fr, NonMembershipWitness,
    NullifierTree, OwnerPk, OwnerScalar, Transaction, EK_SALT,
};

const GENESIS_SPEND_PUBLIC_INPUTS: usize = 2 + MAX_OUTPUTS + 2;
const RECEIPT_PUBLIC_INPUTS: usize = 5;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,

    #[arg(long)]
    grid_cell: bool,

    #[arg(long, hide = true)]
    internal_kind: Option<String>,

    #[arg(long, hide = true)]
    internal_witness: Option<String>,

    #[arg(long, hide = true)]
    internal_output: Option<String>,
}

struct Party {
    name: &'static str,
    enc_sk: [u8; 32],
    enc_pk: [u8; 32],
    sk_p: OwnerScalar,
    pk_p: OwnerPk,
}

impl Party {
    fn new(name: &'static str, seed: u8) -> Self {
        let mut enc_sk = [0u8; 32];
        enc_sk[1] = seed;
        let enc_pk = derive_enc_pk(&enc_sk);
        let sk_p = OwnerScalar::from(seed as u64 + 100);
        let pk_p = derive_owner_pk(&sk_p);
        Self { name, enc_sk, enc_pk, sk_p, pk_p }
    }

    fn genesis() -> Self {
        Self { name: "Genesis", enc_sk: [0u8; 32], enc_pk: [0u8; 32], sk_p: genesis_sk(), pk_p: genesis_pk() }
    }
}

fn coin(seed: u8, value: u64, owner_pk: OwnerPk) -> Coin {
    Coin { value, rand: Fr::from(seed as u64 + 1000), owner_pk }
}

fn pad_outputs(real: &[Fr]) -> [Fr; MAX_OUTPUTS] {
    let mut out = [Fr::from(0u64); MAX_OUTPUTS];
    out[..real.len()].copy_from_slice(real);
    out
}

fn make_tx(
    id: u64,
    sender_enc_sk: [u8; 32],

    _sender_sk_p: &OwnerScalar,

    _input_coins: &[Coin],
    outputs: &[(Coin, [u8; 32])],
) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
    use sha2::{Digest, Sha256};
    let session_key: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(sender_enc_sk);
        h.update(id.to_le_bytes());
        h.update(EK_SALT);
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    };
    let recipient_enc_pks: Vec<[u8; 32]> = outputs.iter().map(|(_, rpk)| *rpk).collect();
    let output_commitments: Vec<Fr> = outputs.iter().map(|(c, _)| c.commitment()).collect();
    let note_encs: Vec<Vec<u8>> = outputs
        .iter()
        .enumerate()
        .map(|(i, (c, _))| cloakkchain_lib::build_note_enc(&session_key, i, c))
        .collect();
    let tx = Transaction { id, output_commitments, note_encs, spend_proof: vec![] };
    (tx, session_key, recipient_enc_pks)
}

fn wait_tracking_peak_memory(mut child: std::process::Child) -> (std::process::ExitStatus, Option<u64>) {
    let pid = child.id();
    let mut peak_kb: Option<u64> = None;
    loop {
        if let Ok(status_text) = std::fs::read_to_string(format!("/proc/{pid}/status")) {
            for line in status_text.lines() {
                if let Some(rest) = line.strip_prefix("VmHWM:") {
                    if let Some(kb) = rest.split_whitespace().next().and_then(|s| s.parse::<u64>().ok()) {
                        peak_kb = Some(peak_kb.map_or(kb, |p: u64| p.max(kb)));
                    }
                }
            }
        }
        match child.try_wait().expect("poll proving subprocess") {
            Some(status) => return (status, peak_kb),
            None => std::thread::sleep(std::time::Duration::from_millis(50)),
        }
    }
}

fn count_constraints<F: ark_ff::Field, C: ConstraintSynthesizer<F> + Clone>(circuit: &C) -> usize {
    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(ark_relations::r1cs::SynthesisMode::Setup);
    circuit.clone().generate_constraints(cs.clone()).expect("synthesize constraints for counting");
    cs.num_constraints()
}

fn write_vk_proof<E: Pairing>(vk: &VerifyingKey<E>, proof: &Proof<E>, path: &std::path::Path) {
    let mut buf = Vec::new();
    vk.serialize_compressed(&mut buf).expect("serialize verifying key");
    proof.serialize_compressed(&mut buf).expect("serialize proof");
    std::fs::write(path, buf).expect("write output file");
}

fn read_vk_proof<E: Pairing>(path: &std::path::Path) -> (VerifyingKey<E>, Proof<E>) {
    let bytes = std::fs::read(path).expect("read output file");
    let mut cursor = &bytes[..];
    let vk = VerifyingKey::<E>::deserialize_compressed(&mut cursor).expect("deserialize verifying key");
    let proof = Proof::<E>::deserialize_compressed(&mut cursor).expect("deserialize proof");
    (vk, proof)
}

fn run_step_subprocess<C: CanonicalSerialize, E: Pairing>(
    kind: &str,
    circuit: &C,
) -> (VerifyingKey<E>, Proof<E>, f64, u64) {
    let witness_path = std::env::temp_dir().join(format!("cloakkchain_{kind}_witness.bin"));
    let output_path = std::env::temp_dir().join(format!("cloakkchain_{kind}_output.bin"));

    let mut witness_buf = Vec::new();
    circuit.serialize_compressed(&mut witness_buf).expect("serialize witness");
    std::fs::write(&witness_path, witness_buf).expect("write witness file");

    let exe = std::env::current_exe().expect("current_exe");
    let mut cmd = std::process::Command::new(&exe);
    cmd.args([
        "--internal-kind",
        kind,
        "--internal-witness",
        witness_path.to_str().expect("temp path is valid UTF-8"),
        "--internal-output",
        output_path.to_str().expect("temp path is valid UTF-8"),
    ]);

    let t = Instant::now();
    let child = cmd.spawn().expect("spawn proving subprocess");
    let (status, peak_mem_kb) = wait_tracking_peak_memory(child);
    let prove_secs = t.elapsed().as_secs_f64();
    assert!(status.success(), "subprocess for {kind} exited with {status}");

    let (vk, proof) = read_vk_proof::<E>(&output_path);
    let _ = std::fs::remove_file(&witness_path);
    let _ = std::fs::remove_file(&output_path);
    (vk, proof, prove_secs, peak_mem_kb.unwrap_or(0))
}

fn run_internal_step(kind: &str, witness_path: &str, output_path: &str) {
    let witness_bytes = std::fs::read(witness_path).expect("read witness file");
    let mut rng = StdRng::seed_from_u64(0x636c6f616b);
    let output_path = std::path::Path::new(output_path);

    match kind {
        "genesis" => {
            let circuit = GenesisSpendCircuit::deserialize_compressed(&witness_bytes[..]).expect("deserialize witness");
            let (pk, vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
            let proof = cloakkchain_circuit_spend::prove(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT4_753>(&vk, &proof, output_path);
        }
        "spend_non_genesis" => {
            let circuit = SpendStepCircuit::deserialize_compressed(&witness_bytes[..]).expect("deserialize witness");
            let wrap_vk = circuit.wrap_vk.clone();
            let (pk, vk) = cloakkchain_circuit_spend::setup_non_genesis(wrap_vk, &mut rng).unwrap();
            let proof = cloakkchain_circuit_spend::prove_non_genesis(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT4_753>(&vk, &proof, output_path);
        }
        "receipt" => {
            let circuit = ReceiptStepCircuit::deserialize_compressed(&witness_bytes[..]).expect("deserialize witness");
            let wrap_vk = circuit.wrap_vk.clone();
            let (pk, vk) = cloakkchain_circuit_coinproof::setup(wrap_vk, &mut rng).unwrap();
            let proof = cloakkchain_circuit_coinproof::prove(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT4_753>(&vk, &proof, output_path);
        }
        "wrap6" => {
            let circuit = WrapCircuit::<GENESIS_SPEND_PUBLIC_INPUTS>::deserialize_compressed(&witness_bytes[..])
                .expect("deserialize witness");
            let inner_vk = circuit.inner_vk.clone();
            let (pk, vk) =
                cloakkchain_circuit_wrap::setup::<GENESIS_SPEND_PUBLIC_INPUTS, _>(inner_vk, &mut rng).unwrap();
            let proof = cloakkchain_circuit_wrap::prove::<GENESIS_SPEND_PUBLIC_INPUTS, _>(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT6_753>(&vk, &proof, output_path);
        }
        "wrap5" => {
            let circuit = WrapCircuit::<RECEIPT_PUBLIC_INPUTS>::deserialize_compressed(&witness_bytes[..])
                .expect("deserialize witness");
            let inner_vk = circuit.inner_vk.clone();
            let (pk, vk) = cloakkchain_circuit_wrap::setup::<RECEIPT_PUBLIC_INPUTS, _>(inner_vk, &mut rng).unwrap();
            let proof = cloakkchain_circuit_wrap::prove::<RECEIPT_PUBLIC_INPUTS, _>(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT6_753>(&vk, &proof, output_path);
        }
        other => panic!("unknown --internal-kind {other}"),
    }
}

struct ProveStats {
    name: String,
    board_size: usize,
    constraints: usize,
    prove_secs: f64,
    verify_ms: f64,
    proof_bytes: usize,
    entry_bytes: Option<usize>,
    peak_mem_kb: u64,
}

fn fmt_constraints(c: usize) -> String {
    if c >= 1_000_000 {
        format!("{:.2}M", c as f64 / 1_000_000.0)
    } else if c >= 1_000 {
        format!("{:.1}K", c as f64 / 1_000.0)
    } else {
        format!("{c}")
    }
}

fn fmt_bytes(b: usize) -> String {
    if b >= 1_048_576 {
        format!("{:.2} MB", b as f64 / 1_048_576.0)
    } else if b >= 1024 {
        format!("{:.1} KB", b as f64 / 1024.0)
    } else {
        format!("{b} B")
    }
}

fn fmt_mem_kb(kb: u64) -> String {
    fmt_bytes(kb as usize * 1024)
}

fn print_prove_table(stats: &[ProveStats]) {
    let w = 122;
    println!("\n{}", "=".repeat(w));
    println!("  Proof Statistics");
    println!("{}", "=".repeat(w));
    println!(
        "{:<28} {:>5}  {:>11}  {:>9}  {:>10}  {:>11}  {:>11}  {:>11}",
        "Step", "Board", "Constraints", "Prove", "Verify", "Proof", "Entry", "Peak Mem"
    );
    println!("{}", "-".repeat(w));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {

        let entry_col = s.entry_bytes.map_or("          —".into(), |b| format!("{:>8} B", b));
        println!(
            "{:<28} {:>5}  {:>11} {:>7.1} s  {:>8.1} ms  {:>11}  {}  {:>11}",
            s.name,
            s.board_size,
            fmt_constraints(s.constraints),
            s.prove_secs,
            s.verify_ms,
            fmt_bytes(s.proof_bytes),
            entry_col,
            fmt_mem_kb(s.peak_mem_kb)
        );
        tp += s.prove_secs;
        tv += s.verify_ms;
    }
    println!("{}", "-".repeat(w));
    println!("{:<28} {:>5} {:>7.1} s  {:>8.1} ms", "TOTAL", "", tp, tv);
    println!("{}", "=".repeat(w));
}

fn ark_serialize_bytes<T: ark_serialize::CanonicalSerialize>(v: &T) -> Vec<u8> {
    let mut out = Vec::new();
    v.serialize_compressed(&mut out).expect("serialize proof");
    out
}

fn ark_serialize_len<T: ark_serialize::CanonicalSerialize>(v: &T) -> usize {
    v.compressed_size()
}

fn main() {
    let args = Args::parse();

    if let Some(kind) = args.internal_kind {
        let witness_path = args.internal_witness.expect("--internal-witness required with --internal-kind");
        let output_path = args.internal_output.expect("--internal-output required with --internal-kind");
        run_internal_step(&kind, &witness_path, &output_path);
        return;
    }

    if args.grid_cell {
        run_prove_grid_cell();
        return;
    }

    let mode_count = [args.execute, args.prove].iter().filter(|&&b| b).count();
    if mode_count != 1 {
        eprintln!("Error: specify exactly one of --execute, --prove");
        std::process::exit(1);
    }

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let genesis_coin = coin(0xA1, 100, genesis.pk_p);
    let alice_coin = coin(0xA2, 100, alice.pk_p);

    if args.execute {
        run_execute(&genesis, &genesis_coin, &alice_coin);
        return;
    }

    run_prove();
}

fn run_execute(genesis: &Party, genesis_coin: &Coin, alice_coin: &Coin) {
    println!("--execute: checking GenesisSpendCircuit's constraints only (no proving)");

    let output_commitments = pad_outputs(&[alice_coin.commitment()]);
    let append_path = append_path_for_next(&[]);
    let board_root = compute_root_from_path(Fr::from(0u64), 0, &append_path);
    let own_nullifier = poseidon_hash(&[genesis_coin.commitment(), fold_owner_scalar(&genesis.sk_p)]);
    let tree = NullifierTree::new();

    let circuit = GenesisSpendCircuit {
        pk_p: Some(genesis.pk_p),
        output_commitments: Some(output_commitments),
        board_root: Some(board_root),
        current_nullifier_root: Some(tree.root()),
        sk_p: Some(genesis.sk_p),
        input_coins: [Some(genesis_coin.clone()), None],
        output_coins: [Some(alice_coin.clone()), None],
        entry_position: Some(0),
        append_path: Some(append_path),
        own_nullifier_nonmembership: [Some(tree.prove_non_membership(own_nullifier)), None],
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).expect("synthesize constraints");
    let satisfied = cs.is_satisfied().expect("check satisfiability");
    println!("  constraints: {}", cs.num_constraints());
    println!("  satisfied:   {satisfied}");
    assert!(satisfied);
    println!("\nRun --prove for the full chain (nine real GM17 proofs).");
}

fn run_prove() {
    let mut stats: Vec<ProveStats> = Vec::new();
    let mut entries: Vec<BoardEntry> = vec![];

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);
    let carol = Party::new("Carol", 3);

    println!("--- Slot 0: Genesis mints 100 units to Alice ---");
    println!("  Proving: pk_p is the fixed genesis key, the mint's nullifier isn't already spent, and the board root updates correctly for the new coin.");
    let genesis_coin = coin(0xA1, 100, genesis.pk_p);
    let alice_coin = coin(0xA2, 100, alice.pk_p);
    let genesis_outputs = pad_outputs(&[alice_coin.commitment()]);
    let genesis_append_path = append_path_for_next(&entries);
    let genesis_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &genesis_append_path);
    let genesis_own_nullifier = poseidon_hash(&[genesis_coin.commitment(), fold_owner_scalar(&genesis.sk_p)]);
    let empty_tree = NullifierTree::new();

    let genesis_circuit = GenesisSpendCircuit {
        pk_p: Some(genesis.pk_p),
        output_commitments: Some(genesis_outputs),
        board_root: Some(genesis_board_root),
        current_nullifier_root: Some(empty_tree.root()),
        sk_p: Some(genesis.sk_p),
        input_coins: [Some(genesis_coin.clone()), None],
        output_coins: [Some(alice_coin.clone()), None],
        entry_position: Some(entries.len() as u64),
        append_path: Some(genesis_append_path.clone()),
        own_nullifier_nonmembership: [Some(empty_tree.prove_non_membership(genesis_own_nullifier)), None],
    };
    let genesis_public_inputs: [Fr; GENESIS_SPEND_PUBLIC_INPUTS] =
        GenesisSpendCircuit::public_inputs(genesis.pk_p, genesis_outputs, genesis_board_root, empty_tree.root())
            .try_into()
            .unwrap();

    let (genesis_vk, genesis_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT4_753>("genesis", &genesis_circuit);
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify(&genesis_vk, &genesis_public_inputs, &genesis_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Genesis mint".into(),
        board_size: entries.len() + 1,
        constraints: count_constraints(&genesis_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&genesis_proof),
        entry_bytes: None,
        peak_mem_kb,
    });

    let (mut tx0, s0, r0) =
        make_tx(0, genesis.enc_sk, &genesis.sk_p, &[genesis_coin.clone()], &[(alice_coin.clone(), alice.enc_pk)]);
    tx0.spend_proof = ark_serialize_bytes(&genesis_proof);
    let genesis_entry = cloakkchain_lib::encrypt_tx(&tx0, genesis_coin.commitment(), &genesis.sk_p, &r0, s0);
    entries.push(genesis_entry.clone());
    let entry0_bytes = bincode::serialize(&genesis_entry).map(|v| v.len()).ok();

    println!("  Wrapping the genesis proof: re-verifies it on the other curve (MNT6-753) and re-exposes its public inputs as small chunks, so Alice's receipt circuit (back on MNT4-753) can recursively check it.");
    let wrap_genesis_circuit = WrapCircuit::<GENESIS_SPEND_PUBLIC_INPUTS> {
        inner_vk: genesis_vk.clone(),
        inner_proof: Some(genesis_proof),
        inner_public_inputs: Some(genesis_public_inputs),
    };
    let (wrap_genesis_vk, wrap_genesis_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT6_753>("wrap6", &wrap_genesis_circuit);
    let wrap_genesis_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&genesis_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_genesis_vk, &wrap_genesis_public_inputs, &wrap_genesis_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Wrapped in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Wrap genesis proof".into(),
        board_size: entries.len(),
        constraints: count_constraints(&wrap_genesis_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_genesis_proof),
        entry_bytes: entry0_bytes,
        peak_mem_kb,
    });

    println!("\n--- Alice scans slot 0, builds her receipt ---");
    let alice_tx = scan_entry(&alice.enc_sk, &genesis_entry).expect("Alice must be able to decrypt slot 0");
    assert!(alice_tx.receives_coin(&alice_coin.commitment()), "Alice's tx must transfer her coin");
    println!("  [{}] discovered coin (value={}) at slot 0", alice.name, alice_coin.value);
    println!("  Proving Alice's receipt: this coin was really created by a verified spend, is really published on the board at this slot, and that spend's own parent wasn't a double-spend — all without revealing tag/rand/value.");

    let alice_receipt_board_root =
        compute_root_from_path(merkle_leaf(0, &genesis_entry), 0, &genesis_append_path);
    let (apx, apy) = owner_pk_to_field_pair(&alice.pk_p);

    let alice_receipt_circuit = ReceiptStepCircuit {
        owner_pk_x: Some(apx),
        owner_pk_y: Some(apy),
        coin_commitment: Some(alice_coin.commitment()),
        board_root: Some(alice_receipt_board_root),
        received_at: Some(0),
        wrap_vk: wrap_genesis_vk.clone(),
        wrap_proof: Some(wrap_genesis_proof),
        wrap_public_inputs: Some(genesis_public_inputs),
        entry_nullifier: Some(genesis_entry.nullifier),
        entry_output_commitments: Some(genesis_outputs),
        entry_ciphertext_commitment: Some(entry_ciphertext_commitment(&genesis_entry)),
        received_slot: Some(0),
        append_path: Some(genesis_append_path.clone()),
        parent_nonmembership: Some(empty_tree.prove_non_membership(genesis_entry.nullifier)),
        nullifier_root_at_parent_slot: Some(empty_tree.root()),
        sk_p: Some(alice.sk_p),
        coin_value: Some(alice_coin.value),
        coin_rand: Some(alice_coin.rand),
    };
    let alice_receipt_public_inputs: [Fr; RECEIPT_PUBLIC_INPUTS] =
        ReceiptStepCircuit::public_inputs(apx, apy, alice_coin.commitment(), alice_receipt_board_root, 0)
            .try_into()
            .unwrap();

    let (alice_receipt_vk, alice_receipt_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT4_753>("receipt", &alice_receipt_circuit);
    let t = Instant::now();
    assert!(cloakkchain_circuit_coinproof::verify(&alice_receipt_vk, &alice_receipt_public_inputs, &alice_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Alice's receipt".into(),
        board_size: entries.len(),
        constraints: count_constraints(&alice_receipt_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&alice_receipt_proof),
        entry_bytes: None,
        peak_mem_kb,
    });

    println!("  Wrapping Alice's receipt so her spend circuit (back on MNT4-753) can recursively verify it as proof of provenance.");
    let wrap_alice_receipt_circuit = WrapCircuit::<RECEIPT_PUBLIC_INPUTS> {
        inner_vk: alice_receipt_vk.clone(),
        inner_proof: Some(alice_receipt_proof),
        inner_public_inputs: Some(alice_receipt_public_inputs),
    };
    let (wrap_alice_receipt_vk, wrap_alice_receipt_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT6_753>("wrap5", &wrap_alice_receipt_circuit);
    let wrap_alice_receipt_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&alice_receipt_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_alice_receipt_vk, &wrap_alice_receipt_public_inputs, &wrap_alice_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Wrapped in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Wrap Alice's receipt".into(),
        board_size: entries.len(),
        constraints: count_constraints(&wrap_alice_receipt_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_alice_receipt_proof),
        entry_bytes: None,
        peak_mem_kb,
    });

    println!("\n--- Slot 1: Alice spends to Bob (40) + change back to herself (60) ---");
    println!("  Proving: Alice owns the input coin, its nullifier isn't already in the nullifier tree (not a double-spend), value conservation holds (100 in = 40 + 60 out), the two new coins are correctly published, and her wrapped receipt recursively verifies she really received the coin she's spending.");
    let bob_coin = coin(0xB1, 40, bob.pk_p);
    let change_coin = coin(0xB2, 60, alice.pk_p);
    let alice_spend_outputs = pad_outputs(&[bob_coin.commitment(), change_coin.commitment()]);

    let alice_spend_append_path = append_path_for_next(&entries);
    let alice_spend_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &alice_spend_append_path);
    let alice_own_nullifier = poseidon_hash(&[alice_coin.commitment(), fold_owner_scalar(&alice.sk_p)]);
    let mut tree_after_genesis = NullifierTree::new();
    tree_after_genesis.insert(genesis_own_nullifier);

    let alice_spend_circuit = SpendStepCircuit {
        pk_p: Some(alice.pk_p),
        output_commitments: Some(alice_spend_outputs),
        board_root: Some(alice_spend_board_root),
        current_nullifier_root: Some(tree_after_genesis.root()),
        sk_p: Some(alice.sk_p),
        input_coins: [Some(alice_coin.clone()), None],
        output_coins: [Some(bob_coin.clone()), Some(change_coin.clone())],
        entry_position: Some(entries.len() as u64),
        append_path: Some(alice_spend_append_path.clone()),
        own_nullifier_nonmembership: [Some(tree_after_genesis.prove_non_membership(alice_own_nullifier)), None],
        wrap_vk: wrap_alice_receipt_vk.clone(),
        input_receipt_proofs: [Some(wrap_alice_receipt_proof), None],
        input_receipt_public_inputs: [Some(alice_receipt_public_inputs), None],
    };
    let alice_spend_public_inputs: [Fr; GENESIS_SPEND_PUBLIC_INPUTS] = SpendStepCircuit::public_inputs(
        alice.pk_p,
        alice_spend_outputs,
        alice_spend_board_root,
        tree_after_genesis.root(),
    )
    .try_into()
    .unwrap();

    let (alice_spend_vk, alice_spend_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT4_753>("spend_non_genesis", &alice_spend_circuit);
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify_non_genesis(&alice_spend_vk, &alice_spend_public_inputs, &alice_spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Alice -> Bob + change".into(),
        board_size: entries.len() + 1,
        constraints: count_constraints(&alice_spend_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&alice_spend_proof),
        entry_bytes: None,
        peak_mem_kb,
    });

    let (mut tx1, s1, r1) = make_tx(
        1,
        alice.enc_sk,
        &alice.sk_p,
        &[alice_coin.clone()],
        &[(bob_coin.clone(), bob.enc_pk), (change_coin.clone(), alice.enc_pk)],
    );
    tx1.spend_proof = ark_serialize_bytes(&alice_spend_proof);
    let alice_entry = cloakkchain_lib::encrypt_tx(&tx1, alice_coin.commitment(), &alice.sk_p, &r1, s1);
    entries.push(alice_entry.clone());
    let entry1_bytes = bincode::serialize(&alice_entry).map(|v| v.len()).ok();

    println!("  Wrapping Alice's spend so Bob's receipt circuit (back on MNT4-753) can recursively verify it.");
    let wrap_alice_spend_circuit = WrapCircuit::<GENESIS_SPEND_PUBLIC_INPUTS> {
        inner_vk: alice_spend_vk.clone(),
        inner_proof: Some(alice_spend_proof),
        inner_public_inputs: Some(alice_spend_public_inputs),
    };
    let (wrap_alice_spend_vk, wrap_alice_spend_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT6_753>("wrap6", &wrap_alice_spend_circuit);
    let wrap_alice_spend_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&alice_spend_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_alice_spend_vk, &wrap_alice_spend_public_inputs, &wrap_alice_spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Wrapped in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Wrap Alice's spend".into(),
        board_size: entries.len(),
        constraints: count_constraints(&wrap_alice_spend_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_alice_spend_proof),
        entry_bytes: entry1_bytes,
        peak_mem_kb,
    });

    println!("\n--- Bob scans slot 1, builds his receipt ---");
    let bob_tx = scan_entry(&bob.enc_sk, &alice_entry).expect("Bob must be able to decrypt slot 1");
    assert!(bob_tx.receives_coin(&bob_coin.commitment()));
    println!("  [{}] discovered coin (value={}) at slot 1", bob.name, bob_coin.value);
    println!("  Proving Bob's receipt (second generation: recursively verifies a wrapped *spend* proof this time, not a wrapped genesis proof — same circuit, keyed to Alice's spend's verifying key instead).");

    let bob_receipt_board_root =
        compute_root_from_path(merkle_leaf(1, &alice_entry), 1, &alice_spend_append_path);
    let (bpx, bpy) = owner_pk_to_field_pair(&bob.pk_p);

    let bob_receipt_circuit = ReceiptStepCircuit {
        owner_pk_x: Some(bpx),
        owner_pk_y: Some(bpy),
        coin_commitment: Some(bob_coin.commitment()),
        board_root: Some(bob_receipt_board_root),
        received_at: Some(1),
        wrap_vk: wrap_alice_spend_vk.clone(),
        wrap_proof: Some(wrap_alice_spend_proof),
        wrap_public_inputs: Some(alice_spend_public_inputs),
        entry_nullifier: Some(alice_entry.nullifier),
        entry_output_commitments: Some(alice_spend_outputs),
        entry_ciphertext_commitment: Some(entry_ciphertext_commitment(&alice_entry)),
        received_slot: Some(1),
        append_path: Some(alice_spend_append_path.clone()),
        parent_nonmembership: Some(tree_after_genesis.prove_non_membership(alice_entry.nullifier)),
        nullifier_root_at_parent_slot: Some(tree_after_genesis.root()),
        sk_p: Some(bob.sk_p),
        coin_value: Some(bob_coin.value),
        coin_rand: Some(bob_coin.rand),
    };
    let bob_receipt_public_inputs: [Fr; RECEIPT_PUBLIC_INPUTS] =
        ReceiptStepCircuit::public_inputs(bpx, bpy, bob_coin.commitment(), bob_receipt_board_root, 1)
            .try_into()
            .unwrap();

    let (bob_receipt_vk, bob_receipt_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT4_753>("receipt", &bob_receipt_circuit);
    let t = Instant::now();
    assert!(cloakkchain_circuit_coinproof::verify(&bob_receipt_vk, &bob_receipt_public_inputs, &bob_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Bob's receipt (gen 2)".into(),
        board_size: entries.len(),
        constraints: count_constraints(&bob_receipt_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&bob_receipt_proof),
        entry_bytes: None,
        peak_mem_kb,
    });

    println!("  Wrapping Bob's receipt so his spend circuit can recursively verify it.");
    let wrap_bob_receipt_circuit = WrapCircuit::<RECEIPT_PUBLIC_INPUTS> {
        inner_vk: bob_receipt_vk.clone(),
        inner_proof: Some(bob_receipt_proof),
        inner_public_inputs: Some(bob_receipt_public_inputs),
    };
    let (wrap_bob_receipt_vk, wrap_bob_receipt_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT6_753>("wrap5", &wrap_bob_receipt_circuit);
    let wrap_bob_receipt_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&bob_receipt_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_bob_receipt_vk, &wrap_bob_receipt_public_inputs, &wrap_bob_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Wrapped in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Wrap Bob's receipt".into(),
        board_size: entries.len(),
        constraints: count_constraints(&wrap_bob_receipt_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_bob_receipt_proof),
        entry_bytes: None,
        peak_mem_kb,
    });

    println!("\n--- Slot 2: Bob spends his 40 units to Carol ---");
    println!("  Proving: Bob owns the input coin, its nullifier isn't already in the nullifier tree (not a double-spend), value conservation holds (40 in = 40 out), the new coin is correctly published, and his wrapped receipt recursively verifies provenance.");
    let carol_coin = coin(0xC1, 40, carol.pk_p);
    let bob_spend_outputs = pad_outputs(&[carol_coin.commitment()]);

    let bob_spend_append_path = append_path_for_next(&entries);
    let bob_spend_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &bob_spend_append_path);
    let bob_own_nullifier = poseidon_hash(&[bob_coin.commitment(), fold_owner_scalar(&bob.sk_p)]);
    let mut tree_after_alice_spend = tree_after_genesis.clone();
    tree_after_alice_spend.insert(alice_own_nullifier);

    let bob_spend_circuit = SpendStepCircuit {
        pk_p: Some(bob.pk_p),
        output_commitments: Some(bob_spend_outputs),
        board_root: Some(bob_spend_board_root),
        current_nullifier_root: Some(tree_after_alice_spend.root()),
        sk_p: Some(bob.sk_p),
        input_coins: [Some(bob_coin.clone()), None],
        output_coins: [Some(carol_coin.clone()), None],
        entry_position: Some(entries.len() as u64),
        append_path: Some(bob_spend_append_path),
        own_nullifier_nonmembership: [Some(tree_after_alice_spend.prove_non_membership(bob_own_nullifier)), None],
        wrap_vk: wrap_bob_receipt_vk.clone(),
        input_receipt_proofs: [Some(wrap_bob_receipt_proof), None],
        input_receipt_public_inputs: [Some(bob_receipt_public_inputs), None],
    };
    let bob_spend_public_inputs = SpendStepCircuit::public_inputs(
        bob.pk_p,
        bob_spend_outputs,
        bob_spend_board_root,
        tree_after_alice_spend.root(),
    );

    let (bob_spend_vk, bob_spend_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT4_753>("spend_non_genesis", &bob_spend_circuit);
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify_non_genesis(&bob_spend_vk, &bob_spend_public_inputs, &bob_spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: "Bob -> Carol (gen 2)".into(),
        board_size: entries.len() + 1,
        constraints: count_constraints(&bob_spend_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&bob_spend_proof),
        entry_bytes: None,
        peak_mem_kb,
    });

    let (mut tx2, s2, r2) =
        make_tx(2, bob.enc_sk, &bob.sk_p, &[bob_coin.clone()], &[(carol_coin.clone(), carol.enc_pk)]);
    tx2.spend_proof = ark_serialize_bytes(&bob_spend_proof);
    let bob_entry = cloakkchain_lib::encrypt_tx(&tx2, bob_coin.commitment(), &bob.sk_p, &r2, s2);
    entries.push(bob_entry.clone());

    stats.last_mut().unwrap().entry_bytes = bincode::serialize(&bob_entry).map(|v| v.len()).ok();

    println!("\n--- Carol scans slot 2 ---");
    let carol_tx = scan_entry(&carol.enc_sk, &bob_entry).expect("Carol must be able to decrypt slot 2");
    assert!(carol_tx.receives_coin(&carol_coin.commitment()));
    println!("  [{}] discovered coin (value={}) at slot 2 — end of chain (no further receipt built)", carol.name, carol_coin.value);

    print_prove_table(&stats);
}

fn run_prove_grid_cell() {
    println!("=== Grid cell: MAX_INPUTS={MAX_INPUTS} MAX_OUTPUTS={MAX_OUTPUTS} ===");

    let mut stats: Vec<ProveStats> = Vec::new();
    let mut entries: Vec<BoardEntry> = vec![];
    let mut tree = NullifierTree::new();

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);

    let input_values: Vec<u64> = match MAX_INPUTS {
        1 => vec![100],
        2 => vec![60, 40],
        n => panic!("grid-cell scenario only supports MAX_INPUTS 1 or 2, got {n}"),
    };

    struct AliceInput {
        coin: Coin,
        own_nullifier: Fr,
    }
    let mut alice_inputs: Vec<AliceInput> = Vec::new();
    let mut wrap_vk_for_spend: Option<VerifyingKey<MNT6_753>> = None;
    let mut input_receipt_wraps: Vec<(Proof<MNT6_753>, Vec<Fr>)> = Vec::new();

    for (k, &val) in input_values.iter().enumerate() {
        println!("\n--- Genesis mint #{k}: {val} units to Alice ---");
        let genesis_coin = coin(0xA0 + k as u8, val, genesis.pk_p);
        let alice_coin = coin(0xB0 + k as u8, val, alice.pk_p);
        let genesis_outputs = pad_outputs(&[alice_coin.commitment()]);
        let g_append_path = append_path_for_next(&entries);
        let g_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &g_append_path);
        let g_own_nullifier = poseidon_hash(&[genesis_coin.commitment(), fold_owner_scalar(&genesis.sk_p)]);
        let nullifier_root_before = tree.root();
        let own_nonmembership = tree.prove_non_membership(g_own_nullifier);

        let mut g_input_coins: [Option<Coin>; MAX_INPUTS] = std::array::from_fn(|_| None);
        g_input_coins[0] = Some(genesis_coin.clone());
        let mut g_nonmembership: [Option<NonMembershipWitness>; MAX_INPUTS] = std::array::from_fn(|_| None);
        g_nonmembership[0] = Some(own_nonmembership.clone());
        let mut g_output_coins: [Option<Coin>; MAX_OUTPUTS] = std::array::from_fn(|_| None);
        g_output_coins[0] = Some(alice_coin.clone());

        let genesis_circuit = GenesisSpendCircuit {
            pk_p: Some(genesis.pk_p),
            output_commitments: Some(genesis_outputs),
            board_root: Some(g_board_root),
            current_nullifier_root: Some(nullifier_root_before),
            sk_p: Some(genesis.sk_p),
            input_coins: g_input_coins,
            output_coins: g_output_coins,
            entry_position: Some(entries.len() as u64),
            append_path: Some(g_append_path.clone()),
            own_nullifier_nonmembership: g_nonmembership,
        };
        let genesis_public_inputs: [Fr; GENESIS_SPEND_PUBLIC_INPUTS] =
            GenesisSpendCircuit::public_inputs(genesis.pk_p, genesis_outputs, g_board_root, nullifier_root_before)
                .try_into()
                .unwrap();

        let (genesis_vk, genesis_proof, prove_secs, peak_mem_kb) =
            run_step_subprocess::<_, MNT4_753>("genesis", &genesis_circuit);
        let t = Instant::now();
        assert!(cloakkchain_circuit_spend::verify(&genesis_vk, &genesis_public_inputs, &genesis_proof).unwrap());
        let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
        println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
        stats.push(ProveStats {
            name: format!("Genesis mint #{k}"),
            board_size: entries.len() + 1,
            constraints: count_constraints(&genesis_circuit),
            prove_secs,
            verify_ms,
            proof_bytes: ark_serialize_len(&genesis_proof),
            entry_bytes: None,
            peak_mem_kb,
        });

        let (mut tx, s, r) = make_tx(
            k as u64,
            genesis.enc_sk,
            &genesis.sk_p,
            &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice.enc_pk)],
        );
        tx.spend_proof = ark_serialize_bytes(&genesis_proof);
        let entry = cloakkchain_lib::encrypt_tx(&tx, genesis_coin.commitment(), &genesis.sk_p, &r, s);
        let entry_bytes = bincode::serialize(&entry).map(|v| v.len()).ok();
        let entry_position = entries.len();
        entries.push(entry.clone());
        tree.insert(g_own_nullifier);

        let wrap_genesis_circuit = WrapCircuit::<GENESIS_SPEND_PUBLIC_INPUTS> {
            inner_vk: genesis_vk.clone(),
            inner_proof: Some(genesis_proof),
            inner_public_inputs: Some(genesis_public_inputs),
        };
        let (wrap_genesis_vk, wrap_genesis_proof, prove_secs, peak_mem_kb) =
            run_step_subprocess::<_, MNT6_753>("wrap6", &wrap_genesis_circuit);
        let wrap_genesis_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&genesis_public_inputs);
        let t = Instant::now();
        assert!(cloakkchain_circuit_wrap::verify(&wrap_genesis_vk, &wrap_genesis_public_inputs, &wrap_genesis_proof).unwrap());
        let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
        println!("  Wrapped in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
        stats.push(ProveStats {
            name: format!("Wrap genesis mint #{k}"),
            board_size: entries.len(),
            constraints: count_constraints(&wrap_genesis_circuit),
            prove_secs,
            verify_ms,
            proof_bytes: ark_serialize_len(&wrap_genesis_proof),
            entry_bytes,
            peak_mem_kb,
        });

        let receipt_board_root =
            compute_root_from_path(merkle_leaf(entry_position, &entry), entry_position, &g_append_path);
        let (apx, apy) = owner_pk_to_field_pair(&alice.pk_p);
        let receipt_circuit = ReceiptStepCircuit {
            owner_pk_x: Some(apx),
            owner_pk_y: Some(apy),
            coin_commitment: Some(alice_coin.commitment()),
            board_root: Some(receipt_board_root),
            received_at: Some(entry_position as u64),
            wrap_vk: wrap_genesis_vk.clone(),
            wrap_proof: Some(wrap_genesis_proof),
            wrap_public_inputs: Some(genesis_public_inputs),
            entry_nullifier: Some(entry.nullifier),
            entry_output_commitments: Some(genesis_outputs),
            entry_ciphertext_commitment: Some(entry_ciphertext_commitment(&entry)),
            received_slot: Some(entry_position as u64),
            append_path: Some(g_append_path.clone()),
            parent_nonmembership: Some(own_nonmembership),
            nullifier_root_at_parent_slot: Some(nullifier_root_before),
            sk_p: Some(alice.sk_p),
            coin_value: Some(alice_coin.value),
            coin_rand: Some(alice_coin.rand),
        };
        let receipt_public_inputs: [Fr; RECEIPT_PUBLIC_INPUTS] = ReceiptStepCircuit::public_inputs(
            apx,
            apy,
            alice_coin.commitment(),
            receipt_board_root,
            entry_position as u64,
        )
        .try_into()
        .unwrap();

        let (receipt_vk, receipt_proof, prove_secs, peak_mem_kb) =
            run_step_subprocess::<_, MNT4_753>("receipt", &receipt_circuit);
        let t = Instant::now();
        assert!(cloakkchain_circuit_coinproof::verify(&receipt_vk, &receipt_public_inputs, &receipt_proof).unwrap());
        let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
        println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
        stats.push(ProveStats {
            name: format!("Alice's receipt #{k}"),
            board_size: entries.len(),
            constraints: count_constraints(&receipt_circuit),
            prove_secs,
            verify_ms,
            proof_bytes: ark_serialize_len(&receipt_proof),
            entry_bytes: None,
            peak_mem_kb,
        });

        let wrap_receipt_circuit = WrapCircuit::<RECEIPT_PUBLIC_INPUTS> {
            inner_vk: receipt_vk.clone(),
            inner_proof: Some(receipt_proof),
            inner_public_inputs: Some(receipt_public_inputs),
        };
        let (wrap_receipt_vk, wrap_receipt_proof, prove_secs, peak_mem_kb) =
            run_step_subprocess::<_, MNT6_753>("wrap5", &wrap_receipt_circuit);
        let wrap_receipt_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&receipt_public_inputs);
        let t = Instant::now();
        assert!(cloakkchain_circuit_wrap::verify(&wrap_receipt_vk, &wrap_receipt_public_inputs, &wrap_receipt_proof).unwrap());
        let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
        println!("  Wrapped in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
        stats.push(ProveStats {
            name: format!("Wrap Alice's receipt #{k}"),
            board_size: entries.len(),
            constraints: count_constraints(&wrap_receipt_circuit),
            prove_secs,
            verify_ms,
            proof_bytes: ark_serialize_len(&wrap_receipt_proof),
            entry_bytes: None,
            peak_mem_kb,
        });

        wrap_vk_for_spend = Some(wrap_receipt_vk);
        input_receipt_wraps.push((wrap_receipt_proof, receipt_public_inputs.to_vec()));
        alice_inputs.push(AliceInput {
            coin: alice_coin.clone(),
            own_nullifier: poseidon_hash(&[alice_coin.commitment(), fold_owner_scalar(&alice.sk_p)]),
        });
    }

    println!("\n--- Alice spends {MAX_INPUTS} input(s) into {MAX_OUTPUTS} output(s) ---");
    let total: u64 = input_values.iter().sum();
    let bob_val = if MAX_OUTPUTS > 1 { 40 } else { total };
    let bob_coin = coin(0xC0, bob_val, bob.pk_p);
    let mut output_coins_vec: Vec<Coin> = vec![bob_coin.clone()];
    if MAX_OUTPUTS > 1 {
        output_coins_vec.push(coin(0xC1, total - bob_val, alice.pk_p));
    }
    let real_output_commitments: Vec<Fr> = output_coins_vec.iter().map(|c| c.commitment()).collect();
    let spend_outputs = pad_outputs(&real_output_commitments);

    let spend_append_path = append_path_for_next(&entries);
    let spend_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &spend_append_path);
    let nullifier_root_before_spend = tree.root();

    let mut spend_input_coins: [Option<Coin>; MAX_INPUTS] = std::array::from_fn(|_| None);
    let mut spend_nonmembership: [Option<NonMembershipWitness>; MAX_INPUTS] = std::array::from_fn(|_| None);
    for (i, ai) in alice_inputs.iter().enumerate() {
        spend_input_coins[i] = Some(ai.coin.clone());
        spend_nonmembership[i] = Some(tree.prove_non_membership(ai.own_nullifier));
    }
    let mut spend_output_coins: [Option<Coin>; MAX_OUTPUTS] = std::array::from_fn(|_| None);
    for (i, c) in output_coins_vec.iter().enumerate() {
        spend_output_coins[i] = Some(c.clone());
    }
    let mut input_receipt_proofs: [Option<Proof<MNT6_753>>; MAX_INPUTS] =
        std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof()));
    let mut input_receipt_public_inputs: [Option<[Fr; RECEIPT_PUBLIC_INPUTS]>; MAX_INPUTS] =
        std::array::from_fn(|_| None);
    for (i, (proof, pis)) in input_receipt_wraps.into_iter().enumerate() {
        input_receipt_proofs[i] = Some(proof);
        input_receipt_public_inputs[i] = Some(pis.try_into().unwrap());
    }

    let spend_circuit = SpendStepCircuit {
        pk_p: Some(alice.pk_p),
        output_commitments: Some(spend_outputs),
        board_root: Some(spend_board_root),
        current_nullifier_root: Some(nullifier_root_before_spend),
        sk_p: Some(alice.sk_p),
        input_coins: spend_input_coins,
        output_coins: spend_output_coins,
        entry_position: Some(entries.len() as u64),
        append_path: Some(spend_append_path),
        own_nullifier_nonmembership: spend_nonmembership,
        wrap_vk: wrap_vk_for_spend.expect("at least one input coin"),
        input_receipt_proofs,
        input_receipt_public_inputs,
    };
    let spend_public_inputs: [Fr; GENESIS_SPEND_PUBLIC_INPUTS] = SpendStepCircuit::public_inputs(
        alice.pk_p,
        spend_outputs,
        spend_board_root,
        nullifier_root_before_spend,
    )
    .try_into()
    .unwrap();

    let (spend_vk, spend_proof, prove_secs, peak_mem_kb) =
        run_step_subprocess::<_, MNT4_753>("spend_non_genesis", &spend_circuit);
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify_non_genesis(&spend_vk, &spend_public_inputs, &spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");

    let mut spend_outputs_for_tx: Vec<(Coin, [u8; 32])> = vec![(output_coins_vec[0].clone(), bob.enc_pk)];
    if output_coins_vec.len() > 1 {
        spend_outputs_for_tx.push((output_coins_vec[1].clone(), alice.enc_pk));
    }
    let (mut spend_tx, spend_s, spend_r) = make_tx(
        100,
        alice.enc_sk,
        &alice.sk_p,
        &alice_inputs.iter().map(|ai| ai.coin.clone()).collect::<Vec<_>>(),
        &spend_outputs_for_tx,
    );
    spend_tx.spend_proof = ark_serialize_bytes(&spend_proof);
    let spend_entry = cloakkchain_lib::encrypt_tx(
        &spend_tx,
        alice_inputs[0].coin.commitment(),
        &alice.sk_p,
        &spend_r,
        spend_s,
    );
    let spend_entry_bytes = bincode::serialize(&spend_entry).map(|v| v.len()).ok();

    stats.push(ProveStats {
        name: format!("Alice's spend ({MAX_INPUTS}-in-{MAX_OUTPUTS}-out)"),
        board_size: entries.len() + 1,
        constraints: count_constraints(&spend_circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&spend_proof),
        entry_bytes: spend_entry_bytes,
        peak_mem_kb,
    });

    print_prove_table(&stats);
    println!("\n=== Grid cell done: MAX_INPUTS={MAX_INPUTS} MAX_OUTPUTS={MAX_OUTPUTS} ===");
}
