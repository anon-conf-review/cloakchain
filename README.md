# CloakChain (mnt-native)

CloakChain is a privacy-preserving coin system built on real, native Groth16
recursion over the MNT4-753/MNT6-753 pairing-friendly curve cycle (no zkVM,
no SP1 — proving happens directly against `ark-groth16` circuits written
with `ark-relations`/`ark-r1cs-std`).

This branch demonstrates a full genesis -> Alice -> Bob -> Carol coin chain:
a genesis mint, a receipt circuit that recursively verifies the wrapped
genesis proof, a 1-in/2-out spend (with real value conservation, not just
equality), a second-generation receipt, and a follow-on spend — nine real
Groth16 proofs end to end.

## Requirements

- [Rust](https://rustup.rs/) — the pinned toolchain in `rust-toolchain` is
  installed automatically by `rustup` the first time you build.
- A machine with enough RAM/CPU to run native Groth16 setup+prove over
  753-bit MNT curves. This is heavier than SNARK-friendly-curve toy demos;
  budget real time and memory headroom, particularly for `--prove`.

No SP1, no GPU, and no external prover network are required.

## Workspace layout

- `lib/` — shared types: coins, board entries, the nullifier tree, Poseidon
  hashing, Merkle path helpers.
- `circuit-spend/` — the genesis-mint and spend (input/output) circuits.
- `circuit-coinproof/` — the receipt circuit that recursively verifies a
  wrapped proof to establish coin ownership.
- `circuit-wrap/` — the MNT4/MNT6 recursion-wrapping circuit.
- `script/` — the `cloakkchain` binary that drives the demo chain.

## Building

```sh
cargo build --release
```

## Running

### Cheap sanity check (no proving)

Builds the genesis-mint witness and checks it satisfies the circuit's
constraints. This is the only circuit in the chain that doesn't recursively
verify another proof, so it's the only step a no-proving mode can check in
isolation.

```sh
RUST_LOG=info cargo run --release -- --execute
```

### Full chain, real proofs

Runs the whole genesis -> Alice -> Bob -> Carol chain, once, in order —
nine real Groth16 proofs. Each step's setup+prove is farmed out to a fresh
subprocess so the reported peak-memory figure reflects that step's own
footprint (via the kernel's `VmHWM`) rather than a same-process running
high-water mark.

```sh
RUST_LOG=info cargo run --release -- --prove
```

### Grid-cell benchmarking (ad hoc)

Runs a single real Groth16 setup+prove+verify at whichever
`MAX_INPUTS`/`MAX_OUTPUTS` shape `circuit-spend`/`circuit-coinproof` are
currently compiled with. Used for filling in benchmark grid cells; not part
of the normal demo.

```sh
cargo run --release -- --grid-cell
```

> The `--internal-kind`/`--internal-witness`/`--internal-output` flags are
> hidden/internal — they're how the binary re-invokes itself as a single
> setup+prove subprocess for `--prove` and `--grid-cell`, and aren't meant
> for direct use.

## Tests

```sh
cargo test --release
```
