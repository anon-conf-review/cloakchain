# CloakChain

CloakChain is a privacy-preserving coin system built on real, native Groth16
recursion over the MNT4-753/MNT6-753 pairing-friendly curve cycle.

## Requirements

- [Rust](https://rustup.rs/) — the pinned toolchain in `rust-toolchain` is
  installed automatically by `rustup` the first time you build.
- A machine with enough RAM/CPU to run native Groth16 setup+prove over
  753-bit MNT curves.

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

Runs the whole genesis -> Alice -> Bob -> Carol chain, once, in order. 
Each step's setup+prove is farmed out to a fresh
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

## Tests

```sh
cargo test --release
```
