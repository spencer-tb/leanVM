# leanvm-verifier

A dependency-free Python verifier for leanVM execution proofs, written to be read next to `doc/leanvm`. It is pinned
against the Rust verifier by `crates/lean_vm/tests/verifiers/python_verifier.rs`.

- `leanvm_verifier.verifier`: the protocol. `verify_execution(bytecode, public_input, proof)` raises
  `VerificationError` on an invalid proof. A `Proof`'s Merkle openings come either as `RawProof` lays them out or as
  transmitted (pruned).
- `leanvm_verifier.eip8288_mixed`: EIP-8288 block proofs under the mixed recursive guest.
  `verify_dependencies(deps_hash, payload)` mirrors `rec_aggregation::eip8288_mixed::verify_mixed_deps`, and
  `guest_key()` is the guest's verification key.

```sh
uv run --group test pytest                                         # the test vectors
uv run leanvm-verify bytecode.bin public_input.bin stream.bin merkle_openings.bin
```

The guest's bytecode table and the test vectors come from Rust:

```sh
EXPORT_DIR=out cargo test --release -p rec_aggregation --features eip8288-mixed --lib export_python_vectors -- --ignored
xz -9e -k out/bytecode.bin   # eip8288_mixed_guest_bytecode.bin.xz, after checking its BLAKE2s
```

`export_eip8288_test_proofs` proves block proofs for consumers' test suites: every file in `EXPORT_REQUESTS` lists one
block's dependencies, a hex line of 96 bytes each, and each block's proof lands in `EXPORT_DIR` as `<deps_hash>.bin`,
signed by the 16 test keys it also writes (`keys.bin`).

## Speed

The protocol code reads as the document does; the arithmetic under it is where the time goes, so that is what is tuned.
An extension element is one integer with its limbs 128 bits apart, a product is one integer multiplication of the two
operands with every bit spread into its own byte (`_clmul`), and sums of products are reduced once. A block proof
verifies in about 2.5 to 4 seconds on CPython 3.14 (an Apple M-series core), against 20 to 40 before.
