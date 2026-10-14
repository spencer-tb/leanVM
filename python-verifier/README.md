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
