"""The block proof `export_python_vectors` writes: a leaf of the mixed guest aggregating one leanSPHINCS signature."""

from pathlib import Path

import pytest

from leanvm_verifier import Digest, E, Proof, verify_execution
from leanvm_verifier.eip8288_mixed import decode_payload, deferred_cells, guest_bytecode, guest_key, statement, verify_dependencies

VECTORS = Path(__file__).parent / "vectors"


def vector(name: str) -> bytes:
    return (VECTORS / f"{name}.bin").read_bytes()


def test_guest_key_matches_rust() -> None:
    assert guest_key() == vector("guest_key")


def test_deferred_cells_and_statement_match_rust() -> None:
    point, matrix_points, _ = decode_payload(vector("payload"))
    cells = deferred_cells(guest_bytecode(), point, matrix_points)
    assert b"".join(cell.to_bytes() for cell in cells) == vector("cells")
    assert statement(guest_bytecode(), vector("deps_hash"), cells).value == vector("public_input")


def test_block_proof_verifies() -> None:
    assert verify_dependencies(vector("deps_hash"), vector("payload"))


def test_raw_proof_verifies() -> None:
    """The same proof as `RawProof` lays it out, the form `python_verifier.rs` hands the command line."""
    stream = vector("stream")
    proof = Proof(tuple(E.from_bytes(stream[at : at + 24]) for at in range(0, len(stream), 24)), vector("merkle_openings"))
    verify_execution(guest_bytecode(), Digest(vector("public_input")), proof)


def flip(at: int) -> object:
    return lambda payload: payload[:at] + bytes([payload[at] ^ 1]) + payload[at + 1 :]


@pytest.mark.parametrize(
    "tamper",
    [
        pytest.param(lambda payload: payload[:-1], id="truncated"),
        pytest.param(lambda payload: payload + b"\0", id="trailing_byte"),
        pytest.param(flip(100), id="bytecode_point"),
        pytest.param(lambda payload: flip(len(payload) // 2)(payload), id="merkle_opening"),
    ],
)
def test_tampered_payload_rejected(tamper) -> None:
    assert not verify_dependencies(vector("deps_hash"), tamper(vector("payload")))


def test_other_dependencies_rejected() -> None:
    assert not verify_dependencies(bytes(32), vector("payload"))
