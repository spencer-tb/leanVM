"""EIP-8288 block proofs: a proof, under the mixed recursive guest, that every dependency a block declares was verified.

The guest is one self-recursive program (`rec_aggregation::eip8288_mixed`). A leaf verifies leanSPHINCS signatures, a
parent its children's proofs, and every node defers three fixed-polynomial evaluations (its bytecode table and each hash
circuit's matrices) to whoever verifies it. A block carries only the root: the deferred points and the leanVM proof. Its
statement binds the guest's key, the block's dependency digest and the deferred claims, which `verify_dependencies`
evaluates itself, as `verify_mixed_deps` does."""

from __future__ import annotations

import hashlib
import lzma
from collections.abc import Sequence
from functools import cache
from importlib.resources import files
from struct import pack, unpack_from

from .verifier import (
    FLOCK_CIRCUITS,
    TABLES,
    ZERO,
    BytecodeTable,
    Digest,
    E,
    MerklePhase,
    Proof,
    VerificationError,
    build_layout,
    bus_layout,
    dot,
    eq_kernel,
    fiat_shamir_iv,
    require,
    verify_execution,
)

GUEST_BYTECODE = "eip8288_mixed_guest_bytecode.bin.xz"  # `mixed_table()`, xz-compressed
GUEST_BYTECODE_DIGEST = bytes.fromhex("e1db0f41bbc80aca355fd77e2c731065029e38f0dd8db5b600d63459b0be5099")  # BLAKE2s, uncompressed

# `preflight_payload`'s bounds, each checked before what it counts is read.
MAX_PAYLOAD_BYTES = 8 * 1024 * 1024
MAX_POINT_LENGTH = 32
STREAM_CAP = 8192
MAX_PHASES = 128
MAX_ROWS_PER_PHASE = 4096
MAX_ROW_ALLOCATION = 32 * 1024 * 1024

# The recursion profile (`recursion_supported`): the shapes the guest can verify, and so the only ones a root may take.
MAX_MIXED_COMMITTED_LOG = 27
MAX_MIXED_BUS_LOG = 26
MIN_COMMITTED_LOG = 15
LOG_INV_RATE = 1


@cache
def guest_bytecode() -> BytecodeTable:
    """The guest's bytecode table, checked against its pinned digest."""
    data = lzma.decompress(files(__package__).joinpath(GUEST_BYTECODE).read_bytes())
    require(hashlib.blake2s(data).digest() == GUEST_BYTECODE_DIGEST, "guest bytecode does not match its digest")
    return BytecodeTable(data)


@cache
def guest_key() -> bytes:
    """The guest's verification key: the seed its transcripts start from (`mixed_guest_key`)."""
    return fiat_shamir_iv(guest_bytecode()).value


class PayloadReader:
    """Fixed-integer bincode, as `preflight_payload` walks it: every count bounded before what it counts is read."""

    def __init__(self, data: bytes) -> None:
        self.data = data
        self.offset = 0

    def take(self, length: int) -> bytes:
        end = self.offset + length
        require(end <= len(self.data), "proof payload truncated")
        chunk = self.data[self.offset : end]
        self.offset = end
        return chunk

    def count(self, maximum: int, width: int) -> int:
        (count,) = unpack_from("<Q", self.take(8))
        require(count <= maximum and count <= (len(self.data) - self.offset) // width, "proof payload count out of bounds")
        return count

    def elements(self, maximum: int) -> list[E]:
        return [E.from_bytes(self.take(24)) for _ in range(self.count(maximum, 24))]


def decode_payload(payload: bytes) -> tuple[list[E], tuple[list[E], list[E]], Proof]:
    """`(Vec<F192>, [Vec<F192>; 2], cpu::Proof)`: the bytecode point, the two matrix points, then the proof."""
    require(len(payload) <= MAX_PAYLOAD_BYTES, "proof payload too large")
    reader = PayloadReader(payload)
    point = reader.elements(MAX_POINT_LENGTH)
    matrix_points = (reader.elements(MAX_POINT_LENGTH), reader.elements(MAX_POINT_LENGTH))
    stream = tuple(reader.elements(STREAM_CAP))
    phases = []
    allocation = 0
    for _ in range(reader.count(MAX_PHASES, 16)):
        row_count = reader.count(MAX_ROWS_PER_PHASE, 8)
        allocation += row_count * 24
        require(allocation <= MAX_ROW_ALLOCATION, "proof payload has too many rows")
        rows = []
        for _ in range(row_count):
            words = reader.count(MAX_PAYLOAD_BYTES // 8, 8)
            rows.append(unpack_from(f"<{words}Q", reader.take(8 * words)))
        siblings = tuple(reader.take(32) for _ in range(reader.count(MAX_PAYLOAD_BYTES // 32, 32)))
        phases.append(MerklePhase(tuple(rows), siblings))
    require(reader.offset == len(payload), "proof payload has trailing bytes")
    return point, matrix_points, Proof(stream, tuple(phases))


def recursion_supported(bytecode: BytecodeTable, stream: Sequence[E]) -> bool:
    """The announced shape is one the guest verifies: small canonical sizes, the profile's rate, and committed stack and
    bus trees within its bounds."""
    if not len(TABLES) + 2 <= len(stream) <= STREAM_CAP:
        return False
    announced, rate = stream[: len(TABLES) + 1], stream[len(TABLES) + 1]
    if any(value.c1 or value.c2 or int(value.c0) > 32 for value in announced) or rate != E(LOG_INV_RATE):
        return False
    layout = build_layout(bytecode, int(announced[0].c0), [int(value.c0) for value in announced[1:]])
    framework = (0, layout.log_memory, layout.log_bytecode)
    depths = (bus_layout(framework, layout.push).depth, bus_layout(framework, layout.pull).depth, bus_layout((), layout.count).depth)
    return MIN_COMMITTED_LOG <= layout.stack_log <= MAX_MIXED_COMMITTED_LOG and all(depth <= MAX_MIXED_BUS_LOG for depth in depths)


def deferred_cells(bytecode: BytecodeTable, point: Sequence[E], matrix_points: tuple[Sequence[E], Sequence[E]]) -> list[E]:
    """The root's deferred claims, evaluated, in the order the statement absorbs them: the bytecode point and value, then
    each circuit's point and its A0 and B0 values (`DeferredClaim::cells`)."""
    require(2 ** len(point) == len(bytecode), "deferred bytecode point has the wrong length")
    cells = [*point, E(bytecode.words[0]) if all(coordinate == ZERO for coordinate in point) else bytecode.evaluate(point)]
    for circuit, matrix_point in zip(FLOCK_CIRCUITS, matrix_points, strict=True):
        size = circuit.log_size
        require(len(matrix_point) == 2 * size, "deferred matrix point has the wrong length")
        row_weights = eq_kernel(matrix_point[:size])
        a_values, b_values = circuit.row_values(eq_kernel(matrix_point[size:]))
        cells += [*matrix_point, dot(row_weights, a_values), dot(row_weights, b_values)]
    return cells


def statement(bytecode: BytecodeTable, deps_hash: bytes, cells: Sequence[E]) -> Digest:
    """The root's public input (`mixed_statement`): the guest's seed and the dependency digest as two-limb cells, then
    every limb of each deferred claim, BLAKE2s over the lanes padded to a whole block."""
    header = (*fiat_shamir_iv(bytecode).halves(), *Digest(deps_hash).halves(), ZERO, ZERO)
    lanes = [limb for cell in header for limb in (cell.c0, cell.c1)]
    lanes += [limb for cell in [*cells, *[ZERO] * (len(cells) % 2)] for limb in (cell.c0, cell.c1, cell.c2)]
    data = pack(f"<{len(lanes)}Q", *lanes)
    return Digest(hashlib.blake2s(data + bytes(-len(data) % 64)).digest())


def verify_dependencies(deps_hash: bytes, payload: bytes) -> bool:
    """Whether `payload` proves, under the guest, exactly the dependencies `deps_hash` commits to (`verify_mixed_deps`)."""
    bytecode = guest_bytecode()
    try:
        point, matrix_points, proof = decode_payload(payload)
        if not recursion_supported(bytecode, proof.stream):
            return False
        verify_execution(bytecode, statement(bytecode, deps_hash, deferred_cells(bytecode, point, matrix_points)), proof)
    except (VerificationError, ValueError, KeyError, IndexError):
        return False
    return True
