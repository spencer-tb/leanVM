"""The fast arithmetic against the textbook one: shift-and-add products, schoolbook extension products, full kernels."""

import random
from array import array

import pytest

from leanvm_verifier.verifier import ONE, BytecodeTable, E, K, dot, eq_kernel, multilinear_eval, outer_product, tensor_dot

WORD = 2**64 - 1
EDGES = (0, 1, 2, WORD, 2**63, 0x1B, WORD ^ 1)


def k_mul(left: int, right: int) -> int:
    """Shift and add, then fold by x^64 = x^4 + x^3 + x + 1."""
    product = 0
    for bit in range(64):
        if right >> bit & 1:
            product ^= left << bit
    for bit in range(127, 63, -1):
        if product >> bit & 1:
            product ^= (1 << bit) ^ (0b11011 << (bit - 64))
    return product


def e_mul(left: tuple[int, int, int], right: tuple[int, int, int]) -> tuple[int, int, int]:
    """Schoolbook over K, then y^3 = y + 1 and y^4 = y^2 + y."""
    p = [0] * 5
    for i in range(3):
        for j in range(3):
            p[i + j] ^= k_mul(left[i], right[j])
    return (p[0] ^ p[3], p[1] ^ p[3] ^ p[4], p[2] ^ p[4])


def limbs(value: E) -> tuple[int, int, int]:
    return (value.c0.value, value.c1.value, value.c2.value)


def random_e(rng: random.Random) -> E:
    return E(*(rng.choice(EDGES) if rng.random() < 0.2 else rng.getrandbits(64) for _ in range(3)))


def naive_kernel(point: list[E]) -> list[E]:
    weights = []
    for index in range(2 ** len(point)):
        weight = ONE
        for bit, r in enumerate(point):
            weight = weight * (r if index >> bit & 1 else ONE + r)
        weights.append(weight)
    return weights


@pytest.fixture
def rng() -> random.Random:
    return random.Random(8288)


def test_k_products(rng: random.Random) -> None:
    pairs = [(a, b) for a in EDGES for b in EDGES] + [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(2000)]
    for a, b in pairs:
        assert (K(a) * K(b)).value == k_mul(a, b)


def test_e_products(rng: random.Random) -> None:
    edge = E(WORD, WORD, WORD)
    for left, right in [(edge, edge), (edge, ONE)] + [(random_e(rng), random_e(rng)) for _ in range(1000)]:
        assert limbs(left * right) == e_mul(limbs(left), limbs(right))
        assert limbs(left * right.c0) == e_mul(limbs(left), (right.c0.value, 0, 0))


def test_inverse(rng: random.Random) -> None:
    for _ in range(5):
        value = random_e(rng) or ONE
        assert value * value.inv() == ONE


def test_sums(rng: random.Random) -> None:
    outer, inner = [random_e(rng) for _ in range(8)], [random_e(rng) for _ in range(5)]
    tensor = [o * i for o in outer for i in inner]
    values = [random_e(rng) if index % 3 else K(rng.getrandbits(64)) for index in range(40)]
    expected = E.sum(E.lift(x) * y for x, y in zip(tensor, values))
    assert dot(tensor, values) == expected
    assert tensor_dot(outer, inner, values) == expected
    assert outer_product(outer, inner) == tensor


@pytest.mark.parametrize("variables", [0, 1, 5, 9])
def test_kernels(rng: random.Random, variables: int) -> None:
    point = [random_e(rng) for _ in range(variables)]
    values = [random_e(rng) for _ in range(2**variables)]
    kernel = naive_kernel(point)
    assert eq_kernel(point) == kernel
    assert multilinear_eval(values, point) == E.sum(w * v for w, v in zip(kernel, values))


@pytest.mark.parametrize("variables", [3, 13])
def test_bytecode_table(rng: random.Random, variables: int) -> None:
    """Mostly zero words, a few repeated ones, as a program's table is."""
    common = [rng.getrandbits(64) for _ in range(6)] + [1, 4, 0x4000, WORD]
    words = array("Q", (0 if rng.random() < 0.7 else rng.choice(common) if rng.random() < 0.8 else rng.getrandbits(64) for _ in range(2**variables)))
    table = BytecodeTable(words.tobytes())
    point = [random_e(rng) for _ in range(variables)]
    assert table.evaluate(point) == multilinear_eval([K(word) for word in words], point)
