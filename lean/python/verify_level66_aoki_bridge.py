"""Exact finite certificate for the exceptional level-33 block via level 66.

This script checks only the finite character arithmetic used to instantiate
Aoki (1987), Theorem 1-4(i),(ii).  The geometric implication is the cited
published theorem, not a claim proved by this script.
"""

from collections import Counter
from math import gcd


M = 66
UNITS = tuple(t for t in range(1, M) if gcd(t, M) == 1)

w = (1, 4, 16, 22, 25, 31)
a = tuple((2 * x) % M for x in w)
Q = (1, 25, 44, 62)
S = (2, 8, 32, 41, 50, 65)
delta0 = (1, 65, 25, 41)
beta = (2, 32, 33, 65)
gamma = (8, 33, 41, 50)
delta1 = (33, 33)


def hodge_sum(character):
    """Return the numerator of sum_i <t*a_i/M> for every unit t."""
    return tuple(sum((t * x) % M for x in character) for t in UNITS)


assert len(UNITS) == 20
for character, length in ((a, 6), (S, 6), (Q, 4), (beta, 4), (gamma, 4)):
    assert len(character) == length and all(0 < x < M for x in character)
assert hodge_sum(a) == (3 * M,) * len(UNITS)       # fourfold, (2,2)
for surface_character in (Q, beta, gamma):
    assert hodge_sum(surface_character) == (2 * M,) * len(UNITS)
assert hodge_sum(S) == (3 * M,) * len(UNITS)

assert Counter(a) + Counter(delta0) == Counter(Q) + Counter(S)
assert Counter(S) + Counter(delta1) == Counter(beta) + Counter(gamma)


def is_self_pair(x, y):
    return 0 < x < M and 0 < y < M and (x + y) % M == 0


assert is_self_pair(1, 65)
assert is_self_pair(25, 41)
assert is_self_pair(33, 33)  # the level-66 order-two self-pair

# R7 §9.2 uses this inflation, with every multiplicity retained.
assert a == (2, 8, 32, 44, 50, 62)

# For pi : X_66^4 -> X_33^4, the quotient is mu_2^6/mu_2,diag.
quotient_signs = {
    tuple(e ^ bits[0] for e in bits)
    for bits in __import__("itertools").product((0, 1), repeat=6)
}
assert len(quotient_signs) == 32
# A sign change acts on a character by (-1)^(e_i*a_i); a is even coordinatewise.
for signs in quotient_signs:
    assert sum(sign * coordinate for sign, coordinate in zip(signs, a)) % 2 == 0

print("units mod 66:", len(UNITS))
print("Hodge checks: a,S=(2,2) on X_66^4; Q,beta,gamma=(1,1) on surfaces")
print("multiset bridges: a+delta0=Q+S; S+delta1=beta+gamma")
print("self-pairs: delta0 and delta1 valid")
print("quotient group size:", len(quotient_signs))
print("target inflation: a = 2*w mod 66")
print("ALL ASSERTIONS PASSED")
