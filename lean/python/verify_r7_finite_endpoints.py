#!/usr/bin/env python3
"""R7 §§9--10: fixed completion identities and every unit Hodge row.

Only the printed finite characters are checked. Counter retains occurrences;
no assertion about Chow realization or arbitrary-conductor exhaustion is made.
The general multiset identities (4),(5) are proved algebraically in Lean.
"""

from collections import Counter
from math import gcd


def fibre(m: int, p: int, c: int) -> tuple[int, ...]:
    assert m % p == 0
    return tuple((c + j * (m // p)) % m for j in range(p))


def standard(m: int, p: int, c: int) -> tuple[int, ...]:
    return fibre(m, p, c) + ((-p * c) % m,)


def check_hodge(m: int, grade: int, a: tuple[int, ...]) -> None:
    assert len(a) == 2 * grade, (m, grade, a)
    assert all(0 < x < m for x in a), (m, a)
    for t in range(m):
        if gcd(t, m) == 1:
            assert sum((t * x) % m for x in a) == grade * m, (m, t, a)


def verify() -> None:
    # R7 §9.1, lines 1486--1491; standard-five is Lemma 3.2 with d=3,a=1.
    a15 = (1, 2, 7, 11, 12, 12)
    s15 = (1, 4, 7, 10, 10, 13)
    assert Counter(a15 + (6, 9)) == Counter(standard(15, 3, 2) + standard(15, 3, 6))
    assert Counter(s15) == Counter(standard(15, 5, 1))
    for a in (a15, s15):
        check_hodge(15, 3, a)
    for a in (standard(15, 3, 2), standard(15, 3, 6)):
        check_hodge(15, 2, a)
    print("level15: occurrence identity and standard-five; all 8 unit rows PASS")

    # R7 §9.2, lines 1517--1520; all three p in the definition at 1493--1495.
    for p in (7, 11, 13):
        m = 3 * p
        q = (1, 1 + p, 1 + 2 * p, 3 + p, 3 + 2 * p, 3 * p - 9)
        assert Counter(q + (3, m - 3)) == Counter(standard(m, 3, 1) + standard(m, 3, 3))
        check_hodge(m, 3, q)
        for a in (standard(m, 3, 1), standard(m, 3, 3)):
            check_hodge(m, 2, a)
        print(f"Q_{p}: C(1)+C(3) identity and all unit rows PASS")

    # R7 §9.2, lines 1525--1530; each occurrence and both zero sums retained.
    split_rows = (
        (21, (1, 4, 9, 15, 16, 18), (1, 4, 16), (9, 15, 18)),
        (21, (1, 4, 10, 13, 16, 19), (1, 4, 16), (10, 13, 19)),
        (39, (1, 7, 16, 22, 34, 37), (1, 16, 22), (7, 34, 37)),
        (39, (1, 14, 16, 22, 29, 35), (1, 16, 22), (14, 29, 35)),
    )
    for m, a, left, right in split_rows:
        assert len(left) == len(right) == 3
        assert sum(left) % m == sum(right) % m == 0
        assert Counter(a) == Counter(left + right)
        check_hodge(m, 3, left + right)
        print(f"split level{m} {a}: two zero-sum triples and all unit rows PASS")

    # R7 §10, line 1622, completed using Lemma 3.3, lines 568--574, equation (5).
    a105 = (3, 24, 50, 66, 85, 87)
    l105 = fibre(105, 5, 3)
    assert l105 == (3, 24, 45, 66, 87)
    assert 3 % (105 // 5) != 0 and 45 in l105
    four_points = Counter(l105)
    four_points.subtract((45,))
    assert sum(four_points.values()) == 4
    assert Counter(a105) == four_points + Counter((50, 85))
    s105 = standard(105, 5, 3)
    b105 = (15, 50, 85, 60)
    assert s105 == (3, 24, 45, 66, 87, 90)
    check_hodge(105, 3, a105)
    check_hodge(105, 3, s105)
    check_hodge(105, 2, b105)
    assert (45 + 60) % 105 == (15 + 90) % 105 == 0
    assert Counter(a105 + (45, 60) + (15, 90)) == Counter(s105 + b105)
    print("level105: L_5(3)-{45}+{50,85}; S=(3,24,45,66,87,90); B=(15,50,85,60)")
    print("level105: nonzero entries, lengths 6/6/4, all 48 unit rows, equation (5) PASS")
    print("R7_FINITE_ENDPOINTS=PASS")


if __name__ == "__main__":
    verify()
