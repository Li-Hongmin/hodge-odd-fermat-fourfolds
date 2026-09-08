#!/usr/bin/env python3
"""Exact finite checks for reconstruction §12; integer arithmetic only.

U25: all odd integral v with ||v||_1 in {2,4,6}, and all four signed
J5-fibre corrections. Half-integral potentials: doubled odd u, p=7,11,13,
with sum of absolute values on the positive half <=6; both signs of 2c=1.
The latter bound follows from the first term of equation (15), not from
the claimed classification. No quotient by signs or unit action is taken.
"""

from collections import Counter
from itertools import combinations_with_replacement
from math import gcd
import ast
from pathlib import Path
import sys

from verify_pure_small_exception_levels import (
    EXCEPTIONS, canonical_orbit, is_dec_free, is_hodge, quasi_representative, units,
)


def integer_ball(n, budget):
    if n == 0:
        yield ()
    else:
        for x in range(-budget, budget + 1):
            for rest in integer_ball(n - 1, budget - abs(x)):
                yield (x,) + rest


def odd_function(m, values):
    half = [x for x in range(1, (m + 1) // 2) if gcd(x, m) == 1]
    assert len(values) == len(half)
    f = dict(zip(half, values))
    f.update({m - x: -f[x] for x in half})
    return f


def check_tuples():
    for m, raw, orbit_count in [(15, 6, 2), (21, 12, 3), (33, 14, 2), (39, 24, 3)]:
        us = units(m)
        table = []
        for head in combinations_with_replacement(range(1, m), 5):
            tail = 3 * m - sum(head)
            if head[-1] <= tail < m:
                a = head + (tail,)
                if is_dec_free(a, m) and is_hodge(a, m, us):
                    table.append(a)
        representatives = ([(1, 2, 7, 11, 12, 12), (1, 4, 7, 10, 10, 13)] if m == 15
                           else [quasi_representative(m // 3), *EXCEPTIONS[m // 3].values()])
        found = {canonical_orbit(a, m, us) for a in table}
        assert len(table) == raw and len(found) == orbit_count
        assert found == {canonical_orbit(a, m, us) for a in representatives}
        print(f"level{m}: {list(map(list, table))}")
        print(f"level{m}: raw={raw} orbits={orbit_count} PASS")


def check_corrections():
    us = units(25)
    corrections = [{x: int(x % 5 == z) - int(x % 5 == 5 - z) for x in us}
                   for z in (1, 2, 3, 4)]
    assert len({tuple(c.values()) for c in corrections}) == 4
    counts, minima = Counter(), {}
    for values in integer_ball(10, 3):
        k = 2 * sum(map(abs, values))
        if not k:
            continue
        v = odd_function(25, values)
        g = {x: v[3 * x % 25] - v[x] for x in us}
        for c in corrections:
            overlap = sum(abs(g[x]) for x in us if c[x])
            d = sum(abs(c[x] + g[x]) for x in us)
            assert overlap <= k and d + k >= 10
            assert k != 2 or d >= 10
            assert 2 * k + d > 12
            counts[k] += 1
            minima[k] = min(minima.get(k, 100), 2 * k + d)
    assert dict(counts) == {2: 80, 4: 800, 6: 5360}
    assert minima == {2: 14, 4: 14, 6: 18}
    print(f"U25: pairs={sum(counts.values())} by_norm={sorted(counts.items())} minima={sorted(minima.items())} PASS")


def check_half_potentials():
    for p, expected in [(7, {4: 12, 6: 4}), (11, {5: 4}), (13, {6: 8})]:
        tested, found = 0, Counter()
        for values in integer_ball((p - 1) // 2, 6):
            if any(x % 2 != 1 for x in values):
                continue
            u = odd_function(p, values)  # values encode 2u
            for c in (-1, 1):  # encodes 2c; both signs retained
                tested += 1
                variation = sum(abs(u[3 * x % p] - u[x]) for x in range(1, (p + 1) // 2))
                twice_energy = 2 * sum(max(abs(x), abs(c)) for x in values) + variation
                if twice_energy <= 12:
                    assert abs(c) == 1 and all(abs(x) == 1 for x in values)
                    assert twice_energy % 2 == 0
                    if p != 7:
                        assert all(u[3 * x % p] == u[x] for x in u)
                    found[twice_energy // 2] += 1
        assert found == expected
        print(f"half p={p}: bounded_pairs={tested} energies={sorted(found.items())} PASS")


if __name__ == "__main__" and sys.argv[1:2] == ["--compare-lean"]:
    def tables(path):
        return {line.split(": ", 1)[0]: ast.literal_eval(line.split(": ", 1)[1])
                for line in Path(path).read_text().splitlines()
                if line.startswith("level") and ": [[" in line}
    python_tables, lean_tables = map(tables, sys.argv[2:4])
    assert set(python_tables) == {"level15", "level21", "level33", "level39"}
    assert python_tables == lean_tables
    print("Python/Lean: all four complete ordered tuple tables are identical PASS")
elif __name__ == "__main__":
    check_tuples()
    check_corrections()
    check_half_potentials()
    print("reconstruction_finite=PASS")
