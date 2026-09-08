#!/usr/bin/env python3
"""Exact finite classification of the pure m=3p exception levels.

For m=3p with p=7,11,13 this streams all sorted sextuples whose t=1
residue sum is 3m, removes opposite-pair tuples, and checks every unit row.
It then compares the surviving U_m-orbits with the quasi orbit and the
listed split/Aoki exceptional orbits.

This closes only the finite effective-level exception after the energy and
ambient-transport argument has reduced to p in {7,11,13}. It does not verify
the arbitrary-M reduction.
"""

from itertools import combinations_with_replacement
from math import gcd


def units(m: int) -> tuple[int, ...]:
    return tuple(t for t in range(1, m) if gcd(t, m) == 1)


def canonical_orbit(
    a: tuple[int, ...], m: int, us: tuple[int, ...]
) -> tuple[int, ...]:
    return min(tuple(sorted((t * x) % m for x in a)) for t in us)


def is_dec_free(a: tuple[int, ...], m: int) -> bool:
    support = set(a)
    return all((m - x) % m not in support for x in support)


def is_hodge(a: tuple[int, ...], m: int, us: tuple[int, ...]) -> bool:
    return all(sum((t * x) % m for x in a) == 3 * m for t in us)


def quasi_representative(p: int) -> tuple[int, ...]:
    return (1, 1 + p, 1 + 2 * p, 3 + p, 3 + 2 * p, 3 * p - 9)


EXCEPTIONS = {
    7: {
        "split-full-21": (1, 4, 10, 13, 16, 19),
        "split-7-21": (1, 4, 9, 15, 16, 18),
    },
    11: {
        "aoki-33": (1, 4, 16, 22, 25, 31),
    },
    13: {
        "split-full-39-a": (1, 7, 16, 22, 34, 37),
        "split-full-39-b": (1, 14, 16, 22, 29, 35),
    },
}


def enumerate_orbits(p: int) -> tuple[int, set[tuple[int, ...]]]:
    m = 3 * p
    us = units(m)
    survivors: set[tuple[int, ...]] = set()
    raw = 0

    # A sorted sextuple is uniquely determined by its first five entries and
    # sum(a_i)=3m. This streams the search without materializing the O(m^6)
    # ambient box.
    for head in combinations_with_replacement(range(1, m), 5):
        tail = 3 * m - sum(head)
        if tail < head[-1] or tail >= m:
            continue
        a = head + (tail,)
        if not is_dec_free(a, m):
            continue
        if not is_hodge(a, m, us):
            continue
        raw += 1
        survivors.add(canonical_orbit(a, m, us))
    return raw, survivors


def main() -> None:
    for p in (7, 11, 13):
        m = 3 * p
        us = units(m)
        raw, found = enumerate_orbits(p)
        expected = {
            canonical_orbit(quasi_representative(p), m, us): "quasi"
        }
        for label, rep in EXCEPTIONS[p].items():
            expected[canonical_orbit(rep, m, us)] = label

        assert found == set(expected), (p, found, expected)
        print(
            f"p={p} m={m} decfree_hodge_tuples={raw} "
            f"orbits={len(found)} labels={','.join(sorted(expected.values()))}"
        )
    print("pure_exception_levels=PASS")


if __name__ == "__main__":
    main()

