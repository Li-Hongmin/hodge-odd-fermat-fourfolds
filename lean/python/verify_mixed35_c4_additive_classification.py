#!/usr/bin/env python3
"""Exact certificate for the local U_3 x U_5 additive-matrix classes.

The columns are ordered by the multiplication-by-3 cycle

    (1, 3, 4, 2) in U_5.

Consequently the geometric relabelling group on columns is C4, not S4.  The
certificate classifies every nonzero integer 2 x 4 matrix M with

    M[i,j] = u[i] + v[j],              ||M||_1 <= 6,

modulo row swap, cyclic column rotation, and global coefficient sign.

Only Python integer arithmetic and finite exhaustive enumeration are used.
"""

from __future__ import annotations

from collections import Counter
from hashlib import sha256
from itertools import permutations, product
import json
from typing import Iterator, TypeAlias


BOUND = 6
ROWS = 2
COLS = 4
U5_TIMES_THREE_CYCLE = (1, 3, 4, 2)
EXPECTED_PAYLOAD_SHA256 = (
    "6884de68c535501c5d08250dbb0d297fda791e05c767291166bce208600127dd"
)

FlatMatrix: TypeAlias = tuple[int, ...]


def l1_norm(vector: FlatMatrix) -> int:
    return sum(abs(entry) for entry in vector)


def integer_l1_ball(length: int, bound: int) -> Iterator[FlatMatrix]:
    """Yield every integer vector of the given length and l1 norm <= bound."""

    prefix = [0] * length

    def recurse(position: int, remaining: int) -> Iterator[FlatMatrix]:
        if position == length:
            yield tuple(prefix)
            return
        for entry in range(-remaining, remaining + 1):
            prefix[position] = entry
            yield from recurse(position + 1, remaining - abs(entry))

    yield from recurse(0, bound)


def is_additive(matrix: FlatMatrix) -> bool:
    """Test M[i,j] = u[i] + v[j] by the three additive 2 x 2 minors."""

    assert len(matrix) == ROWS * COLS
    return all(
        matrix[COLS + column] - matrix[COLS]
        == matrix[column] - matrix[0]
        for column in range(1, COLS)
    )


def transform(
    matrix: FlatMatrix,
    row_order: tuple[int, int],
    column_order: tuple[int, ...],
    coefficient_sign: int,
) -> FlatMatrix:
    return tuple(
        coefficient_sign * matrix[COLS * row + column]
        for row in row_order
        for column in column_order
    )


def cyclic_column_orders() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple((column + shift) % COLS for column in range(COLS))
        for shift in range(COLS)
    )


def canonical_c4(matrix: FlatMatrix) -> FlatMatrix:
    """Canonicalize by C2(row) x C4(column) x C2(global sign)."""

    return min(
        transform(matrix, rows, columns, sign)
        for rows in ((0, 1), (1, 0))
        for columns in cyclic_column_orders()
        for sign in (1, -1)
    )


def canonical_s4_diagnostic(matrix: FlatMatrix) -> FlatMatrix:
    """Deliberately stronger, inadmissible S4 quotient used only as a warning."""

    return min(
        transform(matrix, rows, columns, sign)
        for rows in ((0, 1), (1, 0))
        for columns in permutations(range(COLS))
        for sign in (1, -1)
    )


def enumerate_from_l1_ball() -> tuple[set[FlatMatrix], int, int]:
    """Primary exhaustive enumeration in the full eight-coordinate l1 ball."""

    classes: set[FlatMatrix] = set()
    vectors_seen = 0
    additive_nonzero_seen = 0
    for matrix in integer_l1_ball(ROWS * COLS, BOUND):
        vectors_seen += 1
        if matrix == (0,) * (ROWS * COLS) or not is_additive(matrix):
            continue
        additive_nonzero_seen += 1
        classes.add(canonical_c4(matrix))
    return classes, vectors_seen, additive_nonzero_seen


def enumerate_from_potentials() -> set[FlatMatrix]:
    """Independent additive-potential parametrization used as a cross-check.

    Write the first row as (a, a+c1, a+c2, a+c3) and the second row as
    the first row plus d.  The l1 bound forces a in [-B,B] and c_j,d in
    [-2B,2B], so the displayed loops are exhaustive.
    """

    classes: set[FlatMatrix] = set()
    for first_entry in range(-BOUND, BOUND + 1):
        for row_difference in range(-2 * BOUND, 2 * BOUND + 1):
            for differences in product(
                range(-2 * BOUND, 2 * BOUND + 1), repeat=COLS - 1
            ):
                row0 = (first_entry,) + tuple(
                    first_entry + difference for difference in differences
                )
                row1 = tuple(entry + row_difference for entry in row0)
                matrix = row0 + row1
                if 0 < l1_norm(matrix) <= BOUND:
                    assert is_additive(matrix)
                    classes.add(canonical_c4(matrix))
    return classes


def is_essential_mixed(matrix: FlatMatrix) -> bool:
    """Both the U3 row potential and the U5 column potential are nonconstant."""

    row0 = matrix[:COLS]
    row1 = matrix[COLS:]
    row_varies = row1[0] != row0[0]
    column_varies = any(entry != row0[0] for entry in row0[1:])
    return row_varies and column_varies


def quotient_l1_norm(values: tuple[int, ...]) -> int:
    """Compute min_c sum_i |values_i+c| exactly.

    An integral convex piecewise-linear function reaches its minimum at a
    breakpoint, so it is enough to test c=-values_i.
    """

    return min(sum(abs(entry + shift) for entry in values) for shift in {-v for v in values})


def edge_quotient_norms(matrix: FlatMatrix) -> tuple[int, int]:
    row0 = matrix[:COLS]
    row1 = matrix[COLS:]
    row_difference = row1[0] - row0[0]

    # Potentials can be chosen as u=(0,row_difference), v=row0.  Their common
    # additive gauge changes u and v by opposite constants.  The two edge
    # estimates use the corresponding quotient l1 norms separately.
    row_norm = quotient_l1_norm((0, row_difference))
    column_norm = quotient_l1_norm(row0)
    assert row_norm == abs(row_difference)
    return row_norm, column_norm


def main() -> None:
    # Multiplication by 3 advances one place in the declared U5 cycle.  This
    # makes C4 rotations the exact column action; no reflection or arbitrary
    # permutation is inserted into canonical_c4.
    assert tuple((3 * unit) % 5 for unit in U5_TIMES_THREE_CYCLE) == (
        U5_TIMES_THREE_CYCLE[1:]
        + U5_TIMES_THREE_CYCLE[:1]
    )
    assert len(set(cyclic_column_orders())) == 4

    classes, vectors_seen, additive_nonzero_seen = enumerate_from_l1_ball()
    potential_classes = enumerate_from_potentials()
    assert classes == potential_classes

    ordered = sorted(classes, key=lambda matrix: (l1_norm(matrix), matrix))
    assert all(is_additive(matrix) for matrix in ordered)
    assert all(matrix == canonical_c4(matrix) for matrix in ordered)

    norm_profile = Counter(l1_norm(matrix) for matrix in ordered)
    mixed = [matrix for matrix in ordered if is_essential_mixed(matrix)]
    mixed_norm_profile = Counter(l1_norm(matrix) for matrix in mixed)

    assert len(ordered) == 29
    assert norm_profile == Counter({2: 1, 4: 9, 6: 19})
    assert len(mixed) == 11
    assert mixed_norm_profile == Counter({4: 3, 6: 8})

    energy_rows = []
    for matrix in mixed:
        row_norm, column_norm = edge_quotient_norms(matrix)
        energy = l1_norm(matrix) + 2 * row_norm + 2 * column_norm
        assert energy > BOUND
        energy_rows.append((matrix, row_norm, column_norm, energy))
    assert min(row[3] for row in energy_rows) == 8

    s4_classes = {canonical_s4_diagnostic(matrix) for matrix in ordered}
    assert len(s4_classes) == 16
    assert len(ordered) - len(s4_classes) == 13

    payload = {
        "c4_classes": [list(matrix) for matrix in ordered],
        "essential": [
            {
                "matrix": list(matrix),
                "row_quotient": row_norm,
                "column_quotient": column_norm,
                "augmented_energy": energy,
            }
            for matrix, row_norm, column_norm, energy in energy_rows
        ],
    }
    digest = sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("ascii")
    ).hexdigest()
    assert digest == EXPECTED_PAYLOAD_SHA256

    print(f"l1_ball_vectors={vectors_seen}")
    print(f"additive_nonzero_matrices={additive_nonzero_seen}")
    print("independent_enumerators_agree=yes")
    print(f"c4_classes={len(ordered)}")
    print(f"norm_profile={dict(sorted(norm_profile.items()))}")
    print(f"essential_mixed_classes={len(mixed)}")
    print(f"essential_norm_profile={dict(sorted(mixed_norm_profile.items()))}")
    print(f"minimum_augmented_energy={min(row[3] for row in energy_rows)}")
    print(f"s4_diagnostic_classes={len(s4_classes)}")
    print(f"c4_classes_collapsed_by_s4={len(ordered) - len(s4_classes)}")
    print(f"payload_sha256={digest}")
    for index, (matrix, row_norm, column_norm, energy) in enumerate(energy_rows, 1):
        print(
            f"essential[{index:02d}] norm={l1_norm(matrix)} "
            f"edge_quotients=({row_norm},{column_norm}) "
            f"augmented_energy={energy} matrix={matrix}"
        )
    print("certificate=PASS")


if __name__ == "__main__":
    main()
