#!/usr/bin/env python3
"""Lemma 6.1 (reconstruction Lemma 3.1): all three integer l1 balls.

Matrices are column-major.  The primary enumerator streams every integer
matrix of norm at most six; the second uses row offsets and column budgets,
the same exhaustive pruning whose coverage is proved in SmallMatrices.lean.
Only the at most 295 additive matrices are retained in memory.
"""

from collections import Counter
from itertools import product

from verify_mixed35_c4_additive_classification import integer_l1_ball


def norm(matrix):
    return sum(map(abs, matrix))


def is_additive(matrix, rows, cols):
    return all(
        matrix[rows * col + row] - matrix[rows * col]
        == matrix[row] - matrix[0]
        for col in range(cols)
        for row in range(rows)
    )


def column_budget_matrices(offsets, cols, budget):
    if cols == 0:
        yield ()
        return
    for top in range(-budget, budget + 1):
        column = (top,) + tuple(top + offset for offset in offsets)
        cost = norm(column)
        if cost <= budget:
            for rest in column_budget_matrices(offsets, cols - 1, budget - cost):
                yield column + rest


def row_invariant(matrix, rows, cols):
    return all(
        matrix[rows * col + row] == matrix[rows * col]
        for col in range(cols)
        for row in range(rows)
    )


def column_invariant(matrix, rows, cols):
    return all(
        matrix[rows * col + row] == matrix[row]
        for col in range(cols)
        for row in range(rows)
    )


def complete_row(matrix, rows, cols):
    return any(
        all(
            matrix[rows * col + row] == (sign if row == active else 0)
            for col in range(cols)
            for row in range(rows)
        )
        for active in range(rows)
        for sign in (-1, 1)
    )


def classified(matrix, rows, cols):
    mass = norm(matrix)
    invariant = row_invariant(matrix, rows, cols)
    if rows == 2:
        return (invariant and mass % 2 == 0) or (
            mass == 5
            and all(norm(matrix[2 * col : 2 * col + 2]) == 1 for col in range(5))
        )
    essential = not invariant and not column_invariant(matrix, rows, cols)
    return invariant or complete_row(matrix, rows, cols) or (
        essential
        and (
            (cols == 4 and mass == 5 and abs(sum(matrix)) == 1)
            or (mass == 6 and abs(sum(matrix)) == 2)
        )
    )


def run():
    for rows, cols, expected in ((3, 4, 106), (3, 5, 96), (2, 5, 294)):
        all_vectors = 0
        direct = set()
        for matrix in integer_l1_ball(rows * cols, 6):
            all_vectors += 1
            if is_additive(matrix, rows, cols):
                direct.add(matrix)
        pruned = [
            matrix
            for offsets in product(range(-6, 7), repeat=rows - 1)
            for matrix in column_budget_matrices(offsets, cols, 6)
        ]
        assert len(pruned) == len(set(pruned)), "duplicate normalized parameters"
        assert direct == set(pruned), "full l1 ball and pruned domains differ"
        nonzero = direct - {(0,) * (rows * cols)}
        assert len(nonzero) == expected
        assert all(classified(matrix, rows, cols) for matrix in direct)
        print(f"matrices_{rows}x{cols}_full_l1_ball={all_vectors}")
        print(f"matrices_{rows}x{cols}_nonzero={len(nonzero)}")
        print(f"matrices_{rows}x{cols}_mass_profile={dict(sorted(Counter(map(norm, nonzero)).items()))}")
        print(f"matrices_{rows}x{cols}_classification=PASS")
    print("independent_enumerators_agree=yes")
    print("certificate=PASS")


if __name__ == "__main__":
    run()
