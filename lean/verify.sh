#!/usr/bin/env bash
# Full verification of the finite certificates. Portable: runs anywhere with
# elan (Lean 4) and Python 3.11+. Sequential Lean builds to bound memory (~9 GB peak).
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p verification
PY="${PYTHON:-python3}"

echo "== Python re-computations =="
for script in verify_mixed35_c4_additive_classification verify_pure_small_exception_levels \
    verify_level66_aoki_bridge verify_small_matrices verify_reconstruction_finite \
    verify_r7_finite_endpoints; do
  "$PY" "python/$script.py" > "verification/$script.txt"
  cat "verification/$script.txt"
done
"$PY" python/check_axioms.py --generate

echo "== Lean build (sequential) =="
lean --version
for module in AdditiveDirect Mixed35C4AdditiveClassification Mixed35Direct \
    PureSmallExceptionLevels Level66AokiBridge SmallMatrices U25Correction HalfIntegralPotentials \
    R7FiniteEndpoints; do
  lake build "Certificates.$module"
done
lake build

echo "== Axiom audit =="
lake env lean -j1 PrintAxioms.lean > verification/axioms.txt
cat verification/axioms.txt
"$PY" python/check_axioms.py verification/axioms.txt

echo "== Lean/Python cross-check =="
lake env lean -j1 ComparePython.lean > verification/compare-python.txt
cat verification/compare-python.txt
"$PY" python/verify_reconstruction_finite.py --compare-lean \
  verification/verify_reconstruction_finite.txt verification/compare-python.txt

echo
echo 'FULL VERIFICATION COMPLETE: finite certificates, complete axiom reports, Python comparison.'
echo 'NOT formalized: Theorems 1.1/4.1/10.2; arbitrary conductors/depths and ambient transport;'
echo 'Chow realization, Aoki/Ran/Lefschetz hypotheses and applications, geometric descent.'
