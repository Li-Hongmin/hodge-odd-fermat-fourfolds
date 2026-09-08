# The Hodge Conjecture for Odd-Degree Fermat Fourfolds

[![Verify Lean certificates](https://github.com/Li-Hongmin/hodge-odd-fermat-fourfolds/actions/workflows/verify.yml/badge.svg)](https://github.com/Li-Hongmin/hodge-odd-fermat-fourfolds/actions/workflows/verify.yml)
[![DOI](https://img.shields.io/badge/DOI-10.13140%2FRG.2.2.26853.77288-blue)](https://doi.org/10.13140/RG.2.2.26853.77288)

**An AI-generated proof, released for human verification.**

Hongmin Li — Graduate School of Frontier Sciences, The University of Tokyo
lihongmin@edu.k.u-tokyo.ac.jp

## What is claimed

Let X_m^4 = {x_0^m + ... + x_5^m = 0} ⊂ P^5 be the Fermat fourfold of odd degree m.

**Theorem 1.1.** For every odd integer m ≥ 3, the cycle class map
CH^2(X_m^4)_Q → H^4(X_m^4, Q) ∩ H^{2,2}(X_m^4) is surjective.
Consequently every odd-degree Fermat fourfold satisfies the rational Hodge conjecture in all codimensions.

The argument works in the Shioda–Aoki tradition: Fermat characters, induced cycles, Aoki's join/contraction constructions, Ran's cycles, and a character-sum / conductor-descent reduction to a fixed finite list of endpoint families, which are then checked by exhaustive finite computation.

## How this manuscript was produced — please read before anything else

The manuscript, the reduction strategy, and the finite certificates were produced by AI systems (OpenAI Codex agents and GPT-family models) operating over several weeks under my direction. My role was to set goals, allocate compute, and decide when to stop. **I am not a specialist in algebraic cycles or Hodge theory, and I cannot independently vouch for the correctness of the proof.**

I am releasing it precisely for that reason: the mathematics either stands or it does not, and only human experts in this area can tell. If you work on Fermat varieties, algebraic cycles, or Hodge classes, I would be grateful for your reading — whether the outcome is "correct", "fixable", or "wrong at step X". All three are valuable, and I will publicly record whichever it turns out to be.

Correspondence: lihongmin@edu.k.u-tokyo.ac.jp. Substantive verification or correction will be acknowledged, and co-authorship on any revised version is open to anyone who materially contributes.

## Relation to prior work

Kang (Bull. Aust. Math. Soc. 93, 2016, Corollary 3.2) states a stronger result — the generalized Hodge conjecture for Fermat varieties of dimensions three and four in arbitrary degree — via refined motivic dimension. Section 1.1 of the manuscript explains why we treat that statement as a precedent rather than an input, and identifies a specific step in the product argument (Kang 2015, Proposition 2.2(iv)) that we were unable to confirm. We do not claim to have disproved Kang's statement. An expert opinion on this point is especially welcome.

## Cite

Hongmin Li, *The Hodge Conjecture for Odd-Degree Fermat Fourfolds*, preprint, September 2026. DOI: [10.13140/RG.2.2.26853.77288](https://doi.org/10.13140/RG.2.2.26853.77288). Source and certificates: this repository.

## Contents

| Path | What it is |
|---|---|
| `paper/hodge-odd-fermat-fourfolds.pdf` | The manuscript (26 pages) |
| `paper/main.tex` | LaTeX source |
| `lean/` | Lean 4 certificates for the finite parts of the argument (see below) |
| `.github/workflows/verify.yml` | CI: every push rebuilds all certificates from scratch and audits their axioms; click the badge above for the latest log |

## What the Lean certificates do and do not cover

`lean/` contains a Lean 4 project (toolchain pinned in `lean/lean-toolchain`) with 117 kernel-checked theorems covering the **finite arithmetic endpoints** of the reduction: enumeration of small additive matrices (Appendix A, Lemma 6.1), the exceptional-level tuples at levels 15/21/33/39 (§9.1, Appendix B), the U25 and half-integral potential corrections (Theorems 7.3, 7.5), the level-66 and level-105 occurrence identities (Lemma 3.3, §9–10, Appendix C). Each theorem's axiom footprint is printed and audited on every CI run (`lean/python/check_axioms.py`): all must be subsets of `{propext, Classical.choice, Quot.sound}`, with no `sorryAx`. Independent Python re-computations of every finite enumeration are in `lean/python/` and are cross-checked against the Lean `#eval` output in the same run. Full transcripts are attached to each CI run as an artifact.

**Not formalized** — and this is where a human reader is needed:

1. The main theorems (1.1, 4.1, 10.2) and every infinite argument: the terminal definition, descent-or-packet exhaustiveness, the §6–10 proofs for arbitrary odd conductors and primary depth, and the global assembly.
2. The analytic and ambient transfers: exact-order/Fourier reduction, Euler factors, row-lift freedom, kernel elimination, budget exhaustion, the estimate (11) for j ≥ 2.
3. All Chow-theoretic content: cycle classes, correspondences, non-vanishing, rational projectors, irreducibility of rational blocks. The Lean files prove arithmetic identities only; they do not prove that anything is algebraic.
4. The external inputs (Aoki, Ran, Jumagulov, Lefschetz) and the hypotheses under which they are invoked.

The finite certificates therefore do **not** constitute a formal proof of Theorem 1.1. They rule out arithmetic slips in the endpoint computations, nothing more.

## Reproducing the Lean check

Requires [elan](https://github.com/leanprover/elan), Python 3.11+, and ~9 GB RAM; about 15 minutes after the Mathlib cache is fetched.

```
cd lean
lake exe cache get
bash verify.sh
```

Or simply fork this repository — the GitHub Actions workflow runs the same script on a clean machine.

## License

Manuscript and source: CC BY 4.0. Lean and Python code: MIT.
