import Certificates.PureSmallExceptionLevels
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# R7 finite endpoint completions

The frozen R7 manuscript is
`papers/The-Hodge-Conjecture-for-Odd-Degree-Fermat-Fourfolds/
the-hodge-conjecture-for-odd-degree-fermat-fourfolds.md`.
Line references below are to that source, not the earlier 22-page version.

The identities (4),(5) are proved for arbitrary multisets and instantiated
with the actual fibres and complementary residues, without a conductor bound.
Only the fixed characters in Sections 9--10 receive Hodge-row certificates.
Every occurrence, nonzero entry, length, and unit row is retained. These
assertions do not formalize Chow realization or arbitrary-conductor reduction.
The corresponding Python reproduction is `python/verify_r7_finite_endpoints.py`.
-/

namespace Certificates.R7FiniteEndpoints

open Certificates.PureSmallExceptionLevels (units quasi)

/-- The canonical nonnegative representative of `-x` modulo `m`. -/
def residueNeg (m x : ℕ) : ℕ := (m - x % m) % m

/-- R7 Lemma 3.3, line 528: `L_p(c)`, retaining every occurrence. -/
def fibre (m p c : ℕ) : List ℕ :=
  (List.range p).map fun j => (c + j * (m / p)) % m

/-- `L_p(c)` followed by `-pc`; `p=3` gives `C(c)`, and `p=5` standard-five. -/
def standard (m p c : ℕ) : List ℕ :=
  fibre m p c ++ [residueNeg m (p * c)]

/-- Nonzero Hodge characters of length `2*grade`, tested at every unit. -/
def isHodgeBlock (m grade : ℕ) (a : List ℕ) : Bool :=
  (a.length == 2 * grade) &&
  a.all (fun x => decide (0 < x ∧ x < m)) &&
  (units m).all fun t => (a.map fun x => (t * x) % m).sum == grade * m

/-- R7 §2, equation (1), lines 263--269: the checker has the full unit quantifier. -/
theorem isHodgeBlock_iff (m grade : ℕ) (a : List ℕ) :
    isHodgeBlock m grade a = true ↔
      a.length = 2 * grade ∧ (∀ x ∈ a, 0 < x ∧ x < m) ∧
      ∀ t < m, Nat.gcd t m = 1 →
        (a.map fun x => (t * x) % m).sum = grade * m := by
  simp only [isHodgeBlock, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq, units, List.mem_filter, List.mem_range, and_imp, and_assoc]

/-- R7 (4), lines 556--561: the occurrence identity for arbitrary multisets.
`nx` is unrestricted here; `three_fibre_identity` supplies the residue of `-x`. -/
theorem completion_three_multiset {α : Type*} (L R : Multiset α) (x nx : α) :
    (L + R) + ({x} + {nx}) = (L + {nx}) + (R + {x}) := by
  simp only [add_assoc, add_comm, add_left_comm]

/-- R7 (5), lines 568--574: erase exactly one occurrence of `d`, for every `d ∈ L`.
`nd,nx` are supplied as the actual negative residues in `five_fibre_identity`. -/
theorem completion_five_multiset {α : Type*} [DecidableEq α]
    (L : Multiset α) (d x y z nd nx : α) (hd : d ∈ L) :
    (L.erase d + ({y} + {z})) + ({d} + {nd}) + ({x} + {nx}) =
      (L + {nx}) + ({x} + {y} + {z} + {nd}) := by
  have hrestore : L.erase d + {d} = L := by
    rw [add_comm, Multiset.singleton_add]
    exact Multiset.cons_erase hd
  calc
    _ = (L.erase d + {d}) + ({nx} + ({x} + {y} + {z} + {nd})) := by
      simp only [add_assoc, add_comm, add_left_comm]
    _ = (L + {nx}) + ({x} + {y} + {z} + {nd}) := by
      rw [hrestore]
      simp only [add_assoc]

/-- R7 Lemma 3.3, (4), lines 528,556--561: the literal fibre specialization.
The multiset equality itself needs no Hodge assumption or conductor bound. -/
theorem three_fibre_identity (m c : ℕ) (R : Multiset ℕ) :
    ((fibre m 3 c : Multiset ℕ) + R) +
        ({(3 * c) % m} + {residueNeg m (3 * c)}) =
      ((fibre m 3 c : Multiset ℕ) + {residueNeg m (3 * c)}) +
        (R + {(3 * c) % m}) :=
  completion_three_multiset _ R _ _

/-- R7 Lemma 3.3, (5), lines 528,568--574: every `d ∈ L_5(c)` and arbitrary `y,z`.
In particular, no divisibility condition is imposed on either complementary entry. -/
theorem five_fibre_identity (m c d y z : ℕ)
    (hd : d ∈ (fibre m 5 c : Multiset ℕ)) :
    ((fibre m 5 c : Multiset ℕ).erase d + ({y} + {z})) +
        ({d} + {residueNeg m d}) + ({(5 * c) % m} + {residueNeg m (5 * c)}) =
      ((fibre m 5 c : Multiset ℕ) + {residueNeg m (5 * c)}) +
        ({(5 * c) % m} + {y} + {z} + {residueNeg m d}) :=
  completion_five_multiset _ d _ y z _ _ hd

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- R7 §9.1, lines 1486--1491: the first level-15 endpoint and both actual surfaces. -/
theorem level15_three_completion :
    ((([1, 2, 7, 11, 12, 12] ++ [6, 9]) : List ℕ) : Multiset ℕ) =
        ((standard 15 3 2 ++ standard 15 3 6 : List ℕ) : Multiset ℕ) ∧
      isHodgeBlock 15 3 [1, 2, 7, 11, 12, 12] = true ∧
      isHodgeBlock 15 2 (standard 15 3 2) = true ∧
      isHodgeBlock 15 2 (standard 15 3 6) = true ∧
      (6 + 9) % 15 = 0 := by
  decide +kernel

/-- R7 §9.1, lines 1486--1488, and Lemma 3.2, lines 504--507: `d=3,a=1`. -/
theorem level15_standard_five :
    (([1, 4, 7, 10, 10, 13] : List ℕ) : Multiset ℕ) =
        (standard 15 5 1 : Multiset ℕ) ∧
      isHodgeBlock 15 3 (standard 15 5 1) = true := by
  decide +kernel

/-- R7 §9.2, lines 1517--1520, with precisely the three parameters at 1493--1495. -/
theorem quasi_three_completion (p : ℕ) (hp : p = 7 ∨ p = 11 ∨ p = 13) :
    ((quasi p ++ [3, residueNeg (3 * p) 3] : List ℕ) : Multiset ℕ) =
        ((standard (3 * p) 3 1 ++ standard (3 * p) 3 3 : List ℕ) : Multiset ℕ) ∧
      isHodgeBlock (3 * p) 3 (quasi p) = true ∧
      isHodgeBlock (3 * p) 2 (standard (3 * p) 3 1) = true ∧
      isHodgeBlock (3 * p) 2 (standard (3 * p) 3 3) = true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

/-- The finite arithmetic in R7 §9.2, lines 1525--1530; this asserts no cycle class. -/
def SplitCertificate (m : ℕ) (a left right : List ℕ) : Prop :=
  (a : Multiset ℕ) = ((left ++ right : List ℕ) : Multiset ℕ) ∧
  left.length = 3 ∧ right.length = 3 ∧
  left.sum % m = 0 ∧ right.sum % m = 0 ∧
  isHodgeBlock m 3 (left ++ right) = true

/-- R7 §9.2, line 1525, first split; the representative is §9.1 line 1501. -/
theorem split_level21_first :
    SplitCertificate 21 [1, 4, 9, 15, 16, 18] [1, 4, 16] [9, 15, 18] := by
  unfold SplitCertificate
  decide +kernel

/-- R7 §9.2, line 1525, second split; the representative is §9.1 line 1501. -/
theorem split_level21_second :
    SplitCertificate 21 [1, 4, 10, 13, 16, 19] [1, 4, 16] [10, 13, 19] := by
  unfold SplitCertificate
  decide +kernel

/-- R7 §9.2, line 1526, first split; the representative is §9.1 line 1503. -/
theorem split_level39_first :
    SplitCertificate 39 [1, 7, 16, 22, 34, 37] [1, 16, 22] [7, 34, 37] := by
  unfold SplitCertificate
  decide +kernel

/-- R7 §9.2, line 1526, second split; the representative is §9.1 line 1503. -/
theorem split_level39_second :
    SplitCertificate 39 [1, 14, 16, 22, 29, 35] [1, 16, 22] [14, 29, 35] := by
  unfold SplitCertificate
  decide +kernel

def a105 : List ℕ := [3, 24, 50, 66, 85, 87]
def s105 : List ℕ := standard 105 5 3
def b105 : List ℕ := [15, 50, 85, 60]

/-- R7 §10, line 1622, and Lemma 3.3(2), lines 534--535: the exact four-point fibre. -/
theorem level105_four_point_fibre :
    5 ∣ 105 ∧ 3 % (105 / 5) ≠ 0 ∧
      fibre 105 5 3 = [3, 24, 45, 66, 87] ∧ 45 ∈ fibre 105 5 3 ∧
      ((fibre 105 5 3 : Multiset ℕ).erase 45).card = 4 ∧
      (a105 : Multiset ℕ) = (fibre 105 5 3 : Multiset ℕ).erase 45 +
        (([50, 85] : List ℕ) : Multiset ℕ) := by
  decide +kernel

/-- R7 §10 line 1622 instantiated in Lemma 3.3 lines 568--571: actual `S,B`, all unit rows. -/
theorem level105_hodge_blocks :
    s105 = [3, 24, 45, 66, 87, 90] ∧ b105 = [15, 50, 85, 60] ∧
      isHodgeBlock 105 3 a105 = true ∧ isHodgeBlock 105 3 s105 = true ∧
      isHodgeBlock 105 2 b105 = true := by
  decide +kernel

/-- R7 (5), lines 573--574, instantiated at the §10 endpoint (line 1622). -/
theorem level105_five_completion :
    ((a105 ++ [45, 60] ++ [15, 90] : List ℕ) : Multiset ℕ) =
        ((s105 ++ b105 : List ℕ) : Multiset ℕ) ∧
      (45 + 60) % 105 = 0 ∧ (15 + 90) % 105 = 0 := by
  decide +kernel

#print axioms isHodgeBlock_iff
#print axioms completion_three_multiset
#print axioms completion_five_multiset
#print axioms three_fibre_identity
#print axioms five_fibre_identity
#print axioms level15_three_completion
#print axioms level15_standard_five
#print axioms quasi_three_completion
#print axioms split_level21_first
#print axioms split_level21_second
#print axioms split_level39_first
#print axioms split_level39_second
#print axioms level105_four_point_fibre
#print axioms level105_hodge_blocks
#print axioms level105_five_completion

end Certificates.R7FiniteEndpoints
