import Mathlib.Data.List.Lex
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Decide
import Mathlib.Tactic.FinCases

/-!
# Pure one-small exception levels

This module corresponds to R7 Section 9.1 (lines 1481--1513) and Appendix B of
*The Hodge Conjecture for Odd-Degree Fermat Fourfolds*.
The source is `calculations/bundles/fermat-level15m-pure-small-exception-levels/
verify_pure_small_exception_levels.py`.

For levels 15, 21, 33, 39, all sorted sextuples with entries in
`{1, ..., 3*p-1}` are considered. Every unit Hodge row and the absence of
opposite pairs are required. The set of lexicographically canonical unit
orbits equals the explicitly listed quasi and exceptional orbits. Counts
refer to sorted sextuples before quotienting by units. No assertion about
arbitrary conductors, analytic energy reduction, or algebraic cycles is made.
-/

namespace Certificates.PureSmallExceptionLevels

def units (m : ℕ) : List ℕ :=
  (List.range m).filter fun t => Nat.gcd t m == 1

def isDecFree (m : ℕ) (a : List ℕ) : Bool :=
  a.all fun x => !a.contains ((m - x) % m)

def isHodge (m : ℕ) (a : List ℕ) : Bool :=
  (units m).all fun t => (a.map fun x => (t * x) % m).sum == 3 * m

theorem isHodge_eq_true_iff (m : ℕ) (a : List ℕ) :
    isHodge m a = true ↔
      ∀ t < m, Nat.gcd t m = 1 → (a.map fun x => (t * x) % m).sum = 3 * m := by
  simp only [isHodge, units, List.all_eq_true, List.mem_filter,
    List.mem_range, beq_iff_eq, and_imp]

theorem isDecFree_eq_true_iff (m : ℕ) (a : List ℕ) :
    isDecFree m a = true ↔ ∀ x ∈ a, (m - x) % m ∉ a := by
  simp [isDecFree, List.all_eq_true]

def interval (lo hi : ℕ) : List ℕ := List.range' lo (hi - lo)

theorem mem_interval {x lo hi : ℕ} :
    x ∈ interval lo hi ↔ lo ≤ x ∧ x < hi := by
  simp only [interval, List.mem_range', Nat.one_mul]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hl, hx⟩
    exact ⟨x - lo, by omega, by omega⟩

-- The first five entries determine the sixth by the t = 1 Hodge row.
def candidates (m : ℕ) : List (List ℕ) :=
  (interval 1 m).flatMap fun a =>
  (interval a m).flatMap fun b =>
  (interval b m).flatMap fun c =>
  (interval c m).flatMap fun d =>
  (interval d m).flatMap fun e =>
    let f := 3 * m - (a + b + c + d + e)
    if e ≤ f ∧ f < m then [[a, b, c, d, e, f]] else []

def survivors (m : ℕ) : List (List ℕ) :=
  (candidates m).filter fun a => isDecFree m a && isHodge m a

def SortedPositiveSextuple (m : ℕ) (xs : List ℕ) : Prop :=
  ∃ a b c d e f : ℕ, xs = [a, b, c, d, e, f] ∧
    1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧ e ≤ f ∧ f < m

theorem candidates_sound (m : ℕ) (xs : List ℕ) (hx : xs ∈ candidates m) :
    SortedPositiveSextuple m xs := by
  simp only [candidates, List.mem_flatMap] at hx
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, hx⟩ := hx
  simp only [mem_interval] at ha hb hc hd he
  split_ifs at hx with hf
  · simp only [List.mem_singleton] at hx
    exact ⟨a, b, c, d, e, 3 * m - (a + b + c + d + e), hx,
      ha.1, hb.1, hc.1, hd.1, he.1, hf.1, hf.2⟩
  · simp at hx

theorem sorted_sum_mem_candidates (m a b c d e f : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hef : e ≤ f) (hfm : f < m)
    (hsum : a + b + c + d + e + f = 3 * m) :
    [a, b, c, d, e, f] ∈ candidates m := by
  have htail : 3 * m - (a + b + c + d + e) = f := by omega
  simp only [candidates, List.mem_flatMap]
  refine ⟨a, mem_interval.mpr ⟨ha, by omega⟩, b,
    mem_interval.mpr ⟨hab, by omega⟩, c,
    mem_interval.mpr ⟨hbc, by omega⟩, d,
    mem_interval.mpr ⟨hcd, by omega⟩, e,
    mem_interval.mpr ⟨hde, by omega⟩, ?_⟩
  simp [htail, hef, hfm]

theorem sorted_hodge_mem_survivors (m a b c d e f : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hef : e ≤ f) (hfm : f < m)
    (hdec : isDecFree m [a, b, c, d, e, f] = true)
    (hhodge : isHodge m [a, b, c, d, e, f] = true) :
    [a, b, c, d, e, f] ∈ survivors m := by
  have hm : 1 < m := by omega
  have hunit : 1 ∈ units m := by simp [units, hm]
  have hsum := (List.all_eq_true.mp hhodge) 1 hunit
  have htotal : a + b + c + d + e + f = 3 * m := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.one_mul, Nat.mod_eq_of_lt (show a < m by omega),
      Nat.mod_eq_of_lt (show b < m by omega),
      Nat.mod_eq_of_lt (show c < m by omega),
      Nat.mod_eq_of_lt (show d < m by omega),
      Nat.mod_eq_of_lt (show e < m by omega), Nat.mod_eq_of_lt hfm,
      beq_iff_eq] at hsum
    omega
  simpa [survivors, hdec, hhodge] using
    sorted_sum_mem_candidates m a b c d e f ha hab hbc hcd hde hef hfm htotal

/-- The enumerator is equivalent to the actual universal sextuple domain. -/
theorem mem_survivors_iff (m : ℕ) (xs : List ℕ) :
    xs ∈ survivors m ↔ SortedPositiveSextuple m xs ∧
      isDecFree m xs = true ∧ isHodge m xs = true := by
  constructor
  · intro hx
    have h := List.mem_filter.mp hx
    have hp : isDecFree m xs = true ∧ isHodge m xs = true := by simpa using h.2
    exact ⟨candidates_sound m xs h.1, hp.1, hp.2⟩
  · rintro ⟨⟨a, b, c, d, e, f, rfl, ha, hab, hbc, hcd, hde, hef, hfm⟩, hd, hh⟩
    exact sorted_hodge_mem_survivors m a b c d e f ha hab hbc hcd hde hef hfm hd hh

def canonical (m : ℕ) (a : List ℕ) : List ℕ :=
  ((units m).map fun t =>
    (a.map fun x => (t * x) % m).insertionSort (· ≤ ·)).min?.getD []

def quasi (p : ℕ) : List ℕ :=
  [1, 1 + p, 1 + 2 * p, 3 + p, 3 + 2 * p, 3 * p - 9]

def exceptions (p : ℕ) : List (List ℕ) :=
  if p = 7 then [[1, 4, 10, 13, 16, 19], [1, 4, 9, 15, 16, 18]]
  else if p = 11 then [[1, 4, 16, 22, 25, 31]]
  else if p = 13 then [[1, 7, 16, 22, 34, 37], [1, 14, 16, 22, 29, 35]]
  else []

def found (p : ℕ) : Finset (List ℕ) :=
  ((survivors (3 * p)).map (canonical (3 * p))).toFinset

def expected (p : ℕ) : Finset (List ℕ) :=
  (((quasi p) :: exceptions p).map (canonical (3 * p))).toFinset

-- This is the same enumeration, with filtering performed at each leaf.
-- Prefixes partition the entire search so every kernel check stays bounded.
def survivorSlice (m a b : ℕ) : List (List ℕ) :=
  (interval b m).flatMap fun c =>
  (interval c m).flatMap fun d =>
  (interval d m).flatMap fun e =>
    let f := 3 * m - (a + b + c + d + e)
    if e ≤ f ∧ f < m then
      if isDecFree m [a, b, c, d, e, f] && isHodge m [a, b, c, d, e, f]
      then [[a, b, c, d, e, f]] else []
    else []

theorem survivors_eq_slices (m : ℕ) : survivors m =
    (interval 1 m).flatMap fun a =>
      (interval a m).flatMap fun b => survivorSlice m a b := by
  simp only [survivors, candidates, survivorSlice, List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro b hb
  apply List.flatMap_congr
  intro c hc
  apply List.flatMap_congr
  intro d hd
  apply List.flatMap_congr
  intro e he
  split_ifs <;> simp_all

def tableSlice (table : List (List ℕ)) (a b : ℕ) : List (List ℕ) :=
  table.filter fun xs => xs[0]? == some a && xs[1]? == some b

def table15 : List (List ℕ) :=
  [[1, 2, 7, 11, 12, 12], [1, 4, 7, 10, 10, 13], [1, 6, 6, 8, 11, 13],
   [2, 4, 7, 9, 9, 14], [2, 5, 5, 8, 11, 14], [3, 3, 4, 8, 13, 14]]

def expected15 : Finset (List ℕ) :=
  (([[1, 2, 7, 11, 12, 12], [1, 4, 7, 10, 10, 13]] : List (List ℕ)).map
    (canonical 15)).toFinset

def table21 : List (List ℕ) :=
  [[1, 4, 9, 15, 16, 18], [1, 4, 10, 13, 16, 19], [1, 5, 8, 12, 18, 19],
   [1, 8, 10, 12, 15, 17], [2, 3, 9, 13, 16, 20], [2, 3, 10, 15, 16, 17],
   [2, 5, 8, 11, 17, 20], [2, 8, 9, 11, 15, 18], [3, 5, 6, 12, 17, 20],
   [3, 6, 10, 12, 13, 19], [4, 5, 6, 11, 18, 19], [4, 6, 9, 11, 13, 20]]

def table33 : List (List ℕ) :=
  [[1, 4, 15, 23, 26, 30], [1, 4, 16, 22, 25, 31], [1, 12, 14, 23, 24, 25],
   [2, 8, 11, 17, 29, 32], [2, 8, 13, 19, 27, 30], [2, 13, 15, 17, 24, 28],
   [3, 6, 14, 20, 25, 31], [3, 7, 10, 18, 29, 32], [4, 5, 16, 21, 26, 27],
   [5, 9, 16, 18, 20, 31], [5, 11, 14, 20, 23, 26], [6, 7, 12, 17, 28, 29],
   [7, 10, 13, 19, 22, 28], [8, 9, 10, 19, 21, 32]]

def table39 : List (List ℕ) :=
  [[1, 7, 16, 22, 34, 37], [1, 9, 14, 22, 35, 36], [1, 14, 16, 22, 29, 35],
   [1, 14, 16, 27, 29, 30], [1, 16, 19, 22, 28, 31], [2, 5, 14, 29, 32, 35],
   [2, 5, 17, 23, 32, 38], [2, 5, 18, 28, 31, 33], [2, 5, 19, 28, 31, 32],
   [2, 15, 19, 21, 28, 32], [3, 4, 17, 25, 30, 38], [3, 12, 16, 22, 29, 35],
   [4, 7, 10, 25, 34, 37], [4, 10, 17, 23, 25, 38], [4, 10, 17, 23, 27, 36],
   [4, 10, 19, 25, 28, 31], [5, 6, 19, 24, 31, 32], [6, 8, 11, 21, 34, 37],
   [7, 8, 11, 20, 34, 37], [7, 8, 15, 20, 33, 34], [7, 11, 18, 20, 24, 37],
   [8, 11, 14, 20, 29, 35], [8, 11, 17, 20, 23, 38], [9, 10, 12, 23, 25, 38]]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem level15_slices (a b : Fin 15) :
    1 ≤ a.val → a.val ≤ b.val →
    survivorSlice 15 a.val b.val = tableSlice table15 a.val b.val := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem level21_slices (a b : Fin 21) :
    1 ≤ a.val → a.val ≤ b.val →
    survivorSlice 21 a.val b.val = tableSlice table21 a.val b.val := by
  fin_cases a <;> fin_cases b <;> decide +kernel

#print axioms level21_slices

theorem level33_slices (a b : Fin 33) :
    1 ≤ a.val → a.val ≤ b.val →
    survivorSlice 33 a.val b.val = tableSlice table33 a.val b.val := by
  fin_cases a <;> fin_cases b <;> decide +kernel

#print axioms level33_slices

theorem level39_slices (a b : Fin 39) :
    1 ≤ a.val → a.val ≤ b.val →
    survivorSlice 39 a.val b.val = tableSlice table39 a.val b.val := by
  fin_cases a <;> fin_cases b <;> decide +kernel

#print axioms level39_slices

theorem survivors_eq_table_of_slices (m : ℕ) (table : List (List ℕ))
    (hslices : ∀ a b : Fin m, 1 ≤ a.val → a.val ≤ b.val →
      survivorSlice m a.val b.val = tableSlice table a.val b.val)
    (hreassemble : ((interval 1 m).flatMap fun a =>
      (interval a m).flatMap fun b => tableSlice table a b) = table) :
    survivors m = table := by
  rw [survivors_eq_slices]
  trans (interval 1 m).flatMap fun a =>
    (interval a m).flatMap fun b => tableSlice table a b
  · apply List.flatMap_congr
    intro a ha
    apply List.flatMap_congr
    intro b hb
    have ha' := mem_interval.mp ha
    have hb' := mem_interval.mp hb
    exact hslices ⟨a, ha'.2⟩ ⟨b, hb'.2⟩ ha'.1 hb'.1
  · exact hreassemble

theorem level15_survivors : survivors 15 = table15 :=
  survivors_eq_table_of_slices 15 table15 level15_slices (by decide +kernel)

theorem level21_survivors : survivors 21 = table21 :=
  survivors_eq_table_of_slices 21 table21 level21_slices (by decide +kernel)

theorem level33_survivors : survivors 33 = table33 :=
  survivors_eq_table_of_slices 33 table33 level33_slices (by decide +kernel)

theorem level39_survivors : survivors 39 = table39 :=
  survivors_eq_table_of_slices 39 table39 level39_slices (by decide +kernel)

theorem level15_certificate :
    ((survivors 15).map (canonical 15)).toFinset = expected15 ∧
    (survivors 15).length = 6 ∧ expected15.card = 2 := by
  rw [level15_survivors]
  decide +kernel

/-- All four exact tables, with the actual sorted Hodge domain in both directions. -/
theorem exact_tuple_tables (m : ℕ) (table : List (List ℕ))
    (h : (m = 15 ∧ table = table15) ∨ (m = 21 ∧ table = table21) ∨
         (m = 33 ∧ table = table33) ∨ (m = 39 ∧ table = table39)) (xs : List ℕ) :
    xs ∈ table ↔ SortedPositiveSextuple m xs ∧
      isDecFree m xs = true ∧ isHodge m xs = true := by
  have heq : survivors m = table := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact level15_survivors
    · exact level21_survivors
    · exact level33_survivors
    · exact level39_survivors
  rw [← heq, mem_survivors_iff]

/-- The original canonical-set assertion and its two printed counts at p = 7. -/
theorem level21_certificate : found 7 = expected 7 ∧
    (survivors 21).length = 12 ∧ (found 7).card = 3 := by
  change ((survivors 21).map (canonical 21)).toFinset = expected 7 ∧
    (survivors 21).length = 12 ∧ ((survivors 21).map (canonical 21)).toFinset.card = 3
  rw [level21_survivors]
  decide +kernel

/-- The original canonical-set assertion and its two printed counts at p = 11. -/
theorem level33_certificate : found 11 = expected 11 ∧
    (survivors 33).length = 14 ∧ (found 11).card = 2 := by
  change ((survivors 33).map (canonical 33)).toFinset = expected 11 ∧
    (survivors 33).length = 14 ∧ ((survivors 33).map (canonical 33)).toFinset.card = 2
  rw [level33_survivors]
  decide +kernel

/-- The original canonical-set assertion and its two printed counts at p = 13. -/
theorem level39_certificate : found 13 = expected 13 ∧
    (survivors 39).length = 24 ∧ (found 13).card = 3 := by
  change ((survivors 39).map (canonical 39)).toFinset = expected 13 ∧
    (survivors 39).length = 24 ∧ ((survivors 39).map (canonical 39)).toFinset.card = 3
  rw [level39_survivors]
  decide +kernel

/-- Exact coverage of the actual sorted positive sextuple domain, in both directions. -/
theorem canonical_membership_iff (p : ℕ) (hp : p = 7 ∨ p = 11 ∨ p = 13)
    (c : List ℕ) : c ∈ expected p ↔
      ∃ xs, SortedPositiveSextuple (3 * p) xs ∧ isDecFree (3 * p) xs = true ∧
        isHodge (3 * p) xs = true ∧ canonical (3 * p) xs = c := by
  have hfound : found p = expected p := by
    rcases hp with rfl | rfl | rfl
    · exact level21_certificate.1
    · exact level33_certificate.1
    · exact level39_certificate.1
  rw [← hfound]
  simp [found, mem_survivors_iff, and_assoc]

#print axioms sorted_hodge_mem_survivors
#print axioms mem_survivors_iff
#print axioms survivors_eq_slices
#print axioms level21_certificate
#print axioms level33_certificate
#print axioms level39_certificate
#print axioms canonical_membership_iff

end Certificates.PureSmallExceptionLevels
