import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Basic

/-!
# Direct enumeration of the additive 2 × 4 matrices

Supporting module for `Mixed35C4AdditiveClassification`.

The naive enumerator walks the whole eight-dimensional integer `l1` ball
(40081 vectors) and then keeps the additive ones (288).  Materialising 40081
integer lists inside the kernel exhausts memory.

An additive matrix is determined by five integers: the four top entries
`a₀ a₁ a₂ a₃` and the row offset `d`, because `m[4+j] - m[4] = m[j] - m[0]`.
Enumerating those five parameters over `[-6, 6]` blindly still costs
`13^5 = 371293` kernel steps.  The enumerator below carries the remaining
`l1` budget down the recursion — after choosing `a₀`, the budget for `a₁`
drops to `6 - |a₀|`, and so on — which cuts the traversal to 18521 steps
while producing exactly the same 288 matrices.

The budget bound is forced, not chosen: `l1Norm m ≤ 6` already implies
`|a₀| + |a₁| + |a₂| + |a₃| ≤ 6`, since those four entries are part of the
norm.  `topRow_budget` below is the proof.
-/

namespace Certificates.AdditiveDirect

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev FlatMatrix := List ℤ

def l1Norm (xs : List ℤ) : ℕ := (xs.map Int.natAbs).sum

def signedRange (b : ℕ) : List ℤ :=
  (List.range (2 * b + 1)).map (fun (i : ℕ) => (i : ℤ) - b)

theorem mem_signedRange (x : ℤ) (b : ℕ) :
    x ∈ signedRange b ↔ x.natAbs ≤ b := by
  simp only [signedRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, _, rfl⟩
    omega
  · intro hx
    refine ⟨(x + b).toNat, ?_, ?_⟩ <;> omega

theorem signedRange_nodup (b : ℕ) : (signedRange b).Nodup := by
  exact List.nodup_range.map (fun x y h => by omega)

def isAdditive (m : FlatMatrix) : Bool :=
  m.length == 8 && ([1, 2, 3] : List ℕ).all fun j =>
    m[4+j]! - m[4]! == m[j]! - m[0]!

/-- The eight entries of an additive matrix, from its five free parameters. -/
def ofParams (a₀ a₁ a₂ a₃ d : ℤ) : FlatMatrix :=
  [a₀, a₁, a₂, a₃, a₀ + d, a₁ + d, a₂ + d, a₃ + d]

/-- Budget-pruned enumeration of the top row: `topRows b` lists every
    `[a₀, a₁, a₂, a₃]` with `|a₀| + |a₁| + |a₂| + |a₃| ≤ b`. -/
def topRows : ℕ → ℕ → List (List ℤ)
  | 0, _ => [[]]
  | n + 1, b => (signedRange b).flatMap fun x =>
      (topRows n (b - x.natAbs)).map (x :: ·)

/-- The pruned enumerator lists exactly the bounded top rows: nothing in the
    stated range is skipped. -/
theorem mem_topRows (xs : List ℤ) (n b : ℕ) :
    xs ∈ topRows n b ↔ xs.length = n ∧ l1Norm xs ≤ b := by
  induction n generalizing xs b with
  | zero => cases xs <;> simp [topRows, l1Norm]
  | succ n ih =>
    cases xs with
    | nil => simp [topRows]
    | cons x xs =>
      simp only [topRows, List.mem_flatMap, List.mem_map,
        List.cons.injEq, exists_eq_right_right,
        mem_signedRange, ih, List.length_cons, l1Norm,
        List.map_cons, List.sum_cons]
      omega

theorem topRows_nodup (n b : ℕ) : (topRows n b).Nodup := by
  induction n generalizing b with
  | zero => simp [topRows]
  | succ n ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun x _ => (ih (b - x.natAbs)).map (fun _ _ h => (List.cons.inj h).2),
      (signedRange_nodup b).imp ?_⟩
    intro x y hxy xs hx hy
    obtain ⟨tail, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨tail', _, heq⟩ := List.mem_map.mp hy
    exact hxy (List.cons.inj heq).1.symm

def additiveDirect : List FlatMatrix :=
  (topRows 4 6).flatMap fun row =>
    match row with
    | [a₀, a₁, a₂, a₃] =>
        (signedRange 6).flatMap fun d =>
          let m := ofParams a₀ a₁ a₂ a₃ d
          if 0 < l1Norm m ∧ l1Norm m ≤ 6 then [m] else []
    | _ => []

/-- The top row of a small-norm additive matrix already satisfies the budget:
    the pruning bound is a consequence of `l1Norm m ≤ 6`, not an assumption. -/
theorem topRow_budget (a₀ a₁ a₂ a₃ d : ℤ)
    (h : l1Norm (ofParams a₀ a₁ a₂ a₃ d) ≤ 6) :
    l1Norm [a₀, a₁, a₂, a₃] ≤ 6 := by
  simp only [ofParams, l1Norm, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil] at h ⊢
  omega

/-- `ofParams` really does produce additive matrices. -/
theorem isAdditive_ofParams (a₀ a₁ a₂ a₃ d : ℤ) :
    isAdditive (ofParams a₀ a₁ a₂ a₃ d) = true := by
  simp only [isAdditive, ofParams, List.all_cons, List.all_nil,
    Bool.and_eq_true, beq_iff_eq, List.getElem!_cons_succ,
    List.getElem!_cons_zero, List.length_cons, List.length_nil,
    and_true, true_and]
  omega

/-- Conversely, every additive matrix arises from `ofParams`, so restricting
    to the five parameters loses nothing. -/
theorem ofParams_of_isAdditive (x0 x1 x2 x3 x4 x5 x6 x7 : ℤ)
    (h : isAdditive [x0, x1, x2, x3, x4, x5, x6, x7] = true) :
    [x0, x1, x2, x3, x4, x5, x6, x7] = ofParams x0 x1 x2 x3 (x4 - x0) := by
  simp only [isAdditive, List.all_cons, List.all_nil, Bool.and_eq_true,
    beq_iff_eq, List.getElem!_cons_succ,
    List.getElem!_cons_zero, List.length_cons, List.length_nil] at h
  simp only [ofParams, List.cons.injEq, and_true, true_and]
  omega

/-- Every admissible parameter tuple occurs, including the row-difference
bound forced by the norm. This closes the pruning-to-domain implication. -/
theorem ofParams_mem_additiveDirect (a₀ a₁ a₂ a₃ d : ℤ)
    (hpos : 0 < l1Norm (ofParams a₀ a₁ a₂ a₃ d))
    (hbound : l1Norm (ofParams a₀ a₁ a₂ a₃ d) ≤ 6) :
    ofParams a₀ a₁ a₂ a₃ d ∈ additiveDirect := by
  have hd : d.natAbs ≤ 6 := by
    simp only [ofParams, l1Norm, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hbound
    omega
  simp only [additiveDirect, List.mem_flatMap]
  refine ⟨[a₀, a₁, a₂, a₃],
    (mem_topRows _ 4 6).mpr ⟨rfl, topRow_budget _ _ _ _ _ hbound⟩, ?_⟩
  dsimp only
  exact List.mem_flatMap.mpr ⟨d, (mem_signedRange d 6).mpr hd, by simp [hpos, hbound]⟩

/-- Appendix A, (A.1)--(A.2): exactly the manuscript's full domain of
nonzero integral additive 2 × 4 matrices of norm at most six. -/
theorem mem_additiveDirect_iff (m : FlatMatrix) :
    m ∈ additiveDirect ↔ isAdditive m = true ∧ 0 < l1Norm m ∧ l1Norm m ≤ 6 := by
  constructor
  · intro hm
    simp only [additiveDirect, List.mem_flatMap] at hm
    obtain ⟨row, hrow, hm⟩ := hm
    have hlen := ((mem_topRows row 4 6).mp hrow).1
    simp only [List.length_eq_succ_iff, List.length_eq_zero_iff] at hlen
    obtain ⟨a₀, _, rfl, a₁, _, rfl, a₂, _, rfl, a₃, _, rfl, rfl⟩ := hlen
    simp only [List.mem_flatMap] at hm
    obtain ⟨d, _, hm⟩ := hm
    split_ifs at hm with hnorm
    · simp only [List.mem_singleton] at hm
      subst m
      exact ⟨isAdditive_ofParams _ _ _ _ _, hnorm⟩
    · simp at hm
  · rintro ⟨hm, hpos, hbound⟩
    have hlen : m.length = 8 := by
      have h := hm
      simp only [isAdditive, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    simp only [List.length_eq_succ_iff, List.length_eq_zero_iff] at hlen
    obtain ⟨x0, _, rfl, x1, _, rfl, x2, _, rfl, x3, _, rfl,
      x4, _, rfl, x5, _, rfl, x6, _, rfl, x7, _, rfl, rfl⟩ := hlen
    have heq := ofParams_of_isAdditive x0 x1 x2 x3 x4 x5 x6 x7 hm
    rw [heq] at hpos hbound ⊢
    exact ofParams_mem_additiveDirect _ _ _ _ _ hpos hbound

/-- The enumerator produces exactly 288 matrices. -/
theorem additiveDirect_count : additiveDirect.length = 288 := by
  decide +kernel

/-- Every produced matrix is additive and has norm in the intended range. -/
theorem additiveDirect_sound :
    additiveDirect.all
      (fun m => isAdditive m && 0 < l1Norm m && decide (l1Norm m ≤ 6)) = true := by
  apply List.all_eq_true.mpr
  intro m hm
  simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using
    (mem_additiveDirect_iff m).mp hm

/-- No duplicates: the 288 are distinct. -/
theorem additiveDirect_nodup : additiveDirect.dedup.length = 288 := by
  decide +kernel

#print axioms mem_signedRange
#print axioms signedRange_nodup
#print axioms mem_topRows
#print axioms topRows_nodup
#print axioms topRow_budget
#print axioms isAdditive_ofParams
#print axioms ofParams_of_isAdditive
#print axioms additiveDirect_count
#print axioms additiveDirect_sound
#print axioms additiveDirect_nodup
#print axioms ofParams_mem_additiveDirect
#print axioms mem_additiveDirect_iff

end Certificates.AdditiveDirect
