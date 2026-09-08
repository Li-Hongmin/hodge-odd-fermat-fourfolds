import Certificates.AdditiveDirect

/-!
# The 2 × 4 cyclic additive certificate, on the pruned enumerator

Appendix A (A.1–A.7), including its independent finite energy inequality, of
*The Hodge Conjecture for Odd-Degree Fermat Fourfolds*.
Source: `calculations/bundles/fermat-level15m-mixed35-c4-additive-classification/
verify_mixed35_c4_additive_classification.py`.

`Mixed35C4AdditiveClassification` states the same classification over
`integerL1Ball 8 6`, whose 40081 entries exhaust kernel memory.  This module
runs the identical classification over `AdditiveDirect.additiveDirect`, which
`AdditiveDirect` proves is exactly the set of nonzero additive matrices of
`l1` norm at most six — the two domains agree, so nothing is narrowed:

* `mem_topRows`         the pruned traversal skips nothing in range;
* `topRow_budget`       the pruning bound follows from `l1Norm m ≤ 6`;
* `isAdditive_ofParams` every produced matrix is additive;
* `mem_additiveDirect_iff` exact two-way coverage of the manuscript domain.

Scope.  This certifies the finite classification only.  Neither the Fourier
reduction to this domain nor the physical edge-cost argument is formalized,
and no statement about algebraic cycles is made here. In the reconstructed
manuscript Lemma 8.2 is analytic: this augmented energy is not actual mass.
These 2 × 4 matrices are distinct from the 3 × 4, 3 × 5 and 2 × 5
matrices of reconstructed Lemma 6.1 (Lemma 3.1 in the reconstruction source).
-/

namespace Certificates.Mixed35Direct

open Certificates.AdditiveDirect

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev FlatMatrix := List ℤ

def transform (m : FlatMatrix) (rows columns : List ℕ) (sign : ℤ) : FlatMatrix :=
  rows.flatMap fun r => columns.map fun c => sign * m[4*r+c]!

def cyclicColumnOrders : List (List ℕ) :=
  (List.range 4).map fun s => (List.range 4).map fun c => (c+s)%4

def lexMin (xs : List FlatMatrix) : FlatMatrix := xs.foldl min xs.head!

def canonicalC4 (m : FlatMatrix) : FlatMatrix :=
  lexMin <| [[0, 1], [1, 0]].flatMap fun rows =>
    cyclicColumnOrders.flatMap fun columns =>
      ([1, -1] : List ℤ).map fun s => transform m rows columns s

/-- The 24 column permutations, listed explicitly. `allPerms_correct`
checks distinctness, length and membership of all four column indices. -/
def allPerms : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
   [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
   [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0],
   [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

def canonicalS4 (m : FlatMatrix) : FlatMatrix :=
  lexMin <| [[0, 1], [1, 0]].flatMap fun rows =>
    allPerms.flatMap fun columns =>
      ([1, -1] : List ℤ).map fun s => transform m rows columns s

def c4Classes : List FlatMatrix := (additiveDirect.map canonicalC4).dedup

def ordered : List FlatMatrix :=
  c4Classes.insertionSort fun a b =>
    l1Norm a < l1Norm b ∨ (l1Norm a = l1Norm b ∧ a ≤ b)

def isEssential (m : FlatMatrix) : Bool :=
  m[4]! != m[0]! && ((m.take 4).drop 1).any (fun x => x != m[0]!)

def quotientL1Norm (xs : List ℤ) : ℕ :=
  let costs := xs.map fun v => l1Norm (xs.map (· - v))
  costs.foldl min costs.head!

def rowQuotient (m : FlatMatrix) : ℕ := quotientL1Norm [0, m[4]! - m[0]!]
def colQuotient (m : FlatMatrix) : ℕ := quotientL1Norm (m.take 4)
def energy (m : FlatMatrix) : ℕ := l1Norm m + 2 * rowQuotient m + 2 * colQuotient m
def mixed : List FlatMatrix := ordered.filter isEssential
def normProfile (ms : List FlatMatrix) : List ℕ := (ms.map l1Norm).insertionSort (· ≤ ·)

/-- The eleven rows printed in Appendix A, in exactly the displayed order. -/
def essentialTable : List FlatMatrix :=
  [[-1, -1, -1, 0, 0, 0, 0, 1],
   [-1, -1, 0, 0, 0, 0, 1, 1],
   [-1, 0, -1, 0, 0, 1, 0, 1],
   [-2, -1, -1, -1, -1, 0, 0, 0],
   [-2, -1, -1, 0, -1, 0, 0, 1],
   [-2, -1, 0, -1, -1, 0, 1, 0],
   [-2, -1, 0, 0, -1, 0, 1, 1],
   [-2, 0, -1, -1, -1, 1, 0, 0],
   [-2, 0, -1, 0, -1, 1, 0, 1],
   [-2, 0, 0, -1, -1, 1, 1, 0],
   [-2, 0, 0, 0, -1, 1, 1, 1]]

theorem essential_table : mixed = essentialTable := by decide +kernel

/-- The C4 quotient has 29 classes, with the stated norm profile. -/
theorem class_count :
    ordered.length = 29 ∧
    normProfile ordered = List.replicate 1 2 ++ List.replicate 9 4 ++ List.replicate 19 6 := by
  decide +kernel

/-- Every listed class is additive and is its own C4 canonical form. -/
theorem classes_canonical :
    ordered.all isAdditive = true ∧
    ordered.all (fun m => m == canonicalC4 m) = true := by
  decide +kernel

/-- Appendix A's independent finite inequality: eleven essential classes,
minimum augmented energy eight. This is not the analytic Lemma 8.2. -/
theorem essential_energy :
    mixed.length = 11 ∧
    normProfile mixed = List.replicate 3 4 ++ List.replicate 8 6 ∧
    mixed.all (fun m => rowQuotient m == (m[4]! - m[0]!).natAbs) = true ∧
    mixed.all (fun m => decide (energy m > 6)) = true ∧
    (mixed.map energy).min? = some 8 := by
  rw [essential_table]
  decide +kernel

/-- Each column of the displayed table, including every augmented energy. -/
theorem essential_table_values :
    essentialTable.map (fun m => (l1Norm m, rowQuotient m, colQuotient m, energy m)) =
      [(4, 1, 1, 8), (4, 1, 2, 10), (4, 1, 2, 10),
       (6, 1, 1, 10), (6, 1, 2, 12), (6, 1, 2, 12),
       (6, 1, 3, 14), (6, 1, 2, 12), (6, 1, 3, 14),
       (6, 1, 3, 14), (6, 1, 2, 12)] := by decide +kernel

/-- The two-entry quotient in (A.6) is a minimum over all integer shifts. -/
theorem pair_quotient_minimum (d : ℤ) :
    (∃ c : ℤ, l1Norm [0 + c, d + c] = d.natAbs) ∧
    ∀ c : ℤ, d.natAbs ≤ l1Norm [0 + c, d + c] := by
  constructor
  · exact ⟨0, by simp [l1Norm]⟩
  · intro c
    simp only [l1Norm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- The finite coordinate-based computation of (A.5) agrees with its full
integer quantifier, for every essential row displayed in Appendix A. -/
theorem essential_column_minimum (m : FlatMatrix) (hm : m ∈ mixed) :
    (∃ c : ℤ, l1Norm ((m.take 4).map (fun x => x + c)) = colQuotient m) ∧
    ∀ c : ℤ, colQuotient m ≤ l1Norm ((m.take 4).map (fun x => x + c)) := by
  rw [essential_table] at hm
  simp only [essentialTable, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first
    | exact ⟨0, by decide +kernel⟩
    | exact ⟨1, by decide +kernel⟩
    | (intro c; simp [colQuotient, quotientL1Norm, l1Norm] <;> omega)

/-- The S4 refinement: 16 classes, so 13 of the 29 split. -/
theorem s4_quotient :
    (ordered.map canonicalS4).dedup.length = 16 ∧
    ordered.length - (ordered.map canonicalS4).dedup.length = 13 := by
  decide +kernel

/-- The list contains 24 distinct lists, each of length four and containing
all four column indices. This is an implementation check for the S4 diagnostic. -/
theorem allPerms_correct :
    allPerms.length = 24 ∧
    allPerms.dedup.length = 24 ∧
    allPerms.all (fun p => p.length == 4 && (List.range 4).all (fun i => p.contains i)) = true := by
  decide +kernel

/-- The diagnostic C4 cycle check carried over from the Python source. -/
theorem cycle_certificate :
    ([1, 3, 4, 2] : List ℕ).map (fun t => 3*t%5) = [3,4,2,1] ∧
    cyclicColumnOrders.dedup.length = 4 := by
  decide +kernel

#print axioms class_count
#print axioms classes_canonical
#print axioms essential_table
#print axioms essential_energy
#print axioms essential_table_values
#print axioms pair_quotient_minimum
#print axioms essential_column_minimum
#print axioms s4_quotient
#print axioms allPerms_correct
#print axioms cycle_certificate

end Certificates.Mixed35Direct
