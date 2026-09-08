import Certificates.AdditiveDirect
import Mathlib.Data.List.Sort
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Basic

/-!
# The 2 × 4 cyclic additive certificate

The Hodge Conjecture for Odd-Degree Fermat Fourfolds, Appendix A (A.1–A.7)
and its independent finite energy inequality. The reconstructed Lemma 8.2
uses an analytic proof and does not identify this invariant with actual mass.
Source: calculations/bundles/fermat-level15m-mixed35-c4-additive-classification/
verify_mixed35_c4_additive_classification.py.

The domain is ALL nonzero integer 2 × 4 additive matrices of l1 norm at most 6.
Equivalence uses row swap, C4 column rotation, and global sign, exactly as in
the Python source. The S4 quotient is only a diagnostic. Neither the Fourier
reduction to this domain nor the physical edge-cost argument is formalized.

STATUS: superseded for certification purposes. `certificateStatement` below is
an UNPROVED proposition in THIS module: evaluating it over `integerL1Ball 8 6`
(40081 vectors) exhausts kernel memory, and Lean 4.32.0's `native_decide`
introduces a private axiom, which this repository does not accept.

The same classification IS kernel-proved in `Certificates.Mixed35Direct`, which
runs it over the budget-pruned enumerator of `Certificates.AdditiveDirect`.
`mem_additiveMatrices_iff` below proves the two domains coincide. See
`Mixed35Direct.class_count`, `classes_canonical`, `essential_energy` and
`s4_quotient` for the 29 / 11 / 8 results.
-/

namespace Certificates.Mixed35

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
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hx
    refine ⟨(x + b).toNat, ?_, ?_⟩ <;> omega

def integerL1Ball : ℕ → ℕ → List FlatMatrix
  | 0, _ => [[]]
  | n + 1, b => (signedRange b).flatMap fun x =>
      (integerL1Ball n (b - x.natAbs)).map (x :: ·)

/-- The recursive enumerator contains exactly the entire integer l1 ball. -/
theorem mem_integerL1Ball (xs : List ℤ) (n b : ℕ) :
    xs ∈ integerL1Ball n b ↔ xs.length = n ∧ l1Norm xs ≤ b := by
  induction n generalizing xs b with
  | zero => cases xs <;> simp [integerL1Ball, l1Norm]
  | succ n ih =>
    cases xs with
    | nil => simp [integerL1Ball]
    | cons x xs =>
      simp only [integerL1Ball, List.mem_flatMap, List.mem_map,
        List.cons.injEq, exists_eq_right_right,
        mem_signedRange, ih, List.length_cons, l1Norm,
        List.map_cons, List.sum_cons]
      omega

/-- Scalar recurrence for the full ball cardinality; no vectors are discarded. -/
def integerBallCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, b => ((signedRange b).map fun x => integerBallCount n (b - x.natAbs)).sum

theorem integerL1Ball_length (n b : ℕ) :
    (integerL1Ball n b).length = integerBallCount n b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [integerL1Ball, List.length_flatMap, List.length_map,
      ih, integerBallCount]

theorem integerL1Ball_eq_topRows (n b : ℕ) :
    integerL1Ball n b = Certificates.AdditiveDirect.topRows n b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [integerL1Ball, Certificates.AdditiveDirect.topRows,
      ih, signedRange, Certificates.AdditiveDirect.signedRange]

/-- Appendix A, R7 md:1723: all 40081 distinct points of Z^8, norm at most six. -/
theorem integerL1Ball_card :
    (integerL1Ball 8 6).length = 40081 ∧ (integerL1Ball 8 6).Nodup := by
  constructor
  · rw [integerL1Ball_length]
    decide +kernel
  · rw [integerL1Ball_eq_topRows]
    exact Certificates.AdditiveDirect.topRows_nodup 8 6

def isAdditive (m : FlatMatrix) : Bool :=
  m.length == 8 && ([1, 2, 3] : List ℕ).all fun j =>
    m[4+j]! - m[4]! == m[j]! - m[0]!

def transform (m : FlatMatrix) (rows columns : List ℕ) (sign : ℤ) : FlatMatrix :=
  rows.flatMap fun r => columns.map fun c => sign * m[4*r+c]!

def cyclicColumnOrders : List (List ℕ) :=
  (List.range 4).map fun s => (List.range 4).map fun c => (c+s)%4

def lexMin (xs : List FlatMatrix) : FlatMatrix := xs.foldl min xs.head!

def canonicalC4 (m : FlatMatrix) : FlatMatrix :=
  lexMin <| [[0, 1], [1, 0]].flatMap fun rows =>
    cyclicColumnOrders.flatMap fun columns =>
      ([1, -1] : List ℤ).map fun s => transform m rows columns s

def canonicalS4 (m : FlatMatrix) : FlatMatrix :=
  lexMin <| [[0, 1], [1, 0]].flatMap fun rows =>
    (List.range 4).permutations.flatMap fun columns =>
      ([1, -1] : List ℤ).map fun s => transform m rows columns s

def additiveMatrices : List FlatMatrix :=
  (integerL1Ball 8 6).filter fun m => l1Norm m != 0 && isAdditive m

/-- The retained full-ball definition and the kernel-practical enumerator
have identical membership, without any additional hypothesis or sampling. -/
theorem mem_additiveMatrices_iff (m : FlatMatrix) :
    m ∈ additiveMatrices ↔ m ∈ Certificates.AdditiveDirect.additiveDirect := by
  simp only [additiveMatrices, List.mem_filter, mem_integerL1Ball,
    Certificates.AdditiveDirect.mem_additiveDirect_iff,
    isAdditive, Certificates.AdditiveDirect.isAdditive,
    l1Norm, Certificates.AdditiveDirect.l1Norm,
    Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  constructor
  · rintro ⟨⟨hlen, hbound⟩, hpos, _, hadd⟩
    exact ⟨⟨hlen, hadd⟩, by omega, hbound⟩
  · rintro ⟨⟨hlen, hadd⟩, hpos, hbound⟩
    exact ⟨⟨hlen, hbound⟩, by omega, hlen, hadd⟩

def c4Classes : List FlatMatrix := (additiveMatrices.map canonicalC4).dedup

def ordered : List FlatMatrix :=
  c4Classes.insertionSort fun a b =>
    l1Norm a < l1Norm b ∨ (l1Norm a = l1Norm b ∧ a ≤ b)

def potentialMatrix (a d c₁ c₂ c₃ : ℤ) : FlatMatrix :=
  [a, a+c₁, a+c₂, a+c₃, a+d, a+c₁+d, a+c₂+d, a+c₃+d]

def potentialMatrices : List FlatMatrix :=
  (signedRange 6).flatMap fun a => (signedRange 12).flatMap fun d =>
    (signedRange 12).flatMap fun c₁ => (signedRange 12).flatMap fun c₂ =>
      (signedRange 12).flatMap fun c₃ =>
        let m := potentialMatrix a d c₁ c₂ c₃
        if 0 < l1Norm m ∧ l1Norm m ≤ 6 then [m] else []

def potentialClasses : List FlatMatrix := (potentialMatrices.map canonicalC4).dedup

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

theorem cycle_certificate :
    ([1, 3, 4, 2] : List ℕ).map (fun t => 3*t%5) = [3,4,2,1] ∧
    cyclicColumnOrders.dedup.length = 4 := by decide +kernel

/-- The exact ordered Python payload, not a list of sampled matrices. -/
def expectedTable : List FlatMatrix := [
  [-1, 0, 0, 0, -1, 0, 0, 0],
  [-2, 0, 0, 0, -2, 0, 0, 0],
  [-1, -1, -1, -1, 0, 0, 0, 0],
  [-1, -1, -1, 0, 0, 0, 0, 1],
  [-1, -1, 0, 0, -1, -1, 0, 0],
  [-1, -1, 0, 0, 0, 0, 1, 1],
  [-1, 0, -1, 0, -1, 0, -1, 0],
  [-1, 0, -1, 0, 0, 1, 0, 1],
  [-1, 0, 0, 1, -1, 0, 0, 1],
  [-1, 0, 1, 0, -1, 0, 1, 0],
  [-3, 0, 0, 0, -3, 0, 0, 0],
  [-2, -1, -1, -1, -1, 0, 0, 0],
  [-2, -1, -1, 0, -1, 0, 0, 1],
  [-2, -1, 0, -1, -1, 0, 1, 0],
  [-2, -1, 0, 0, -2, -1, 0, 0],
  [-2, -1, 0, 0, -1, 0, 1, 1],
  [-2, 0, -1, -1, -1, 1, 0, 0],
  [-2, 0, -1, 0, -2, 0, -1, 0],
  [-2, 0, -1, 0, -1, 1, 0, 1],
  [-2, 0, 0, -1, -2, 0, 0, -1],
  [-2, 0, 0, -1, -1, 1, 1, 0],
  [-2, 0, 0, 0, -1, 1, 1, 1],
  [-2, 0, 0, 1, -2, 0, 0, 1],
  [-2, 0, 1, 0, -2, 0, 1, 0],
  [-2, 1, 0, 0, -2, 1, 0, 0],
  [-1, -1, -1, 0, -1, -1, -1, 0],
  [-1, -1, 0, 1, -1, -1, 0, 1],
  [-1, -1, 1, 0, -1, -1, 1, 0],
  [-1, 0, -1, 1, -1, 0, -1, 1]]

/-- Unproved mathematical assertions of the Python verifier. No theorem
establishes this proposition. The SHA-256 integrity check remains in Python. -/
def certificateStatement : Prop :=
  c4Classes.toFinset = potentialClasses.toFinset ∧
  potentialMatrices.all isAdditive = true ∧
  ordered.all isAdditive = true ∧
  ordered.all (fun m => m == canonicalC4 m) = true ∧
  ordered.length = 29 ∧
  normProfile ordered = List.replicate 1 2 ++ List.replicate 9 4 ++ List.replicate 19 6 ∧
  mixed.length = 11 ∧
  normProfile mixed = List.replicate 3 4 ++ List.replicate 8 6 ∧
  mixed.all (fun m => rowQuotient m == (m[4]! - m[0]!).natAbs) = true ∧
  mixed.all (fun m => energy m > 6) = true ∧
  (mixed.map energy).min? = some 8 ∧
  (ordered.map canonicalS4).dedup.length = 16 ∧
  ordered.length - (ordered.map canonicalS4).dedup.length = 13

#print axioms mem_signedRange
#print axioms mem_integerL1Ball
#print axioms mem_additiveMatrices_iff
#print axioms cycle_certificate

end Certificates.Mixed35
