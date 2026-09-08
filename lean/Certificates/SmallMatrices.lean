import Certificates.AdditiveDirect

/-!
# The three small integral additive matrix classifications

R7 manuscript Lemma 6.1, lines 778–808.
Matrices are stored column-major. `IsAdditive` allows arbitrary integer row
and column potentials: `integerPotentials_normalize` proves the normalized
representation used here loses no such matrix. `mem_matrices` proves exact
coverage, including zero and repeated complete columns; the finite kernels
then check all matrices, never samples or orbit representatives.
-/

namespace Certificates.SmallMatrices

open Certificates.AdditiveDirect (l1Norm signedRange mem_signedRange)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev FlatMatrix := List ℤ

def column (offsets : List ℤ) (top : ℤ) : List ℤ :=
  top :: offsets.map (top + ·)

def ofParams (offsets tops : List ℤ) : FlatMatrix :=
  tops.flatMap (column offsets)

/-- An integral additive `rows × cols` matrix, with unrestricted potentials. -/
def IsAdditive (rows cols : ℕ) (m : FlatMatrix) : Prop :=
  ∃ offsets tops : List ℤ,
    offsets.length + 1 = rows ∧ tops.length = cols ∧ m = ofParams offsets tops

/-- Normalizing the first row potential to zero preserves every entry. -/
theorem integerPotentials_normalize (first : ℤ) (rest cols : List ℤ) :
    cols.flatMap (fun v => (first :: rest).map (· + v)) =
      ofParams (rest.map (· - first)) (cols.map (first + ·)) := by
  simp only [ofParams, List.flatMap_map]
  apply List.flatMap_congr
  intro v _
  simp only [column, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  dsimp only [Function.comp_apply]
  omega

theorem norm_append (xs ys : List ℤ) :
    l1Norm (xs ++ ys) = l1Norm xs + l1Norm ys := by
  simp [l1Norm, List.sum_append]

theorem norm_params_cons (ds : List ℤ) (x : ℤ) (xs : List ℤ) :
    l1Norm (ofParams ds (x :: xs)) =
      l1Norm (column ds x) + l1Norm (ofParams ds xs) := by
  simp only [ofParams, List.flatMap_cons, norm_append]

theorem entry_norm_le (x : ℤ) (xs : List ℤ) (h : x ∈ xs) :
    x.natAbs ≤ l1Norm xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    simp only [l1Norm, List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h
      unfold l1Norm at this
      omega

def offsetBox : ℕ → ℕ → List (List ℤ)
  | 0, _ => [[]]
  | n + 1, b => (signedRange b).flatMap fun x =>
      (offsetBox n b).map (x :: ·)

theorem mem_offsetBox (xs : List ℤ) (n b : ℕ) :
    xs ∈ offsetBox n b ↔ xs.length = n ∧ ∀ x ∈ xs, x.natAbs ≤ b := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [offsetBox]
  | succ n ih =>
    cases xs with
    | nil => simp [offsetBox]
    | cons x xs =>
      simp only [offsetBox, List.mem_flatMap, List.mem_map,
        List.cons.injEq, exists_eq_right_right, mem_signedRange, ih,
        List.length_cons, List.mem_cons, forall_eq_or_imp]
      aesop

def boundedTopRows (ds : List ℤ) : ℕ → ℕ → List (List ℤ)
  | 0, _ => [[]]
  | n + 1, b =>
      ((signedRange b).filter fun x => decide (l1Norm (column ds x) ≤ b)).flatMap
        fun x => (boundedTopRows ds n (b - l1Norm (column ds x))).map (x :: ·)

/-- Exact budget pruning: every top row of an admissible matrix occurs. -/
theorem mem_boundedTopRows (ds xs : List ℤ) (n b : ℕ) :
    xs ∈ boundedTopRows ds n b ↔
      xs.length = n ∧ l1Norm (ofParams ds xs) ≤ b := by
  induction n generalizing xs b with
  | zero => cases xs <;> simp [boundedTopRows, ofParams, l1Norm]
  | succ n ih =>
    cases xs with
    | nil => simp [boundedTopRows]
    | cons x xs =>
      have hx : x.natAbs ≤ l1Norm (column ds x) := by
        simp [column, l1Norm]
      simp only [boundedTopRows, List.mem_flatMap, List.mem_filter,
        List.mem_map, decide_eq_true_eq, mem_signedRange,
        List.cons.injEq, exists_eq_right_right, ih,
        List.length_cons, norm_params_cons]
      omega

/-- An offset is a difference of two entries in the first column. Its
    bound follows from the total norm, without an extra domain hypothesis. -/
theorem offset_bound (ds xs : List ℤ) (b : ℕ) (hne : xs ≠ [])
    (h : l1Norm (ofParams ds xs) ≤ b) :
    ∀ d ∈ ds, d.natAbs ≤ b := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    intro d hd
    have hm : x + d ∈ ds.map (x + ·) := List.mem_map.mpr ⟨d, hd, rfl⟩
    have he := entry_norm_le (x + d) (ds.map (x + ·)) hm
    rw [norm_params_cons] at h
    simp only [column, l1Norm, List.map_cons, List.sum_cons] at h
    unfold l1Norm at he
    omega

def matrices (rows cols b : ℕ) : List FlatMatrix :=
  (offsetBox (rows - 1) b).flatMap fun ds =>
    (boundedTopRows ds cols b).map (ofParams ds)

/-- Exhaustive coverage of all integral additive matrices of the given norm. -/
theorem mem_matrices (rows cols b : ℕ) (hr : 0 < rows) (hc : 0 < cols)
    (m : FlatMatrix) :
    m ∈ matrices rows cols b ↔ IsAdditive rows cols m ∧ l1Norm m ≤ b := by
  simp only [matrices, List.mem_flatMap, List.mem_map, mem_offsetBox,
    mem_boundedTopRows]
  constructor
  · rintro ⟨ds, ⟨hd, _⟩, xs, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨ds, xs, ?_, hx, rfl⟩, hn⟩
    omega
  · rintro ⟨⟨ds, xs, hd, hx, rfl⟩, hn⟩
    have hne : xs ≠ [] := by intro h; simp [h] at hx; omega
    exact ⟨ds, ⟨by omega, offset_bound ds xs b hne hn⟩, xs, ⟨hx, hn⟩, rfl⟩

def rowInvariant (rows cols : ℕ) (m : FlatMatrix) : Bool :=
  (List.range cols).all fun c =>
    (List.range rows).all fun r => m[rows*c+r]! == m[rows*c]!

def columnInvariant (rows cols : ℕ) (m : FlatMatrix) : Bool :=
  (List.range cols).all fun c =>
    (List.range rows).all fun r => m[rows*c+r]! == m[r]!

def completeRow (rows cols : ℕ) (m : FlatMatrix) : Bool :=
  (List.range rows).any fun active => ([-1, 1] : List ℤ).any fun sign =>
    (List.range cols).all fun c => (List.range rows).all fun r =>
      m[rows*c+r]! == if r = active then sign else 0

def essential (rows cols : ℕ) (m : FlatMatrix) : Bool :=
  !rowInvariant rows cols m && !columnInvariant rows cols m

def classification34 (m : FlatMatrix) : Bool :=
  rowInvariant 3 4 m || completeRow 3 4 m ||
    (essential 3 4 m &&
      ((l1Norm m == 5 && m.sum.natAbs == 1) ||
       (l1Norm m == 6 && m.sum.natAbs == 2)))

def classification35 (m : FlatMatrix) : Bool :=
  rowInvariant 3 5 m || completeRow 3 5 m ||
    (essential 3 5 m && l1Norm m == 6 && m.sum.natAbs == 2)

def classification25 (m : FlatMatrix) : Bool :=
  (rowInvariant 2 5 m && l1Norm m % 2 == 0) ||
    (l1Norm m == 5 && (List.range 5).all fun c =>
      (m[2*c]! == 0 && m[2*c+1]!.natAbs == 1) ||
      (m[2*c]!.natAbs == 1 && m[2*c+1]! == 0))

def nonzeroMatrices (rows cols : ℕ) : List FlatMatrix :=
  (matrices rows cols 6).filter (fun m => decide (0 < l1Norm m))

theorem small_matrix_counts :
    (nonzeroMatrices 3 4).length = 106 ∧
    (nonzeroMatrices 3 5).length = 96 ∧
    (nonzeroMatrices 2 5).length = 294 := by
  decide +kernel

theorem small_matrix_nodup :
    (matrices 3 4 6).dedup.length = (matrices 3 4 6).length ∧
    (matrices 3 5 6).dedup.length = (matrices 3 5 6).length ∧
    (matrices 2 5 6).dedup.length = (matrices 2 5 6).length := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem small_matrix_classification_kernel :
    (matrices 3 4 6).all classification34 = true ∧
    (matrices 3 5 6).all classification35 = true ∧
    (matrices 2 5 6).all classification25 = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Lemma 6.1: every integral additive 3 × 4 matrix, including zero. -/
theorem small_matrix_3x4 (m : FlatMatrix) (ha : IsAdditive 3 4 m)
    (hn : l1Norm m ≤ 6) : classification34 m = true := by
  exact List.all_eq_true.mp small_matrix_classification_kernel.1 m
    ((mem_matrices 3 4 6 (by decide) (by decide) m).mpr ⟨ha, hn⟩)

/-- Lemma 6.1: every integral additive 3 × 5 matrix, including zero. -/
theorem small_matrix_3x5 (m : FlatMatrix) (ha : IsAdditive 3 5 m)
    (hn : l1Norm m ≤ 6) : classification35 m = true := by
  exact List.all_eq_true.mp small_matrix_classification_kernel.2.1 m
    ((mem_matrices 3 5 6 (by decide) (by decide) m).mpr ⟨ha, hn⟩)

/-- Lemma 6.1: every integral additive 2 × 5 matrix, including zero. -/
theorem small_matrix_2x5 (m : FlatMatrix) (ha : IsAdditive 2 5 m)
    (hn : l1Norm m ≤ 6) : classification25 m = true := by
  exact List.all_eq_true.mp small_matrix_classification_kernel.2.2 m
    ((mem_matrices 2 5 6 (by decide) (by decide) m).mpr ⟨ha, hn⟩)

#print axioms integerPotentials_normalize
#print axioms norm_append
#print axioms norm_params_cons
#print axioms entry_norm_le
#print axioms mem_offsetBox
#print axioms mem_boundedTopRows
#print axioms offset_bound
#print axioms mem_matrices
#print axioms small_matrix_counts
#print axioms small_matrix_nodup
#print axioms small_matrix_classification_kernel
#print axioms small_matrix_3x4
#print axioms small_matrix_3x5
#print axioms small_matrix_2x5

end Certificates.SmallMatrices
