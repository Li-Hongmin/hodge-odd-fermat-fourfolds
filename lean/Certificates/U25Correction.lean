import Certificates.AdditiveDirect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Fin

/-! R7 Theorem 7.3, equation (11); manuscript lines 955--984.
Exactly j=2, r=1: every odd integral v on U25 of norm 2,4,6, and all four
distinct signed five-fibre corrections. This is not the arbitrary-j proof.
-/
namespace Certificates.U25Correction
open Certificates.AdditiveDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def units : List ℕ := [1,2,3,4,6,7,8,9,11,12,13,14,16,17,18,19,21,22,23,24]
def encode (f : ℕ → ℤ) : List ℤ := [f 1,f 2,f 3,f 4,f 6,f 7,f 8,f 9,f 11,f 12]
def value (v : List ℤ) : ℕ → ℤ
  | 1 => v[0]! | 2 => v[1]! | 3 => v[2]! | 4 => v[3]!
  | 6 => v[4]! | 7 => v[5]! | 8 => v[6]! | 9 => v[7]!
  | 11 => v[8]! | 12 => v[9]!
  | 13 => -v[9]! | 14 => -v[8]! | 16 => -v[7]! | 17 => -v[6]!
  | 18 => -v[5]! | 19 => -v[4]! | 21 => -v[3]! | 22 => -v[2]!
  | 23 => -v[1]! | 24 => -v[0]! | _ => 0
def norm (f : ℕ → ℤ) : ℕ := (units.map fun x => (f x).natAbs).sum
def correction (z x : ℕ) : ℤ :=
  if x % 5 = z then 1 else if x % 5 = 5-z then -1 else 0
def difference (v : List ℤ) (x : ℕ) : ℤ := value v (3*x%25) - value v x
def overlap (v : List ℤ) (z : ℕ) : ℕ :=
  ((units.filter fun x => correction z x != 0).map fun x => (difference v x).natAbs).sum
def correctedNorm (v : List ℤ) (z : ℕ) : ℕ :=
  norm fun x => correction z x + difference v x
def vectors : List (List ℤ) := (topRows 10 3).filter fun v => 0 < l1Norm v
def checkPair (v : List ℤ) (z : ℕ) : Bool :=
  let k := 2 * l1Norm v
  decide (overlap v z ≤ k ∧ 10 ≤ correctedNorm v z + k ∧
    (k = 2 → 10 ≤ correctedNorm v z) ∧ 12 < 2*k + correctedNorm v z)

theorem units_exact (x : Fin 25) : x.val ∈ units ↔ Nat.gcd x.val 25 = 1 := by
  fin_cases x <;> decide +kernel

theorem odd_negatives (f : ℕ → ℤ) (hodd : ∀ x ∈ units, f (25-x) = -f x) :
    f 24 = -f 1 ∧ f 23 = -f 2 ∧ f 22 = -f 3 ∧ f 21 = -f 4 ∧
    f 19 = -f 6 ∧ f 18 = -f 7 ∧ f 17 = -f 8 ∧ f 16 = -f 9 ∧
    f 14 = -f 11 ∧ f 13 = -f 12 :=
  ⟨hodd 1 (by decide), hodd 2 (by decide), hodd 3 (by decide), hodd 4 (by decide),
   hodd 6 (by decide), hodd 7 (by decide), hodd 8 (by decide), hodd 9 (by decide),
   hodd 11 (by decide), hodd 12 (by decide)⟩

theorem reconstruct (f : ℕ → ℤ)
    (hodd : ∀ x ∈ units, f (25-x) = -f x) (x : Fin 25) (hx : x.val ∈ units) :
    value (encode f) x.val = f x.val := by
  obtain ⟨h1,h2,h3,h4,h6,h7,h8,h9,h11,h12⟩ := odd_negatives f hodd
  clear hodd
  fin_cases x <;> simp_all [units, value, encode]

theorem encode_norm (f : ℕ → ℤ) (hodd : ∀ x ∈ units, f (25-x) = -f x) :
    2 * l1Norm (encode f) = norm f := by
  obtain ⟨h1,h2,h3,h4,h6,h7,h8,h9,h11,h12⟩ := odd_negatives f hodd
  clear hodd
  simp_all [encode, l1Norm, norm, units, Int.natAbs_neg]
  omega

theorem mem_vectors (v : List ℤ) :
    v ∈ vectors ↔ v.length = 10 ∧ 0 < l1Norm v ∧ l1Norm v ≤ 3 := by
  simp [vectors, mem_topRows]
  tauto

theorem correction_count :
    (([1,2,3,4] : List ℕ).map fun z => units.map (correction z)).dedup.length = 4 ∧
    ([1,2,3,4] : List ℕ).all (fun z => norm (correction z) == 10) = true := by
  decide +kernel

theorem pairs_count : vectors.length = 1560 ∧ vectors.length * 4 = 6240 := by
  decide +kernel

-- Check each leaf as it is generated, without materializing the whole ball.
def checkTree (pre : List ℤ) : ℕ → ℕ → ℕ → Bool
  | 0, _, z => if l1Norm pre = 0 then true else checkPair pre z
  | n+1, b, z => (signedRange b).all fun x =>
      checkTree (pre ++ [x]) n (b-x.natAbs) z

theorem checkTree_sound (n : ℕ) (pre tail : List ℤ) (b z : ℕ)
    (hcheck : checkTree pre n b z = true) (htail : tail ∈ topRows n b)
    (hpos : 0 < l1Norm (pre ++ tail)) : checkPair (pre ++ tail) z = true := by
  induction n generalizing pre tail b with
  | zero =>
    have heq : tail = [] := by simpa [topRows] using htail
    subst tail
    simpa [checkTree, show l1Norm pre ≠ 0 by simpa using Nat.ne_of_gt hpos] using hcheck
  | succ n ih =>
    simp only [topRows, List.mem_flatMap, List.mem_map] at htail
    obtain ⟨x,hx,rest,hrest,rfl⟩ := htail
    have hc := List.all_eq_true.mp hcheck x hx
    have hp : 0 < l1Norm ((pre ++ [x]) ++ rest) := by simpa using hpos
    simpa using ih (pre ++ [x]) rest (b-x.natAbs) hc hrest hp

theorem tree_checked (z : Fin 4) : checkTree [] 10 3 (z.val+1) = true := by
  fin_cases z <;> decide +kernel

theorem all_for_correction (z : Fin 4) :
    vectors.all (fun v => checkPair v (z.val+1)) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  have h := (mem_vectors v).mp hv
  exact checkTree_sound 10 [] v 3 (z.val+1) (tree_checked z)
    ((mem_topRows v 10 3).mpr ⟨h.1,h.2.2⟩) h.2.1

theorem all_pairs : vectors.all (fun v => ([1,2,3,4] : List ℕ).all (checkPair v)) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  apply List.all_eq_true.mpr
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp (all_for_correction 0) v hv
  · exact List.all_eq_true.mp (all_for_correction 1) v hv
  · exact List.all_eq_true.mp (all_for_correction 2) v hv
  · exact List.all_eq_true.mp (all_for_correction 3) v hv

/-- No bound on individual coefficients is assumed beyond the full norm. -/
theorem correction_estimate (v : List ℤ) (hv : v.length = 10)
    (hk : 0 < l1Norm v ∧ l1Norm v ≤ 3) (z : ℕ) (hz : z ∈ [1,2,3,4]) :
    overlap v z ≤ 2*l1Norm v ∧ 10 ≤ correctedNorm v z + 2*l1Norm v ∧
    (2*l1Norm v = 2 → 10 ≤ correctedNorm v z) ∧
    12 < 4*l1Norm v + correctedNorm v z := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp all_pairs v ((mem_vectors v).mpr ⟨hv,hk⟩)) z hz
  simpa only [checkPair, decide_eq_true_eq, ← Nat.mul_assoc] using h

/-- Every odd function of the manuscript's full norm is covered by all_pairs. -/
theorem covers_odd_functions (f : ℕ → ℤ)
    (hodd : ∀ x ∈ units, f (25-x) = -f x)
    (hk : norm f = 2 ∨ norm f = 4 ∨ norm f = 6) : encode f ∈ vectors := by
  apply (mem_vectors (encode f)).mpr
  have hn := encode_norm f hodd
  refine ⟨by simp [encode], ?_, ?_⟩ <;> omega

theorem vectors_nodup : vectors.Nodup := (topRows_nodup 10 3).filter _

/-- Equation (11) and its k=2 refinement, on the manuscript's actual functions. -/
theorem estimate_on_U25 (f : ℕ → ℤ)
    (hodd : ∀ x ∈ units, f (25-x) = -f x)
    (hk : norm f = 2 ∨ norm f = 4 ∨ norm f = 6)
    (z : ℕ) (hz : z ∈ [1,2,3,4]) :
    let g := fun x => f (3*x%25) - f x
    let d := norm (fun x => correction z x + g x)
    ((units.filter fun x => correction z x != 0).map fun x => (g x).natAbs).sum ≤ norm f ∧
      10 ≤ d + norm f ∧ (norm f = 2 → 10 ≤ d) ∧ 12 < 2*norm f + d := by
  have hv := (mem_vectors (encode f)).mp (covers_odd_functions f hodd hk)
  have h := correction_estimate (encode f) hv.1 ⟨hv.2.1,hv.2.2⟩ z hz
  have hxlt : ∀ x ∈ units, x < 25 := by intro x hx; simp [units] at hx; omega
  have hmul : ∀ x ∈ units, 3*x%25 ∈ units := by
    intro x hx
    have hx' : (⟨x,hxlt x hx⟩ : Fin 25).val ∈ units := hx
    have hall : ∀ t : Fin 25, t.val ∈ units → 3*t.val%25 ∈ units := by
      decide +kernel
    exact hall ⟨x,hxlt x hx⟩ hx'
  have hg : ∀ x ∈ units, difference (encode f) x = f (3*x%25) - f x := by
    intro x hx
    unfold difference
    rw [reconstruct f hodd ⟨x,hxlt x hx⟩ hx,
      reconstruct f hodd ⟨3*x%25,Nat.mod_lt _ (by decide)⟩ (hmul x hx)]
  have hd : correctedNorm (encode f) z = norm (fun x => correction z x + (f (3*x%25) - f x)) := by
    unfold correctedNorm norm
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    simp only [hg x hx]
  have ho : overlap (encode f) z =
      ((units.filter fun x => correction z x != 0).map fun x => (f (3*x%25) - f x).natAbs).sum := by
    unfold overlap
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    simp only [hg x (List.mem_filter.mp hx).1]
  dsimp
  rw [← hd, ← ho, ← encode_norm f hodd]
  simpa [← Nat.mul_assoc] using h

end Certificates.U25Correction
