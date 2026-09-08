import Certificates.AdditiveDirect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! R7 Theorem 7.5, equation (15), manuscript lines 1158--1183.
v stores 2u on 1,...,(p-1)/2; c stores 2c. Odd integers encode strict
half-integers exactly. The enumeration uses the first-term budget <=6,
including coefficients ±3; it does not assume the conclusion |2u|=1.
-/
namespace Certificates.HalfIntegralPotentials
open Certificates.AdditiveDirect
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def value (p : ℕ) (v : List ℤ) (x : ℕ) : ℤ :=
  if x ≤ (p-1)/2 then v[x-1]! else -v[p-x-1]!
def base (v : List ℤ) (c : ℤ) : ℕ := (v.map fun x => max x.natAbs c.natAbs).sum
def variation (p : ℕ) (v : List ℤ) : ℕ :=
  ((List.range' 1 ((p-1)/2)).map fun x =>
    (value p v (3*x%p) - value p v x).natAbs).sum
def twiceEnergy (p : ℕ) (v : List ℤ) (c : ℤ) : ℕ := 2 * base v c + variation p v
def oddCoefficients (v : List ℤ) : Bool := v.all fun x => x % 2 == 1
def oddRows : ℕ → ℕ → List (List ℤ)
  | 0, _ => [[]]
  | n+1, b => ((signedRange b).filter fun x => x % 2 == 1).flatMap fun x =>
      (oddRows n (b-x.natAbs)).map (x :: ·)

theorem mem_oddRows (v : List ℤ) (n b : ℕ) :
    v ∈ oddRows n b ↔ v.length = n ∧ l1Norm v ≤ b ∧ ∀ x ∈ v, x % 2 = 1 := by
  induction n generalizing v b with
  | zero => cases v <;> simp [oddRows, l1Norm]
  | succ n ih =>
    cases v with
    | nil => simp [oddRows]
    | cons x xs =>
      simp only [oddRows, List.mem_flatMap, List.mem_filter, List.mem_map,
        List.cons.injEq, exists_eq_right_right, mem_signedRange, beq_iff_eq,
        ih, List.length_cons, l1Norm, List.map_cons, List.sum_cons,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨hx,ho⟩,hlen,hn,hs⟩
        exact ⟨by omega, by omega, ho, hs⟩
      · rintro ⟨hlen,hn,ho,hs⟩
        exact ⟨⟨by omega,ho⟩,by omega,by omega,hs⟩

theorem oddRows_nodup (n b : ℕ) : (oddRows n b).Nodup := by
  induction n generalizing b with
  | zero => simp [oddRows]
  | succ n ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun x _ => (ih (b-x.natAbs)).map (fun _ _ h => (List.cons.inj h).2),
      ((signedRange_nodup b).filter _).imp ?_⟩
    intro x y hxy xs hx hy
    obtain ⟨rest,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨rest',_,heq⟩ := List.mem_map.mp hy
    exact hxy (List.cons.inj heq).1.symm

def potentials (p : ℕ) : List (List ℤ) :=
  oddRows ((p-1)/2) 6
def accepted (p : ℕ) : List (List ℤ × ℤ) :=
  (potentials p).flatMap fun v => ([-1,1] : List ℤ).filterMap fun c =>
    if twiceEnergy p v c ≤ 12 then some (v,c) else none
def conclusion (p : ℕ) (v : List ℤ) (c : ℤ) : Bool :=
  c.natAbs == 1 && v.all (fun x => x.natAbs == 1) &&
    (if p = 7 then twiceEnergy p v c == 8 || twiceEnergy p v c == 12
     else variation p v == 0 && twiceEnergy p v c == p-1)

theorem norm_le_base (v : List ℤ) (c : ℤ) : l1Norm v ≤ base v c := by
  induction v with
  | nil => simp [l1Norm, base]
  | cons x xs ih =>
    simp only [l1Norm, base, List.map_cons, List.sum_cons] at *
    have h := Nat.le_max_left x.natAbs c.natAbs
    omega

theorem constant_le_base (v : List ℤ) (c : ℤ) : v.length * c.natAbs ≤ base v c := by
  induction v with
  | nil => simp [base]
  | cons x xs ih =>
    simp only [base, List.length_cons, List.map_cons, List.sum_cons] at *
    have h := Nat.le_max_right x.natAbs c.natAbs
    rw [Nat.add_mul]
    omega

theorem mem_potentials (p : ℕ) (v : List ℤ) :
    v ∈ potentials p ↔ v.length = (p-1)/2 ∧ l1Norm v ≤ 6 ∧
      ∀ x ∈ v, x % 2 = 1 := by
  exact mem_oddRows v ((p-1)/2) 6

/-- The energy hypothesis itself supplies the finite budget and both signs of c. -/
theorem budget_covers (p : ℕ) (hp : p = 7 ∨ p = 11 ∨ p = 13)
    (v : List ℤ) (c : ℤ) (hlen : v.length = (p-1)/2)
    (hodd : ∀ x ∈ v, x % 2 = 1) (hc : c % 2 = 1)
    (he : twiceEnergy p v c ≤ 12) : v ∈ potentials p ∧ c ∈ [-1,1] := by
  have hbase : base v c ≤ 6 := by unfold twiceEnergy at he; omega
  have hn := norm_le_base v c
  have hconst := constant_le_base v c
  have hcabs : c.natAbs ≤ 2 := by
    rcases hp with rfl | rfl | rfl <;> norm_num at hlen <;> rw [hlen] at hconst <;> omega
  refine ⟨(mem_potentials p v).mpr ⟨hlen, by omega, hodd⟩, ?_⟩
  simp only [List.mem_cons]
  omega

theorem finite_classification :
    ([7,11,13] : List ℕ).all (fun p =>
      (accepted p).all fun vc => conclusion p vc.1 vc.2) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem exact_counts :
    (accepted 7).length = 16 ∧ (accepted 11).length = 4 ∧ (accepted 13).length = 8 ∧
    ((accepted 7).filter fun vc => twiceEnergy 7 vc.1 vc.2 == 8).length = 12 ∧
    ((accepted 7).filter fun vc => twiceEnergy 7 vc.1 vc.2 == 12).length = 4 := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Arbitrary strict half-integral odd potentials under (15), not a sampled box. -/
theorem bounded_half_integral (p : ℕ) (hp : p = 7 ∨ p = 11 ∨ p = 13)
    (v : List ℤ) (c : ℤ) (hlen : v.length = (p-1)/2)
    (hodd : ∀ x ∈ v, x % 2 = 1) (hc : c % 2 = 1)
    (he : twiceEnergy p v c ≤ 12) : conclusion p v c = true := by
  have hcover := budget_covers p hp v c hlen hodd hc he
  have hmem : (v,c) ∈ accepted p := by
    simp only [accepted, List.mem_flatMap]
    refine ⟨v,hcover.1,?_⟩
    simp only [List.mem_filterMap]
    exact ⟨c,hcover.2,by simp [he]⟩
  have hp' : p ∈ ([7,11,13] : List ℕ) := by simpa using hp
  exact List.all_eq_true.mp (List.all_eq_true.mp finite_classification p hp') (v,c) hmem

end Certificates.HalfIntegralPotentials
