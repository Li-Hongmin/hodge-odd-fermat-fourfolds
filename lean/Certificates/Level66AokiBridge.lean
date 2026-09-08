import Mathlib.Data.List.Sections
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Card

/-!
# The exceptional level-33 block via level 66: finite character arithmetic

This module corresponds to the finite data in Section 9.2, lines
1539--1569, of the R7 *The Hodge Conjecture for Odd-Degree Fermat Fourfolds*.
The certificate is attributed there to Jumagulov, Theorem 1.4; the
module name is retained for import compatibility.
Its arithmetic definitions reuse
`calculations/bundles/fermat-x33-level66-aoki/verify_level66_aoki_bridge.py`.

The level is exactly 66.  The Hodge sums run over every integer t with
1 <= t < 66 and gcd(t, 66) = 1, for the five fixed characters a, Q, beta,
gamma, S.  The other assertions are the two fixed multiset identities,
three fixed self-pairs, the displayed inflation from level 33 to 66, and the
cardinality and a-character parity of the image of all 64 binary six-tuples
under e_i -> e_i XOR e_0.  No range is sampled or reduced.

Only these finite arithmetic assertions are formalized.  In particular,
the Aoki and Lefschetz theorems, geometric quotient and push--pull formula,
unit-group isomorphism and stabilizer arguments, and the algebraicity of
the complete rational block remain outside this module.
-/

namespace Certificates.Level66AokiBridge

def modulus : ℕ := 66

def units : List ℕ :=
  (List.range' 1 (modulus - 1)).filter fun t => Nat.gcd t modulus == 1

def w : List ℕ := [1, 4, 16, 22, 25, 31]
def a : List ℕ := w.map fun x => (2 * x) % modulus
def Q : List ℕ := [1, 25, 44, 62]
def S : List ℕ := [2, 8, 32, 41, 50, 65]
def delta0 : List ℕ := [1, 65, 25, 41]
def beta : List ℕ := [2, 32, 33, 65]
def gamma : List ℕ := [8, 33, 41, 50]
def delta1 : List ℕ := [33, 33]

def hodgeSums (character : List ℕ) : List ℕ :=
  units.map fun t => (character.map fun x => (t * x) % modulus).sum

def isSelfPair (x y : ℕ) : Bool :=
  decide (0 < x ∧ x < modulus ∧ 0 < y ∧ y < modulus) && (x + y) % modulus == 0

def bitVectors : List (List ℕ) := (List.replicate 6 [0, 1]).sections

def quotientSigns : Finset (List ℕ) :=
  (bitVectors.map fun bits => bits.map fun e => Nat.xor e (bits.headD 0)).toFinset

def signExponent (signs : List ℕ) : ℕ :=
  ((signs.zip a).map fun pair => pair.1 * pair.2).sum

-- Python line 31.
theorem units_card : units.length = 20 := by decide

-- Python line 32.
theorem hodge_a :
    a.length = 6 ∧ (∀ x ∈ a, 0 < x ∧ x < modulus) ∧
    hodgeSums a = List.replicate units.length (3 * modulus) := by decide +kernel

-- Python lines 33--34: all three iterations of the surface-character loop.
theorem hodge_surfaces :
    ∀ C ∈ [Q, beta, gamma],
      C.length = 4 ∧ (∀ x ∈ C, 0 < x ∧ x < modulus) ∧
      hodgeSums C = List.replicate units.length (2 * modulus) := by decide +kernel

-- Python line 35.
theorem hodge_S :
    S.length = 6 ∧ (∀ x ∈ S, 0 < x ∧ x < modulus) ∧
    hodgeSums S = List.replicate units.length (3 * modulus) := by decide +kernel

-- Python lines 37--38: equality retains every multiplicity.
theorem bridge_a :
    ((a ++ delta0 : List ℕ) : Multiset ℕ) = ((Q ++ S : List ℕ) : Multiset ℕ) := by decide

theorem bridge_S :
    ((S ++ delta1 : List ℕ) : Multiset ℕ) =
      ((beta ++ gamma : List ℕ) : Multiset ℕ) := by decide

-- Python lines 45--47.
theorem delta0_first_self_pair : isSelfPair 1 65 = true := by decide +kernel
theorem delta0_second_self_pair : isSelfPair 25 41 = true := by decide +kernel
theorem delta1_self_pair : isSelfPair 33 33 = true := by decide +kernel

-- R7 manuscript lines 1502 and 1540--1547: the exceptional tuple is doubled.
theorem target_inflation :
    w = [1,4,16,22,25,31] ∧ a = w.map (fun x => (2*x)%66) ∧
    a = [2,8,32,44,50,62] := by decide +kernel

-- Python lines 53--57: the set image of all binary six-tuples.
theorem quotient_signs_card : quotientSigns.card = 32 := by decide

-- Python lines 59--60: every element of that set, for the fixed character a.
theorem quotient_signs_trivial :
    ∀ signs ∈ quotientSigns, signExponent signs % 2 = 0 := by decide

#print axioms units_card
#print axioms hodge_a
#print axioms hodge_surfaces
#print axioms hodge_S
#print axioms bridge_a
#print axioms bridge_S
#print axioms delta0_first_self_pair
#print axioms delta0_second_self_pair
#print axioms delta1_self_pair
#print axioms target_inflation
#print axioms quotient_signs_card
#print axioms quotient_signs_trivial

end Certificates.Level66AokiBridge
