/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Cyclic
public import TauCeti.GroupTheory.TriangleGroup.Dihedral
public import TauCeti.GroupTheory.TriangleGroup.Hyperbolic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Triangle group signatures: the spherical and Euclidean parameter triples

The *signature* of a permutation triple is the ordered triple `(a, b, c)` of the orders of its three
monodromies, and `TauCeti.TriangleGroup a b c` is the presented group whose generators are
constrained by those orders. Signatures are written sorted, `1 ≤ a ≤ b ≤ c`, the usual convention
for the triangle-group presentation, which is symmetric in the three parameters. The orbifold
Euler characteristic of a signature is

`χᵒʳᵇ(a, b, c) = 1/a + 1/b + 1/c - 1 ∈ ℚ`,

and its sign is the trichotomy of the triangle groups: a positive signature is spherical, one whose
reciprocal sum is exactly one is Euclidean, and one with a smaller sum is hyperbolic. The last two
are infinite, by `TauCeti.TriangleGroup.infinite_of_inv_add_inv_add_inv_le_one`.

This file classifies the two finite lists, the classical spherical and Euclidean signatures of
the triangle-group classification, by an elementary case analysis on the reciprocal sum. The
spherical signatures are those with a first parameter
`1`, those with a repeated `2`, and the three polyhedral triples `(2, 3, 3)`, `(2, 3, 4)` and
`(2, 3, 5)`; the Euclidean ones are `(3, 3, 3)`, `(2, 4, 4)` and `(2, 3, 6)`. The classification
is what the trichotomy amounts to for finiteness: a signature outside the spherical list gives an
infinite group, while the cyclic and dihedral rows of that list give finite groups, of order
`Nat.gcd b c` and `2m` by `natCard_one` and `natCard_two_two`, so in particular the repeated
signatures `(1, m, m)` and `(2, 2, m)` have orders `m` and `2m`. The three polyhedral rows are the
remaining finite cases; the orders the spherical table records for them as `2 / χᵒʳᵇ` are not
established here.

## Main definitions

* `TauCeti.orbifoldEulerChar`: the orbifold Euler characteristic `1/a + 1/b + 1/c - 1` of a
  signature.
* `TauCeti.IsSphericalSignature`, `TauCeti.IsEuclideanSignature`: the two classified lists of
  sorted positive signatures.

## Main results

* `TauCeti.orbifoldEulerChar_pos_iff`, `TauCeti.orbifoldEulerChar_eq_zero_iff`,
  `TauCeti.orbifoldEulerChar_neg_iff`: the sign of the orbifold Euler characteristic.
* `TauCeti.isSphericalSignature_iff`, `TauCeti.isEuclideanSignature_iff`: the classification of
  the two finite lists, under `1 ≤ a ≤ b ≤ c`.
* `TauCeti.signature_trichotomy`, `TauCeti.not_isSphericalSignature_of_isEuclideanSignature`:
  every sorted positive signature is spherical, Euclidean or hyperbolic, and the two classified
  lists are disjoint.
* `TauCeti.TriangleGroup.infinite_of_not_isSphericalSignature`: a non-spherical signature gives an
  infinite triangle group.
* `TauCeti.TriangleGroup.finite_one`, `TauCeti.TriangleGroup.finite_two_two`: the cyclic and
  dihedral spherical signatures give finite triangle groups.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, §2.4, for the signature `abc` of a dessin
  and the reciprocal sum of its orders as the datum that decides the geometry of the cover.
-/

public section

namespace TauCeti

/-- The orbifold Euler characteristic `χᵒʳᵇ(a, b, c) = 1/a + 1/b + 1/c - 1` of the signature
`(a, b, c)`, as an element of `ℚ`. -/
def orbifoldEulerChar (a b c : ℕ) : ℚ :=
  (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1

/-- A signature has positive orbifold Euler characteristic exactly when its reciprocal sum is
greater than one. -/
@[simp]
theorem orbifoldEulerChar_pos_iff (a b c : ℕ) :
    0 < orbifoldEulerChar a b c ↔ 1 < (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ := by
  simp only [orbifoldEulerChar]
  constructor <;> intro h <;> linarith

/-- A signature has zero orbifold Euler characteristic exactly when its reciprocal sum is one. -/
@[simp]
theorem orbifoldEulerChar_eq_zero_iff (a b c : ℕ) :
    orbifoldEulerChar a b c = 0 ↔ (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1 := by
  simp only [orbifoldEulerChar]
  constructor <;> intro h <;> linarith

/-- A signature has negative orbifold Euler characteristic exactly when its reciprocal sum is less
than one. -/
@[simp]
theorem orbifoldEulerChar_neg_iff (a b c : ℕ) :
    orbifoldEulerChar a b c < 0 ↔ (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ < 1 := by
  simp only [orbifoldEulerChar]
  constructor <;> intro h <;> linarith

/-- A sorted positive signature is spherical when its first parameter is `1`, or its first two
parameters are `2`, or it is one of the three polyhedral triples `(2, 3, 3)`, `(2, 3, 4)` and
`(2, 3, 5)`. These are exactly the signatures of positive orbifold Euler characteristic.

The body is exposed so that the `Decidable` instance below, and `decide` on a concrete signature,
can reduce it. -/
@[expose]
def IsSphericalSignature (a b c : ℕ) : Prop :=
  a = 1 ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨ (a, b, c) = (2, 3, 5)

instance (a b c : ℕ) : Decidable (IsSphericalSignature a b c) := by
  simp only [IsSphericalSignature]
  infer_instance

/-- A sorted positive signature is Euclidean when it is one of the three triples whose reciprocal
sum is one: `(3, 3, 3)`, `(2, 4, 4)` and `(2, 3, 6)`. The body is exposed so that the
`Decidable` instance below, and `decide` on a concrete signature, can reduce it. -/
@[expose]
def IsEuclideanSignature (a b c : ℕ) : Prop :=
  (a, b, c) = (3, 3, 3) ∨ (a, b, c) = (2, 4, 4) ∨ (a, b, c) = (2, 3, 6)

instance (a b c : ℕ) : Decidable (IsEuclideanSignature a b c) := by
  simp only [IsEuclideanSignature]
  infer_instance

/-- **The spherical classification.** For a sorted positive signature the orbifold Euler
characteristic is positive exactly when the signature has a first parameter `1`, or its first two
parameters are `2`, or it is one of the three polyhedral triples `(2, 3, 3)`, `(2, 3, 4)` and
`(2, 3, 5)`. -/
theorem isSphericalSignature_iff {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    IsSphericalSignature a b c ↔ 0 < orbifoldEulerChar a b c := by
  constructor
  · rintro (h | h | h | h | h)
    · -- the cyclic row: `χᵒʳᵇ(1, b, c) = 1/b + 1/c > 0`
      subst h
      have hb : (0 : ℚ) < b := by exact_mod_cast (by omega)
      have hc : (0 : ℚ) < c := by exact_mod_cast (by omega)
      simp only [orbifoldEulerChar]
      linarith [inv_pos.mpr hb, inv_pos.mpr hc]
    · -- the dihedral row: `χᵒʳᵇ(2, 2, c) = 1/c > 0`
      obtain ⟨rfl, rfl⟩ := h
      have hc : (0 : ℚ) < c := by exact_mod_cast (by omega)
      simp only [orbifoldEulerChar]
      linarith [inv_pos.mpr hc]
    · obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num [orbifoldEulerChar]
    · obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num [orbifoldEulerChar]
    · obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num [orbifoldEulerChar]
  · intro h
    have hsum : 1 < 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) := by
      simpa only [orbifoldEulerChar, div_eq_mul_inv, one_mul] using
        (orbifoldEulerChar_pos_iff a b c).1 h
    have ha : (0 : ℚ) < a := by exact_mod_cast (by omega)
    have hb : (0 : ℚ) < b := by exact_mod_cast (by omega)
    have hc : (0 : ℚ) < c := by exact_mod_cast (by omega)
    have h₂' : (a : ℚ) ≤ b := by exact_mod_cast h₂
    have h₃' : (b : ℚ) ≤ c := by exact_mod_cast h₃
    -- the reciprocal sum is at most `3 / a`, so the first parameter is one of `1`, `2`, `3`
    have ha3 : a ≤ 3 := by
      have hba : 1 / (b : ℚ) ≤ 1 / a := one_div_le_one_div_of_le ha h₂'
      have hca : 1 / (c : ℚ) ≤ 1 / a := one_div_le_one_div_of_le ha (h₂'.trans h₃')
      have hle : 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) ≤ 3 * (1 / (a : ℚ)) := by
        linarith
      have h3 : (1 : ℚ) ≤ 3 * (1 / (a : ℚ)) := le_of_lt (lt_of_lt_of_le hsum hle)
      have h3' : (1 : ℚ) ≤ 3 / (a : ℚ) := by simpa only [div_eq_mul_inv, one_mul] using h3
      have hlt : (a : ℚ) ≤ 3 := by linarith [(le_div_iff₀ ha).mp h3']
      exact_mod_cast hlt
    interval_cases a
    · exact Or.inl rfl
    · have hbc : 1 / 2 + 1 / (b : ℚ) + 1 / (c : ℚ) > 1 := by simpa using hsum
      -- `1/b + 1/c > 1/2` and `1/c ≤ 1/b` force `b < 4`
      have hb4 : b < 4 := by
        have hcb : 1 / (c : ℚ) ≤ 1 / (b : ℚ) := one_div_le_one_div_of_le hb h₃'
        have h2 : (1 : ℚ) / 2 < 2 * (1 / (b : ℚ)) := by linarith
        have h2' : (1 : ℚ) / 2 < 2 / (b : ℚ) := by
          simpa only [div_eq_mul_inv, one_mul] using h2
        have hlt : (b : ℚ) < 4 := by
          linarith [(lt_div_iff₀ hb).mp h2']
        exact_mod_cast hlt
      interval_cases b
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · -- `1/c > 1/6` forces `c ≤ 5`
        have hc6 : c < 6 := by
          have h6 : (1 : ℚ) / 6 < 1 / (c : ℚ) := by linarith
          have hlt : (c : ℚ) < 6 := (one_div_lt_one_div (by norm_num : (0 : ℚ) < 6) hc).mp h6
          exact_mod_cast hlt
        obtain rfl | rfl | rfl := (by omega : c = 3 ∨ c = 4 ∨ c = 5)
        · decide
        · decide
        · decide
    · -- three parameters at least `3` have reciprocal sum at most one
      have hbc : 1 / 3 + 1 / (b : ℚ) + 1 / (c : ℚ) > 1 := by simpa using hsum
      have hba : 1 / (b : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) h₂'
      have hca : 1 / (c : ℚ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) (h₂'.trans h₃')
      linarith

/-- **The Euclidean classification.** For a sorted positive signature the orbifold Euler
characteristic vanishes exactly when the signature is `(3, 3, 3)`, `(2, 4, 4)` or `(2, 3, 6)`. -/
theorem isEuclideanSignature_iff {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    IsEuclideanSignature a b c ↔ orbifoldEulerChar a b c = 0 := by
  constructor
  · rintro (h | h | h)
    · obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num [orbifoldEulerChar]
    · obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num [orbifoldEulerChar]
    · obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num [orbifoldEulerChar]
  · intro h
    have hsum : 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) = 1 := by
      simpa only [orbifoldEulerChar, div_eq_mul_inv, one_mul] using
        (orbifoldEulerChar_eq_zero_iff a b c).1 h
    have ha : (0 : ℚ) < a := by exact_mod_cast (by omega)
    have hb : (0 : ℚ) < b := by exact_mod_cast (by omega)
    have hc : (0 : ℚ) < c := by exact_mod_cast (by omega)
    have h₂' : (a : ℚ) ≤ b := by exact_mod_cast h₂
    have h₃' : (b : ℚ) ≤ c := by exact_mod_cast h₃
    -- the reciprocal sum is at most `3 / a`, so the first parameter is one of `1`, `2`, `3`
    have ha3 : a ≤ 3 := by
      have hba : 1 / (b : ℚ) ≤ 1 / a := one_div_le_one_div_of_le ha h₂'
      have hca : 1 / (c : ℚ) ≤ 1 / a := one_div_le_one_div_of_le ha (h₂'.trans h₃')
      have hle : (1 : ℚ) ≤ 3 * (1 / (a : ℚ)) := by linarith
      have hle' : (1 : ℚ) ≤ 3 / (a : ℚ) := by simpa only [div_eq_mul_inv, one_mul] using hle
      have hlt : (a : ℚ) ≤ 3 := by linarith [(le_div_iff₀ ha).mp hle']
      exact_mod_cast hlt
    interval_cases a
    · -- a first parameter of `1` already exceeds the sum
      norm_num at hsum
      linarith [inv_pos.mpr hb, inv_pos.mpr hc]
    · have hbc : 1 / (b : ℚ) + 1 / (c : ℚ) = 1 / 2 := by linarith
      -- `1/b + 1/c = 1/2` and `1/c ≤ 1/b` force `b ≤ 4`
      have hb5 : b ≤ 4 := by
        have hcb : 1 / (c : ℚ) ≤ 1 / (b : ℚ) := one_div_le_one_div_of_le hb h₃'
        have h2 : (1 : ℚ) / 2 ≤ 2 * (1 / (b : ℚ)) := by linarith
        have h2' : (1 : ℚ) / 2 ≤ 2 / (b : ℚ) := by
          simpa only [div_eq_mul_inv, one_mul] using h2
        have hlt : (b : ℚ) ≤ 4 := by
          linarith [(le_div_iff₀ hb).mp h2']
        exact_mod_cast hlt
      interval_cases b
      · have hzero : 1 / (c : ℚ) = 0 := by linarith
        linarith [one_div_pos.mpr hc, hzero]
      · have hc6 : c = 6 := by
          exact_mod_cast eq_of_one_div_eq_one_div (show (1 : ℚ) / c = 1 / 6 by linarith)
        subst hc6
        decide
      · have hc4 : c = 4 := by
          exact_mod_cast eq_of_one_div_eq_one_div (show (1 : ℚ) / c = 1 / 4 by linarith)
        subst hc4
        decide
    · have hbc : 1 / (b : ℚ) + 1 / (c : ℚ) = 2 / 3 := by linarith
      -- `1/b + 1/c = 2/3` and `1/c ≤ 1/b` force `b ≤ 3`
      have hb4 : b ≤ 3 := by
        have hcb : 1 / (c : ℚ) ≤ 1 / (b : ℚ) := one_div_le_one_div_of_le hb h₃'
        have h2 : (2 : ℚ) / 3 ≤ 2 * (1 / (b : ℚ)) := by linarith
        have h2' : (2 : ℚ) / 3 ≤ 2 / (b : ℚ) := by
          simpa only [div_eq_mul_inv, one_mul] using h2
        have hlt : (b : ℚ) ≤ 3 := by
          linarith [(le_div_iff₀ hb).mp h2']
        exact_mod_cast hlt
      have hb3 : b = 3 := by omega
      subst hb3
      have hc3 : c = 3 := by
        exact_mod_cast eq_of_one_div_eq_one_div (show (1 : ℚ) / c = 1 / 3 by linarith)
      subst hc3
      decide

/-- Every sorted positive signature is spherical, Euclidean or hyperbolic. -/
theorem signature_trichotomy {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    IsSphericalSignature a b c ∨ IsEuclideanSignature a b c ∨ orbifoldEulerChar a b c < 0 := by
  rcases lt_trichotomy 0 (orbifoldEulerChar a b c) with h | h | h
  · exact Or.inl ((isSphericalSignature_iff h₁ h₂ h₃).2 h)
  · exact Or.inr (Or.inl ((isEuclideanSignature_iff h₁ h₂ h₃).2 h.symm))
  · exact Or.inr (Or.inr h)

/-- A spherical signature is not Euclidean. -/
theorem not_isEuclideanSignature_of_isSphericalSignature {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b)
    (h₃ : b ≤ c) (hs : IsSphericalSignature a b c) : ¬ IsEuclideanSignature a b c := by
  intro he
  have hpos : 0 < orbifoldEulerChar a b c := (isSphericalSignature_iff h₁ h₂ h₃).1 hs
  have hzero : orbifoldEulerChar a b c = 0 := (isEuclideanSignature_iff h₁ h₂ h₃).1 he
  linarith

/-- A Euclidean signature is not spherical. -/
theorem not_isSphericalSignature_of_isEuclideanSignature {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b)
    (h₃ : b ≤ c) (he : IsEuclideanSignature a b c) : ¬ IsSphericalSignature a b c := by
  intro hs
  have hpos : 0 < orbifoldEulerChar a b c := (isSphericalSignature_iff h₁ h₂ h₃).1 hs
  have hzero : orbifoldEulerChar a b c = 0 := (isEuclideanSignature_iff h₁ h₂ h₃).1 he
  linarith

-- The five spherical rows and the three Euclidean rows, as the classification records them.
section Examples

theorem isSphericalSignature_one_two_three : IsSphericalSignature 1 2 3 := by decide

theorem isSphericalSignature_two_two_six : IsSphericalSignature 2 2 6 := by decide

theorem isSphericalSignature_two_three_three : IsSphericalSignature 2 3 3 := by decide

theorem isSphericalSignature_two_three_four : IsSphericalSignature 2 3 4 := by decide

theorem isSphericalSignature_two_three_five : IsSphericalSignature 2 3 5 := by decide

theorem isEuclideanSignature_three_three_three : IsEuclideanSignature 3 3 3 := by decide

theorem isEuclideanSignature_two_four_four : IsEuclideanSignature 2 4 4 := by decide

theorem isEuclideanSignature_two_three_six : IsEuclideanSignature 2 3 6 := by decide

/-- The classification is sharp at the polyhedral triple `(2, 3, 5)`: the next triple of that
family, `(2, 3, 6)`, is Euclidean rather than spherical. -/
theorem not_isSphericalSignature_two_three_six : ¬ IsSphericalSignature 2 3 6 := by decide

/-- The classification is sharp at a first parameter of `3`: the smallest triple with all three
parameters at least `3` is Euclidean rather than spherical. -/
theorem not_isSphericalSignature_three_three_three : ¬ IsSphericalSignature 3 3 3 := by decide

end Examples

namespace TriangleGroup

/-- **The trichotomy in the large.** A sorted positive signature outside the spherical rows gives an
infinite triangle group. -/
theorem infinite_of_not_isSphericalSignature {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c)
    (h : ¬ IsSphericalSignature a b c) : Infinite (TriangleGroup a b c) := by
  refine infinite_of_inv_add_inv_add_inv_le_one (by omega) (by omega) (by omega) ?_
  have hle : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ ≤ 1 := by
    by_contra hcon
    exact h ((isSphericalSignature_iff h₁ h₂ h₃).2 (sub_pos.mpr (not_le.1 hcon)))
  exact hle

/-- The cyclic spherical row: a signature `(1, m, n)` with `1 ≤ m` gives a finite triangle group,
the cyclic group of order `Nat.gcd m n`. -/
theorem finite_one {m n : ℕ} (hm : 1 ≤ m) : Finite (TriangleGroup 1 m n) := by
  have hcard : 0 < Nat.card (TriangleGroup 1 m n) := by
    rw [natCard_one]
    exact Nat.gcd_pos_of_pos_left n (by omega)
  exact Nat.card_pos_iff.mp hcard |>.2

/-- The dihedral spherical row: a signature `(2, 2, m)` with `2 ≤ m` gives a finite triangle group,
the dihedral group of order `2m`. -/
theorem finite_two_two {m : ℕ} (hm : 2 ≤ m) : Finite (TriangleGroup 2 2 m) := by
  have hcard : 0 < Nat.card (TriangleGroup 2 2 m) := by
    rw [natCard_two_two m hm]
    omega
  exact Nat.card_pos_iff.mp hcard |>.2

end TriangleGroup

end TauCeti
