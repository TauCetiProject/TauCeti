/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Orders
public import TauCeti.GroupTheory.TriangleGroup.Cyclic
public import TauCeti.GroupTheory.TriangleGroup.Dihedral
public import TauCeti.GroupTheory.TriangleGroup.Hyperbolic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Triangle group signatures: the spherical and Euclidean parameter triples

A *signature* here is a sorted parameter triple `1 ≤ a ≤ b ≤ c` of the presentation
`TauCeti.TriangleGroup a b c`, whose generators are constrained by the relations `x ^ a`, `y ^ b`
and `z ^ c`; the presentation is symmetric in the three parameters, which is why a signature is
written sorted. The **exact** signature of a permutation triple is a further datum, its order
triple `t.orderTriple = (a, b, c)`, the `abc` invariant of a three-point cover
(`TauCeti.PermutationTriple.HasExactOrders`), and the two are not to be conflated. A first
parameter `1` shows the difference most sharply: no condition on a presentation forbids the
parameter triple `(1, b, c)`, whose group is the cyclic group of order `Nat.gcd b c`, whereas an
exact signature with first order `1` is the reduced form `(1, m, m)`, because a monodromy of order
one is the identity and the product relation `σinf * σ1 * σ0 = 1` then makes the other two inverse.
The spherical list is therefore stated in the two readings: `TauCeti.IsSphericalSignature` is the
list of exact signatures, whose five rows are `(1, m, m)`, `(2, 2, m)`, `(2, 3, 3)`, `(2, 3, 4)`
and `(2, 3, 5)`, while `TauCeti.IsSphericalParameterSignature` is the list of presentation
parameters, in which the first row is every sorted triple with first parameter `1`. The geometry
type of a triple with exact orders `(a, b, c)` is the sign of the orbifold characteristic.

The orbifold Euler characteristic of a signature is

`χᵒʳᵇ(a, b, c) = 1/a + 1/b + 1/c - 1 ∈ ℚ`,

and its sign is the trichotomy of the triangle groups: a positive signature is spherical, one whose
reciprocal sum is exactly one is Euclidean, and one with a smaller sum is hyperbolic. The last two
are infinite, by `TauCeti.TriangleGroup.infinite_of_inv_add_inv_add_inv_le_one`.

This file classifies the finite lists of the triangle-group classification by an elementary case
analysis on the reciprocal sum. The spherical parameters are those with a first parameter `1`,
those with a repeated `2`, and the three polyhedral triples `(2, 3, 3)`, `(2, 3, 4)` and
`(2, 3, 5)`; among exact signatures the first row is the reduced form `(1, m, m)`, so the exact
spherical list is the five rows `(1, m, m)`, `(2, 2, m)`, `(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`.
The Euclidean signatures are `(3, 3, 3)`, `(2, 4, 4)` and `(2, 3, 6)`, all three of which are
exact already. The classification is what the trichotomy amounts to for finiteness: a signature
outside the spherical parameters gives an infinite group, while the cyclic and dihedral rows give
finite groups, of order `Nat.gcd b c` and `2m` by `natCard_one` and `natCard_two_two`, so in
particular the signatures `(1, m, m)` and `(2, 2, m)` have orders `m` and `2m`. The three
polyhedral rows are the remaining finite cases; the orders the spherical table records for them as
`2 / χᵒʳᵇ` are not established here. That formula is a statement about the exact rows, where
`2 / χᵒʳᵇ(1, m, m) = m` and `2 / χᵒʳᵇ(2, 2, m) = 2m` are the orders just proved, while an
unreduced parameter triple `(1, b, c)` has order `Nat.gcd b c`, which is `2 / χᵒʳᵇ(1, b, c)` only
when `b = c`.

## Main definitions

* `TauCeti.orbifoldEulerChar`: the orbifold Euler characteristic `1/a + 1/b + 1/c - 1` of a
  signature.
* `TauCeti.IsSphericalSignature`: the five rows of the spherical table, read on exact signatures.
* `TauCeti.IsSphericalParameterSignature`, `TauCeti.IsEuclideanSignature`: the classified lists read
  on presentation parameters, where the cyclic row is every sorted triple with first parameter `1`,
  and the Euclidean rows, which are the same in both readings.

## Main results

* `TauCeti.orbifoldEulerChar_def`: the defining formula for the orbifold Euler characteristic.
* `TauCeti.orbifoldEulerChar_pos_iff`, `TauCeti.orbifoldEulerChar_eq_zero_iff`,
  `TauCeti.orbifoldEulerChar_neg_iff`: the sign of the orbifold Euler characteristic.
* `TauCeti.isSphericalParameterSignature_iff`, `TauCeti.isEuclideanSignature_iff`: the
  classification of the two finite lists of presentation parameters, under `1 ≤ a ≤ b ≤ c`.
* `TauCeti.signature_trichotomy`, `TauCeti.not_isSphericalSignature_of_isEuclideanSignature`:
  every sorted positive signature is spherical, Euclidean or hyperbolic, and the two classified
  lists are disjoint.
* `TauCeti.TriangleGroup.infinite_of_not_isSphericalParameterSignature`: a signature whose
  parameters are not a row of the spherical table gives an infinite triangle group; the cyclic and
  dihedral rows are finite, by `TauCeti.TriangleGroup.finite_one` in
  `TauCeti.GroupTheory.TriangleGroup.Cyclic` and `TauCeti.TriangleGroup.finite_two_two` in
  `TauCeti.GroupTheory.TriangleGroup.Dihedral`.
* `TauCeti.PermutationTriple.geometryType_eq_spherical_iff_orbifoldEulerChar_pos` and its
  Euclidean and hyperbolic counterparts: the sign of the orbifold characteristic is the geometry
  type of a triple with exact orders `(a, b, c)`.
* `TauCeti.PermutationTriple.geometryType_eq_spherical_iff_isSphericalSignature`: the spherical
  classification read on exact signatures, where the cyclic row is the reduced form `(1, m, m)`.

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

/-- The defining formula for the orbifold Euler characteristic, `1/a + 1/b + 1/c - 1`. The orders
the spherical table records as `2 / χᵒʳᵇ` are read off this equation. -/
theorem orbifoldEulerChar_def (a b c : ℕ) :
    orbifoldEulerChar a b c = (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1 := by
  simp only [orbifoldEulerChar]

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

/-- A sorted positive triple is a **spherical signature** when it is one of the five rows of the
spherical table `(1, m, m)`, `(2, 2, m)`, `(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`, the exact
signatures of positive orbifold Euler characteristic. The cyclic row is the reduced form
`(1, m, m)`: the group `TriangleGroup 1 b c` is cyclic of order `Nat.gcd b c`, and it is exactness,
not the presentation, that forces `b = c`, by
`TauCeti.PermutationTriple.b_eq_c_of_hasExactOrders_one`. A triple of exact orders `(a, b, c)`,
sorted, is spherical exactly when it is a row, by
`TauCeti.PermutationTriple.geometryType_eq_spherical_iff_isSphericalSignature`.

Two of the five rows have a free entry, so the ordering conjuncts are stated here rather than left
implicit: without them the degenerate triples `(1, 0, 0)` and `(2, 2, 0)` would pass as signatures,
although neither is a signature and their orbifold Euler characteristics are `0`, not positive.
`TauCeti.IsEuclideanSignature` needs no conjuncts of its own, all three of its rows being concrete.

The body is exposed so that the `Decidable` instance below, and `decide` on a concrete signature,
can reduce it. -/
@[expose]
def IsSphericalSignature (a b c : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧
    ((a = 1 ∧ b = c) ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
      (a, b, c) = (2, 3, 5))

instance (a b c : ℕ) : Decidable (IsSphericalSignature a b c) := by
  simp only [IsSphericalSignature]
  infer_instance

/-- A **spherical parameter signature** is a sorted positive parameter triple whose first parameter
is `1`, or whose first two parameters are `2`, or which is one of the three polyhedral triples
`(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`. These are exactly the presentation parameters of
positive orbifold Euler characteristic, by `TauCeti.isSphericalParameterSignature_iff`.

The first branch is a statement about presentation parameters, and the monodromy orders are only
required to divide the presentation parameters: among exact signatures it is therefore the
reduced form `(1, m, m)`, by
`TauCeti.PermutationTriple.geometryType_eq_spherical_iff_isSphericalSignature`.

The body is exposed so that the `Decidable` instance below, and `decide` on a concrete signature,
can reduce it. -/
@[expose]
def IsSphericalParameterSignature (a b c : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧
    (a = 1 ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
      (a, b, c) = (2, 3, 5))

instance (a b c : ℕ) : Decidable (IsSphericalParameterSignature a b c) := by
  simp only [IsSphericalParameterSignature]
  infer_instance

/-- A triple is a **Euclidean signature** when it is one of the three triples whose reciprocal
sum is one: `(3, 3, 3)`, `(2, 4, 4)` and `(2, 3, 6)`. All three are sorted, positive and exact, so
this predicate needs no ordering conjunct of its own, unlike `TauCeti.IsSphericalSignature`, whose
first two rows have a free entry. The body is exposed so that the `Decidable` instance below, and
`decide` on a concrete signature, can reduce it. -/
@[expose]
def IsEuclideanSignature (a b c : ℕ) : Prop :=
  (a, b, c) = (3, 3, 3) ∨ (a, b, c) = (2, 4, 4) ∨ (a, b, c) = (2, 3, 6)

instance (a b c : ℕ) : Decidable (IsEuclideanSignature a b c) := by
  simp only [IsEuclideanSignature]
  infer_instance

/-- The reciprocal sum of a sorted positive parameter triple is at most `3 / a`, so a reciprocal
sum of at least one forces the first parameter to be at most `3`. Both classifications below are
case analyses after this bound. -/
private theorem first_le_three_of_one_le_reciprocal_sum {a b c : ℕ} (ha : (0 : ℚ) < a)
    (h₂ : (a : ℚ) ≤ b) (h₃ : (b : ℚ) ≤ c)
    (habc : 1 ≤ 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ)) : a ≤ 3 := by
  have hba : 1 / (b : ℚ) ≤ 1 / (a : ℚ) := one_div_le_one_div_of_le ha h₂
  have hca : 1 / (c : ℚ) ≤ 1 / (a : ℚ) := one_div_le_one_div_of_le ha (h₂.trans h₃)
  have hle : 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) ≤ 3 * (1 / (a : ℚ)) := by
    linarith
  have h3 : (1 : ℚ) ≤ 3 * (1 / (a : ℚ)) := habc.trans hle
  have h3' : (1 : ℚ) ≤ 3 / (a : ℚ) := by simpa only [div_eq_mul_inv, one_mul] using h3
  have hlt : (a : ℚ) ≤ 3 := by linarith [(le_div_iff₀ ha).mp h3']
  exact_mod_cast hlt

/-- **The spherical classification, on presentation parameters.** For a sorted positive
signature the orbifold Euler characteristic is positive exactly when the parameters are a row of
the spherical table: a first parameter `1`, a repeated `2`, or one of the three polyhedral triples
`(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`. The order `2 / χᵒʳᵇ` of the spherical table is read on
the exact signatures of `TauCeti.IsSphericalSignature`, in which the cyclic row is the reduced form
`(1, m, m)`. -/
theorem isSphericalParameterSignature_iff {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    IsSphericalParameterSignature a b c ↔ 0 < orbifoldEulerChar a b c := by
  constructor
  · rintro ⟨-, -, -, h | h | h | h | h⟩
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
    have ha3 : a ≤ 3 := first_le_three_of_one_le_reciprocal_sum ha h₂' h₃' hsum.le
    interval_cases a
    · exact ⟨h₁, h₂, h₃, Or.inl rfl⟩
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
      · exact ⟨h₁, h₂, h₃, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · -- `1/c > 1/6` forces `c ≤ 5`
        have hc6 : c < 6 := by
          have h6 : (1 : ℚ) / 6 < 1 / (c : ℚ) := by linarith
          have hlt : (c : ℚ) < 6 := (one_div_lt_one_div (by norm_num : (0 : ℚ) < 6) hc).mp h6
          exact_mod_cast hlt
        obtain rfl | rfl | rfl := (by omega : c = 3 ∨ c = 4 ∨ c = 5)
        · exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
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
    have ha3 : a ≤ 3 := first_le_three_of_one_le_reciprocal_sum ha h₂' h₃' hsum.symm.le
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
      · have hinv : (1 : ℚ) / c = 1 / 6 := by linarith
        have hc6 : c = 6 := by exact_mod_cast eq_of_one_div_eq_one_div hinv
        subst hc6
        decide
      · have hinv : (1 : ℚ) / c = 1 / 4 := by linarith
        have hc4 : c = 4 := by exact_mod_cast eq_of_one_div_eq_one_div hinv
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
      have hinv : (1 : ℚ) / c = 1 / 3 := by linarith
      have hc3 : c = 3 := by exact_mod_cast eq_of_one_div_eq_one_div hinv
      subst hc3
      decide

/-- A row of the spherical table is a row of the parameter list: the reduced cyclic row `(1, m, m)`
is one of the triples whose first parameter is `1`, the other four rows are rows of both. -/
private theorem row_isParameterRow {a b c : ℕ}
    (h : (a = 1 ∧ b = c) ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
      (a, b, c) = (2, 3, 5)) :
    a = 1 ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
      (a, b, c) = (2, 3, 5) := by
  rcases h with ⟨ha, -⟩ | h' | h' | h' | h'
  · exact Or.inl ha
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

/-- Every sorted positive signature is spherical, Euclidean or hyperbolic. -/
theorem signature_trichotomy {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    IsSphericalParameterSignature a b c ∨ IsEuclideanSignature a b c ∨
      orbifoldEulerChar a b c < 0 := by
  rcases lt_trichotomy 0 (orbifoldEulerChar a b c) with h | h | h
  · exact Or.inl ((isSphericalParameterSignature_iff h₁ h₂ h₃).2 h)
  · exact Or.inr (Or.inl ((isEuclideanSignature_iff h₁ h₂ h₃).2 h.symm))
  · exact Or.inr (Or.inr h)

/-- A spherical signature is not Euclidean. The two classified lists are disjoint, for all
parameters. -/
theorem not_isEuclideanSignature_of_isSphericalSignature {a b c : ℕ}
    (hs : IsSphericalSignature a b c) : ¬ IsEuclideanSignature a b c := by
  intro he
  rcases he with h | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [IsSphericalSignature] at hs

/-- A Euclidean signature is not spherical. -/
theorem not_isSphericalSignature_of_isEuclideanSignature {a b c : ℕ}
    (he : IsEuclideanSignature a b c) : ¬ IsSphericalSignature a b c := by
  intro hs
  exact not_isEuclideanSignature_of_isSphericalSignature hs he

/-! ### Exact signatures -/

namespace PermutationTriple

variable {n a b c : ℕ}

/-- **The orbifold sign is the geometry type.** A triple with exact orders `(a, b, c)` is
spherical exactly when the orbifold Euler characteristic of its signature is positive. -/
theorem geometryType_eq_spherical_iff_orbifoldEulerChar_pos {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) :
    t.geometryType = .spherical ↔ 0 < orbifoldEulerChar a b c := by
  obtain ⟨h0, h1, h2⟩ := orderOf_eq_of_hasExactOrders t h
  rw [geometryType_eq_spherical_iff, orbifoldEulerChar_pos_iff, h0, h1, h2]

/-- A triple with exact orders `(a, b, c)` is Euclidean exactly when the orbifold Euler
characteristic of its signature vanishes. -/
theorem geometryType_eq_euclidean_iff_orbifoldEulerChar_eq_zero {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) :
    t.geometryType = .euclidean ↔ orbifoldEulerChar a b c = 0 := by
  obtain ⟨h0, h1, h2⟩ := orderOf_eq_of_hasExactOrders t h
  rw [geometryType_eq_euclidean_iff, orbifoldEulerChar_eq_zero_iff, h0, h1, h2]

/-- A triple with exact orders `(a, b, c)` is hyperbolic exactly when the orbifold Euler
characteristic of its signature is negative. -/
theorem geometryType_eq_hyperbolic_iff_orbifoldEulerChar_neg {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) :
    t.geometryType = .hyperbolic ↔ orbifoldEulerChar a b c < 0 := by
  obtain ⟨h0, h1, h2⟩ := orderOf_eq_of_hasExactOrders t h
  rw [geometryType_eq_hyperbolic_iff, orbifoldEulerChar_neg_iff, h0, h1, h2]

/-- **The spherical classification, on exact signatures.** A triple with exact orders
`(a, b, c)`, sorted, is spherical exactly when its order triple is one of the five rows of
`TauCeti.IsSphericalSignature`, the cyclic row being the reduced form `(1, m, m)` rather than the
whole first branch of `TauCeti.IsSphericalParameterSignature`. Exactness makes the first order
positive, so it is not a hypothesis. -/
theorem geometryType_eq_spherical_iff_isSphericalSignature {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    t.geometryType = .spherical ↔ IsSphericalSignature a b c := by
  obtain ⟨h0, _, _⟩ := orderOf_eq_of_hasExactOrders t h
  have hpos : 1 ≤ orderOf t.σ0 := orderOf_pos _
  have h₁ : 1 ≤ a := by omega
  have hsign : t.geometryType = .spherical ↔ IsSphericalParameterSignature a b c :=
    (t.geometryType_eq_spherical_iff_orbifoldEulerChar_pos h).trans
      (isSphericalParameterSignature_iff h₁ h₂ h₃).symm
  constructor
  · intro hs
    rcases hsign.mp hs with ⟨-, -, -, ha | h' | h' | h' | h'⟩
    · -- the cyclic branch: exactness forces the two remaining orders to agree
      rw [ha] at h
      exact ⟨h₁, h₂, h₃, Or.inl ⟨ha, b_eq_c_of_hasExactOrders_one t h⟩⟩
    · exact ⟨h₁, h₂, h₃, Or.inr (Or.inl h')⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inl rfl))⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  · rintro ⟨-, -, -, hrows⟩
    exact hsign.mpr ⟨h₁, h₂, h₃, row_isParameterRow hrows⟩

end PermutationTriple

namespace TriangleGroup

/-- **The trichotomy in the large.** A sorted positive signature whose parameters are not a row
of the spherical table gives an infinite triangle group. -/
theorem infinite_of_not_isSphericalParameterSignature {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b)
    (h₃ : b ≤ c) (h : ¬ IsSphericalParameterSignature a b c) :
    Infinite (TriangleGroup a b c) := by
  refine infinite_of_inv_add_inv_add_inv_le_one (by omega) (by omega) (by omega) ?_
  have hle : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ ≤ 1 := by
    by_contra hcon
    exact h ((isSphericalParameterSignature_iff h₁ h₂ h₃).2 (sub_pos.mpr (not_le.1 hcon)))
  exact hle

end TriangleGroup

end TauCeti
