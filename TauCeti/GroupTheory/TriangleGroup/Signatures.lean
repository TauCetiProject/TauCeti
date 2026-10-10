/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Orders
public import TauCeti.GroupTheory.TriangleGroup.Hyperbolic
import TauCeti.GroupTheory.TriangleGroup.Cyclic
import TauCeti.GroupTheory.TriangleGroup.Dihedral
import TauCeti.GroupTheory.TriangleGroup.Polyhedral
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
The Euclidean signatures are `(3, 3, 3)`, `(2, 4, 4)` and `(2, 3, 6)`, the same three triples in
both readings. The classification is what the trichotomy amounts to for finiteness: a signature
outside the spherical parameters gives an infinite group, while the cyclic and dihedral rows give
finite groups, of order `Nat.gcd b c` and `2m` by `natCard_one` and `natCard_two_two`, so in
particular the signatures `(1, m, m)` and `(2, 2, m)` have orders `m` and `2m`. The three
polyhedral rows give the finite groups `A₄`, `S₄` and `A₅`, of orders `12`, `24` and `60` by
`natCard_two_three_three`, `natCard_two_three_four` and `natCard_two_three_five`, the orders the
spherical table records as `2 / χᵒʳᵇ`. So a sorted positive signature gives a finite triangle
group exactly when it is a spherical parameter signature. The formula `2 / χᵒʳᵇ` is a statement
about the exact rows, where `2 / χᵒʳᵇ(1, m, m) = m` and `2 / χᵒʳᵇ(2, 2, m) = 2m` are the orders
just proved, while an unreduced parameter triple `(1, b, c)` has order `Nat.gcd b c`, which is
`2 / χᵒʳᵇ(1, b, c)` only when `b = c`.

## Main definitions

* `TauCeti.orbifoldEulerChar`: the orbifold Euler characteristic `1/a + 1/b + 1/c - 1` of a
  signature.
* `TauCeti.IsSphericalSignature`: the five rows of the spherical table, read on exact signatures.
* `TauCeti.IsSphericalParameterSignature`, `TauCeti.IsEuclideanSignature`: the classified lists read
  on presentation parameters, where the cyclic row is every sorted triple with first parameter `1`,
  and the Euclidean rows, which are the same in both readings.

None of the three predicates exposes its body. Each carries a `Decidable` instance, so `decide`
works on a concrete signature, and a public characteristic lemma
`TauCeti.isSphericalSignature_rows_iff`, `TauCeti.isSphericalParameterSignature_rows_iff` or
`TauCeti.isEuclideanSignature_rows_iff`, which is how a signature is read.

## Main results

* `TauCeti.orbifoldEulerChar` and `TauCeti.orbifoldEulerChar_def`: the orbifold Euler
  characteristic `1/a + 1/b + 1/c - 1`, whose unexposed definition is given its value by the `simp`
  equation `orbifoldEulerChar a b c = (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1`. That equation is the
  single simplification level of the orbifold characteristic, and the sign is read off the formula
  it exposes.
* `TauCeti.orbifoldEulerChar_pos_iff`, `TauCeti.orbifoldEulerChar_eq_zero_iff`,
  `TauCeti.orbifoldEulerChar_neg_iff`: the sign of the orbifold Euler characteristic, as
  characterisations of the reciprocal sum against `TauCeti.orbifoldEulerChar_def`.
* `TauCeti.isSphericalSignature_rows_iff`, `TauCeti.isSphericalParameterSignature_rows_iff`,
  `TauCeti.isEuclideanSignature_rows_iff`: the rows of each classified list, as simp lemmas.
* `TauCeti.isSphericalParameterSignature_iff`, `TauCeti.isEuclideanSignature_iff`: the
  classification of the two finite lists of presentation parameters, under `1 ≤ a ≤ b ≤ c`.
* `TauCeti.parameterSignature_trichotomy`: every sorted positive signature is spherical, Euclidean
  or hyperbolic, stated on presentation parameters.
* `TauCeti.not_isEuclideanSignature_of_isSphericalParameterSignature` and
  `TauCeti.not_isSphericalParameterSignature_of_isEuclideanSignature`, with
  `TauCeti.not_isEuclideanSignature_of_isSphericalSignature` and
  `TauCeti.not_isSphericalSignature_of_isEuclideanSignature` on exact signatures: the two
  classified lists are disjoint.
* `TauCeti.TriangleGroup.infinite_of_not_isSphericalParameterSignature`: a signature whose
  parameters are not a row of the spherical table gives an infinite triangle group.
* `TauCeti.TriangleGroup.finite_iff_isSphericalParameterSignature`: a sorted positive signature
  gives a finite triangle group exactly when its parameters are a row of the spherical table.
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
`(a, b, c)`, as an element of `ℚ`. The definition is kept unexposed, and its value is given by the
`@[simp]` equation `TauCeti.orbifoldEulerChar_def`; the three sign characterisations below and the
orders the spherical table records as `2 / χᵒʳᵇ` are both read off that formula. -/
def orbifoldEulerChar (a b c : ℕ) : ℚ :=
  (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1

/-- The defining formula of `TauCeti.orbifoldEulerChar`, as a `simp` lemma. It is the only
simplification rule for the orbifold Euler characteristic: simplification reduces
`orbifoldEulerChar a b c` to `1/a + 1/b + 1/c - 1`, and the sign is then read off that expression.
This is why the three sign characterisations below carry no `simp` attribute of their own: as `simp`
lemmas they would be duplicates of this equation. -/
@[simp]
theorem orbifoldEulerChar_def (a b c : ℕ) :
    orbifoldEulerChar a b c = (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1 :=
  -- The parentheses matter: a bare `rfl` in an exported theorem would demand that
  -- `orbifoldEulerChar` be `@[expose]`, which would defeat the point of this equation.
  (rfl)

/-- A signature has positive orbifold Euler characteristic exactly when its reciprocal sum is
greater than one. This is a characterisation rather than a simplification rule:
`TauCeti.orbifoldEulerChar_def` already simplifies `orbifoldEulerChar` to its reciprocal-sum
formula, and `simp` then proves this equivalence on its own. -/
theorem orbifoldEulerChar_pos_iff (a b c : ℕ) :
    0 < orbifoldEulerChar a b c ↔ 1 < (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ := by
  simp only [orbifoldEulerChar]
  constructor <;> intro h <;> linarith

/-- A signature has zero orbifold Euler characteristic exactly when its reciprocal sum is one. It
carries no `simp` attribute, as `TauCeti.orbifoldEulerChar_pos_iff` does. -/
theorem orbifoldEulerChar_eq_zero_iff (a b c : ℕ) :
    orbifoldEulerChar a b c = 0 ↔ (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1 := by
  simp only [orbifoldEulerChar]
  constructor <;> intro h <;> linarith

/-- A signature has negative orbifold Euler characteristic exactly when its reciprocal sum is less
than one. It carries no `simp` attribute, as `TauCeti.orbifoldEulerChar_pos_iff` does. -/
theorem orbifoldEulerChar_neg_iff (a b c : ℕ) :
    orbifoldEulerChar a b c < 0 ↔ (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ < 1 := by
  simp only [orbifoldEulerChar]
  constructor <;> intro h <;> linarith

/-- A sorted positive triple is a **spherical signature** when it is one of the five rows of the
spherical table `(1, m, m)`, `(2, 2, m)`, `(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`, the exact
signatures of positive orbifold Euler characteristic. The cyclic row is the reduced form
`(1, m, m)`: the group `TriangleGroup 1 b c` is cyclic of order `Nat.gcd b c`, and it is exactness,
not the presentation, that forces `b = c`, by
`TauCeti.PermutationTriple.second_eq_third_of_hasExactOrders_one`. A triple of exact orders
`(a, b, c)`, sorted, is spherical exactly when it is a row, by
`TauCeti.PermutationTriple.geometryType_eq_spherical_iff_isSphericalSignature`.

Two of the five rows have a free entry, so the ordering conjuncts are stated here rather than left
implicit: without them the degenerate triples `(1, 0, 0)` and `(2, 2, 0)` would pass as signatures,
although neither is a signature and their orbifold Euler characteristics are `0`, not positive.
`TauCeti.IsEuclideanSignature` needs no conjuncts of its own, all three of its rows being concrete.

The body is not exposed: the `Decidable` instance below is built from the characteristic formula,
and a signature is read through the same formula. -/
def IsSphericalSignature (a b c : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧
    ((a = 1 ∧ b = c) ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
      (a, b, c) = (2, 3, 5))

/-- The rows of the spherical table, as the characteristic formula of
`TauCeti.IsSphericalSignature`. -/
@[simp]
theorem isSphericalSignature_rows_iff (a b c : ℕ) :
    IsSphericalSignature a b c ↔
      1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧
        ((a = 1 ∧ b = c) ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
          (a, b, c) = (2, 3, 5)) := Iff.rfl

instance (a b c : ℕ) : Decidable (IsSphericalSignature a b c) := by
  rw [isSphericalSignature_rows_iff]
  infer_instance

/-- A **spherical parameter signature** is a sorted positive parameter triple whose first parameter
is `1`, or whose first two parameters are `2`, or which is one of the three polyhedral triples
`(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`. These are exactly the presentation parameters of
positive orbifold Euler characteristic, by `TauCeti.isSphericalParameterSignature_iff`.

The first branch is a statement about presentation parameters, and the monodromy orders are only
required to divide the presentation parameters: among exact signatures it is therefore the
reduced form `(1, m, m)`, by
`TauCeti.PermutationTriple.geometryType_eq_spherical_iff_isSphericalSignature`.

The body is not exposed: the `Decidable` instance below is built from the characteristic formula,
and a signature is read through the same formula. -/
def IsSphericalParameterSignature (a b c : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧
    (a = 1 ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
      (a, b, c) = (2, 3, 5))

/-- The rows of the spherical table, as the characteristic formula of
`TauCeti.IsSphericalParameterSignature`, whose cyclic row is every sorted triple with first
parameter `1`. -/
@[simp]
theorem isSphericalParameterSignature_rows_iff (a b c : ℕ) :
    IsSphericalParameterSignature a b c ↔
      1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧
        (a = 1 ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
          (a, b, c) = (2, 3, 5)) := Iff.rfl

instance (a b c : ℕ) : Decidable (IsSphericalParameterSignature a b c) := by
  rw [isSphericalParameterSignature_rows_iff]
  infer_instance

/-- A triple is a **Euclidean signature** when it is one of the three triples whose reciprocal
sum is one: `(3, 3, 3)`, `(2, 4, 4)` and `(2, 3, 6)`. All three are sorted and positive, so this
predicate needs no ordering conjunct of its own, unlike `TauCeti.IsSphericalSignature`, whose
first two rows have a free entry. The body is not exposed: the `Decidable` instance below is built
from the characteristic formula, and a signature is read through the same formula. -/
def IsEuclideanSignature (a b c : ℕ) : Prop :=
  (a, b, c) = (3, 3, 3) ∨ (a, b, c) = (2, 4, 4) ∨ (a, b, c) = (2, 3, 6)

/-- The three Euclidean rows, as the characteristic formula of
`TauCeti.IsEuclideanSignature`. -/
@[simp]
theorem isEuclideanSignature_rows_iff (a b c : ℕ) :
    IsEuclideanSignature a b c ↔
      (a, b, c) = (3, 3, 3) ∨ (a, b, c) = (2, 4, 4) ∨ (a, b, c) = (2, 3, 6) := Iff.rfl

instance (a b c : ℕ) : Decidable (IsEuclideanSignature a b c) := by
  rw [isEuclideanSignature_rows_iff]
  infer_instance

/-- A row of the spherical table is a row of the parameter list: the reduced cyclic row `(1, m, m)`
is one of the triples whose first parameter is `1`, and the other four rows are rows of both. -/
theorem IsSphericalSignature.isSphericalParameterSignature {a b c : ℕ}
    (h : IsSphericalSignature a b c) : IsSphericalParameterSignature a b c := by
  rw [isSphericalSignature_rows_iff] at h
  rw [isSphericalParameterSignature_rows_iff]
  obtain ⟨h₁, h₂, h₃, hrows | h' | h' | h' | h'⟩ := h
  · exact ⟨h₁, h₂, h₃, Or.inl hrows.1⟩
  · exact ⟨h₁, h₂, h₃, Or.inr (Or.inl h')⟩
  · exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inl h'))⟩
  · exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inl h')))⟩
  · exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inr h')))⟩

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
  · intro h
    have h' := isSphericalParameterSignature_rows_iff a b c |>.mp h
    rcases h' with ⟨-, -, -, h | h | h | h | h⟩
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
      have hba : 1 / (b : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) h₂'
      have hca : 1 / (c : ℚ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) (h₂'.trans h₃')
      linarith

/-- **The Euclidean classification.** For a sorted positive signature the orbifold Euler
characteristic vanishes exactly when the signature is `(3, 3, 3)`, `(2, 4, 4)` or `(2, 3, 6)`. -/
theorem isEuclideanSignature_iff {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    IsEuclideanSignature a b c ↔ orbifoldEulerChar a b c = 0 := by
  constructor
  · intro h
    have h' := isEuclideanSignature_rows_iff a b c |>.mp h
    rcases h' with (h | h | h)
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

/-- Every sorted positive signature is spherical, Euclidean or hyperbolic. The trichotomy is stated
on presentation parameters, whose spherical list `TauCeti.IsSphericalParameterSignature` is the
broader of the two readings. -/
theorem parameterSignature_trichotomy {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    IsSphericalParameterSignature a b c ∨ IsEuclideanSignature a b c ∨
      orbifoldEulerChar a b c < 0 := by
  rcases lt_trichotomy 0 (orbifoldEulerChar a b c) with h | h | h
  · exact Or.inl ((isSphericalParameterSignature_iff h₁ h₂ h₃).2 h)
  · exact Or.inr (Or.inl ((isEuclideanSignature_iff h₁ h₂ h₃).2 h.symm))
  · exact Or.inr (Or.inr h)

/-- A spherical parameter signature is not Euclidean. The two classified lists are disjoint, for
all parameters. -/
theorem not_isEuclideanSignature_of_isSphericalParameterSignature {a b c : ℕ}
    (hs : IsSphericalParameterSignature a b c) : ¬ IsEuclideanSignature a b c := by
  intro he
  rcases he with h | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
    simp [IsSphericalParameterSignature] at hs

/-- A Euclidean signature is not a spherical parameter signature. -/
theorem not_isSphericalParameterSignature_of_isEuclideanSignature {a b c : ℕ}
    (he : IsEuclideanSignature a b c) : ¬ IsSphericalParameterSignature a b c :=
  fun hsp => not_isEuclideanSignature_of_isSphericalParameterSignature hsp he

/-- A spherical signature is not Euclidean, by the disjointness of the parameter lists and the
inclusion of exact rows in parameter rows. -/
theorem not_isEuclideanSignature_of_isSphericalSignature {a b c : ℕ}
    (hs : IsSphericalSignature a b c) : ¬ IsEuclideanSignature a b c :=
  not_isEuclideanSignature_of_isSphericalParameterSignature hs.isSphericalParameterSignature

/-- A Euclidean signature is not spherical, by the disjointness of the parameter lists and the
inclusion of exact rows in parameter rows. -/
theorem not_isSphericalSignature_of_isEuclideanSignature {a b c : ℕ}
    (he : IsEuclideanSignature a b c) : ¬ IsSphericalSignature a b c :=
  fun hsp => not_isSphericalParameterSignature_of_isEuclideanSignature he
    hsp.isSphericalParameterSignature

/-! ### Exact signatures -/

namespace PermutationTriple

variable {n a b c : ℕ}

/-- **The orbifold sign is the geometry type.** A triple with exact orders `(a, b, c)` is
spherical exactly when the orbifold Euler characteristic of its signature is positive. -/
theorem geometryType_eq_spherical_iff_orbifoldEulerChar_pos {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) :
    t.geometryType = .spherical ↔ 0 < orbifoldEulerChar a b c := by
  simp only [hasExactOrders_iff, Prod.ext_iff, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf] at h
  rw [geometryType_eq_spherical_iff, orbifoldEulerChar_pos_iff, h.1, h.2.1, h.2.2]

/-- A triple with exact orders `(a, b, c)` is Euclidean exactly when the orbifold Euler
characteristic of its signature vanishes. -/
theorem geometryType_eq_euclidean_iff_orbifoldEulerChar_eq_zero {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) :
    t.geometryType = .euclidean ↔ orbifoldEulerChar a b c = 0 := by
  simp only [hasExactOrders_iff, Prod.ext_iff, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf] at h
  rw [geometryType_eq_euclidean_iff, orbifoldEulerChar_eq_zero_iff, h.1, h.2.1, h.2.2]

/-- A triple with exact orders `(a, b, c)` is hyperbolic exactly when the orbifold Euler
characteristic of its signature is negative. -/
theorem geometryType_eq_hyperbolic_iff_orbifoldEulerChar_neg {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) :
    t.geometryType = .hyperbolic ↔ orbifoldEulerChar a b c < 0 := by
  simp only [hasExactOrders_iff, Prod.ext_iff, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf] at h
  rw [geometryType_eq_hyperbolic_iff, orbifoldEulerChar_neg_iff, h.1, h.2.1, h.2.2]

/-- **The spherical classification, on exact signatures.** A triple with exact orders
`(a, b, c)`, sorted, is spherical exactly when its order triple is one of the five rows of
`TauCeti.IsSphericalSignature`, the cyclic row being the reduced form `(1, m, m)` rather than the
whole first branch of `TauCeti.IsSphericalParameterSignature`. Exactness makes the first order
positive, so it is not a hypothesis. -/
theorem geometryType_eq_spherical_iff_isSphericalSignature {t : PermutationTriple n}
    (h : t.HasExactOrders a b c) (h₂ : a ≤ b) (h₃ : b ≤ c) :
    t.geometryType = .spherical ↔ IsSphericalSignature a b c := by
  have h' := (t.hasExactOrders_iff).mp h
  simp only [Prod.ext_iff, orderTriple_σ0, orderTriple_σ1, orderTriple_σinf] at h'
  have hpos : 0 < orderOf t.σ0 := orderOf_pos _
  have h₁ : 1 ≤ a := by omega
  have hsign : t.geometryType = .spherical ↔ IsSphericalParameterSignature a b c :=
    (t.geometryType_eq_spherical_iff_orbifoldEulerChar_pos h).trans
      (isSphericalParameterSignature_iff h₁ h₂ h₃).symm
  constructor
  · intro hs
    have hrows := isSphericalParameterSignature_rows_iff a b c |>.mp (hsign.mp hs)
    rw [isSphericalSignature_rows_iff]
    rcases hrows with ⟨-, -, -, ha | h' | h' | h' | h'⟩
    · -- the cyclic branch: exactness forces the two remaining orders to agree
      rw [ha] at h
      exact ⟨h₁, h₂, h₃, Or.inl ⟨ha, second_eq_third_of_hasExactOrders_one t h⟩⟩
    · exact ⟨h₁, h₂, h₃, Or.inr (Or.inl h')⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inl rfl))⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨h₁, h₂, h₃, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  · intro hs
    exact hsign.mpr hs.isSphericalParameterSignature

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

/-- **The finite triangle groups.** A sorted positive signature gives a finite triangle group
exactly when its parameters are a row of the spherical table: the cyclic and dihedral rows and
the three polyhedral triples `(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`. -/
theorem finite_iff_isSphericalParameterSignature {a b c : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ b)
    (h₃ : b ≤ c) : Finite (TriangleGroup a b c) ↔ IsSphericalParameterSignature a b c := by
  refine ⟨fun _ ↦ by_contra fun h ↦ ?_, fun h ↦ ?_⟩
  · have := infinite_of_not_isSphericalParameterSignature h₁ h₂ h₃ h
    exact not_finite (TriangleGroup a b c)
  · rcases (isSphericalParameterSignature_rows_iff a b c).1 h with
      ⟨-, -, -, rfl | ⟨rfl, rfl⟩ | h | h | h⟩
    · exact finite_one (Nat.gcd_pos_of_pos_left _ (by omega))
    · exact finite_two_two c h₃
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact finite_two_three_three
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact finite_two_three_four
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact finite_two_three_five

end TriangleGroup

end TauCeti
