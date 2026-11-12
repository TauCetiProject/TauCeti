/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
public import Mathlib.FieldTheory.Perfect
-- Proof-only: the points with singular reduction when the reduction is singular at the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
-- Proof-only: the coordinates of a solution in `(ϖ)` on the normal form at `III*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction
-- Proof-only: index two from the sums of points outside a subgroup.
import TauCeti.GroupTheory.Index.Two
-- Proof-only: Hensel's lemma for a polynomial that is not monic.
import TauCeti.RingTheory.Henselian.Basic
-- Proof-only: the maximal ideal of a local ring with principal maximal ideal.
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator
-- Proof-only: a double root of the tangent quadratic over a perfect residue field.
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

/-!
# Points with singular reduction: the index two cases

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪` and residue field
`k`, and let `W` be a Weierstrass curve over `F` with an integral model `W_O` over `O` whose
reduction is singular at the origin, that is `a₃, a₄, a₆ ∈ 𝔪`. The points with nonsingular
reduction form the subgroup `E₀(F)` of `W(F)` (`WeierstrassCurve.Affine.nonsingularReduction`).
When `F` is complete for a discrete valuation with perfect residue field and the equation is
minimal, the index `[E(F) : E₀(F)]` is the local index `c_v` that Tate's algorithm computes
(Silverman, *Advanced Topics*, IV.9, Table 4.1). This file computes the index at the reduction
symbols `III` and `III*`, where `c_v = 2`, and shows that it divides `2` when the tangent quadratic
at the singular point has no root in the residue field. Over a perfect residue field this is a
nonsplit node, where `c_v` is `1` or `2`.

The points of `W(F)` outside `E₀(F)` are the affine points `(x, y)` with `x, y ∈ 𝔪`
(`WeierstrassCurve.Affine.some_notMem_nonsingularReduction_iff`). Let `P = (x₁, y₁)` and
`Q = (x₂, y₂)` be two of them with `P + Q ≠ O`, let `ℓ` be the slope of the line through them, and
suppose that `P + Q = (x₃, y₃)` lies outside `E₀(F)` as well. Then `ℓ` is integral, since
`ℓ² + a₁ ℓ − a₂ = x₁ + x₂ + x₃`, and comparing the coefficients of `X` in the factorisation of the
Weierstrass cubic restricted to the line, with `ν = y₁ − ℓ x₁`
(`WeierstrassCurve.Affine.exists_chord_of_add_notMem_nonsingularReduction`),

`a₄ − a₃ ℓ − (2 ℓ + a₁) ν = x₁ x₂ + x₁ x₃ + x₂ x₃ ∈ 𝔪²`.

So the residue of `ℓ` is a root of the tangent quadratic `T² + a₁ T − a₂`. When that quadratic has
no root in `k` this is impossible, and at the symbol `III`, where `ϖ ∣ b₂`, `ϖ ∣ a₃`, `ϖ ∣ a₄`,
`ϖ² ∣ a₆` and `ϖ³ ∤ b₈` for a generator `ϖ` of `𝔪`, the root is double, so `2 ℓ + a₁ ∈ 𝔪` and
`a₄ ≡ a₃ ℓ` modulo `ϖ²`. Then

`b₈ = b₂ a₆ − (a₄ − a₃ ℓ) (a₄ + a₃ ℓ + a₁ a₃) − a₃² (ℓ² + a₁ ℓ − a₂)`

is divisible by `ϖ³`, which is excluded. In both cases the sum of two points outside `E₀(F)` lies in
`E₀(F)`, and the index divides `2`.

At the symbol `III` over a Henselian valuation ring with perfect residue field, a point with
singular reduction exists, so the index is exactly `2`. Writing `x = ϖ X` and `y = ϖ s X`, where
`s` lifts the double root of the tangent quadratic, the Weierstrass equation divided by `ϖ²`
becomes a cubic in `X` whose reduction is linear with unit coefficient `a₄ / ϖ − s a₃ / ϖ`: this is
again the condition `ϖ³ ∤ b₈`. Its leading coefficient `ϖ` is not a unit, so the root is lifted by
Hensel's lemma for polynomials that are not monic
(`Polynomial.exists_isRoot_sub_mem`).

At the symbol `III*`, where `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`, `ϖ³ ∣ a₄`, `ϖ⁵ ∣ a₆` and
`ϖ⁴ ∤ a₄`, comparing powers of `ϖ` in the Weierstrass equation shows that a point with singular
reduction has `ϖ² ∣ x` and `ϖ³ ∣ y`. If `P`, `Q` and `P + Q` all had singular reduction, then
`ℓ ∈ 𝔪` because `ℓ² + a₁ ℓ − a₂ = x₁ + x₂ + x₃`, and then `ϖ⁴` would divide every term of
`a₄ = x₁ x₂ + x₁ x₃ + x₂ x₃ + a₃ ℓ + (2 ℓ + a₁) ν`, which is excluded. So again the index divides
`2`. Over a Henselian valuation ring, with any residue field, the point `(ϖ² X, 0)` has singular
reduction, where `X` is a root of the Weierstrass cubic `x³ + a₂ x² + a₄ x + a₆` at `x = ϖ² X`,
divided by `ϖ⁵`, whose reduction is linear with the unit coefficient `a₄ / ϖ³`.

The cases `c_v = 1` are `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_Δ_notMem`,
`WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_not_splits` and
`WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_a₆_notMem`.

## Main results

* `WeierstrassCurve.Affine.exists_slope_of_notMem_nonsingularReduction`: when two points and their
  sum have singular reduction, the slope of the chord through the two points is integral and its
  residue is a root of the tangent quadratic.
* `WeierstrassCurve.Affine.add_mem_nonsingularReduction_of_tangentQuadratic_no_roots` and
  `WeierstrassCurve.Affine.index_nonsingularReduction_dvd_two_of_tangentQuadratic_no_roots`: when
  the tangent quadratic at the singular point has no root in the residue field, the sum of two
  points with singular reduction has nonsingular reduction, and `[E(F) : E₀(F)]` divides `2`.
* `WeierstrassCurve.Affine.add_mem_nonsingularReduction_of_isTateTerminal_III` and
  `WeierstrassCurve.Affine.index_nonsingularReduction_dvd_two_of_isTateTerminal_III`: the same at
  the reduction symbol `III`.
* `WeierstrassCurve.Affine.exists_notMem_nonsingularReduction_of_isTateTerminal_III` and
  `WeierstrassCurve.Affine.index_nonsingularReduction_eq_two_of_isTateTerminal_III`: at the symbol
  `III` over a Henselian valuation ring with perfect residue field, some point has singular
  reduction, and `[E(F) : E₀(F)] = 2`.
* `WeierstrassCurve.Affine.index_nonsingularReduction_dvd_two_of_isTateTerminal_IIIStar` and
  `WeierstrassCurve.Affine.index_nonsingularReduction_eq_two_of_isTateTerminal_IIIStar`: at the
  symbol `III*`, `[E(F) : E₀(F)]` divides `2`, and equals `2` over a Henselian valuation ring.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial
open TauCeti.IsLocalRing (mem_maximalIdeal_iff_dvd)

namespace WeierstrassCurve

/-- On the normal form of Tate's algorithm at the symbol `III`, if `ϖ` divides the value of the
tangent quadratic at `ℓ` and `ϖ²` divides `a₄ − a₃ ℓ`, then `ϖ³ ∣ b₈`: the stopping test for `III`
fails. -/
private theorem pow_three_dvd_b₈_of_sq_dvd_a₄_sub_a₃_mul {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {ϖ ℓ : R} (hb₂ : ϖ ∣ W.b₂) (h₃ : ϖ ∣ W.a₃) (h₄ : ϖ ∣ W.a₄)
    (h₆ : ϖ ^ 2 ∣ W.a₆) (hℓ : ϖ ∣ ℓ ^ 2 + W.a₁ * ℓ - W.a₂) (h : ϖ ^ 2 ∣ W.a₄ - W.a₃ * ℓ) :
    ϖ ^ 3 ∣ W.b₈ := by
  have hb₈ : W.b₈ = W.b₂ * W.a₆ - ((W.a₄ - W.a₃ * ℓ) * (W.a₄ + W.a₃ * ℓ + W.a₁ * W.a₃) +
      W.a₃ ^ 2 * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂)) := by
    rw [b₈, b₂]
    ring
  rw [hb₈, pow_succ']
  refine dvd_sub (mul_dvd_mul hb₂ h₆) (dvd_add ?_ ?_) <;> rw [← pow_succ', pow_succ]
  · exact mul_dvd_mul h (dvd_add (dvd_add h₄ (h₃.mul_right ℓ)) (h₃.mul_left _))
  · exact mul_dvd_mul (pow_dvd_pow_of_dvd h₃ 2) hℓ

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

variable [DecidableEq F]

/-- **The slope of a chord through two points with singular reduction whose sum has singular
reduction.** At a reduction singular at the origin, the slope `ℓ = W.slope x₁ x₂ y₁ y₂` of the line
through the two points `(x₁, y₁)` and `(x₂, y₂)` is integral and its residue is a root of the
tangent quadratic `T² + a₁ T − a₂`, and with `ν = y₁ − ℓ x₁ ∈ 𝔪` the coefficient
`a₄ − a₃ ℓ − (2 ℓ + a₁) ν` of the Weierstrass cubic restricted to the line lies in `𝔪²`. -/
theorem exists_slope_of_notMem_nonsingularReduction
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hP : Point.some _ _ h₁ ∉ W.nonsingularReduction v)
    (hQ : Point.some _ _ h₂ ∉ W.nonsingularReduction v)
    (hPQ : Point.some _ _ h₁ + Point.some _ _ h₂ ∉ W.nonsingularReduction v) :
    ∃ ℓ ν : v.valuationSubring, (ℓ : F) = W.slope x₁ x₂ y₁ y₂ ∧
      ν ∈ maximalIdeal v.valuationSubring ∧
      ℓ ^ 2 + (integralModel v.valuationSubring W).a₁ * ℓ -
        (integralModel v.valuationSubring W).a₂ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₄ - (integralModel v.valuationSubring W).a₃ * ℓ -
        (2 * ℓ + (integralModel v.valuationSubring W).a₁) * ν ∈
          maximalIdeal v.valuationSubring ^ 2 := by
  obtain ⟨X₁, Y₁, _, hP', hx₁, hy₁⟩ := exists_eq_some_of_notMem_nonsingularReduction v h₃ h₄ h₆ hP
  obtain ⟨rfl, rfl⟩ := Point.some.inj hP'
  obtain ⟨X₂, Y₂, _, hQ', hx₂, -⟩ := exists_eq_some_of_notMem_nonsingularReduction v h₃ h₄ h₆ hQ
  obtain ⟨rfl, rfl⟩ := Point.some.inj hQ'
  obtain ⟨x₃, -, ℓ, -, -, hℓ, hx₃, -, hs, -, hc, -⟩ :=
    exists_chord_of_add_notMem_nonsingularReduction v h₃ h₄ h₆ hPQ
  refine ⟨ℓ, Y₁ - ℓ * X₁, hℓ, sub_mem hy₁ ((maximalIdeal _).mul_mem_left _ hx₁), ?_, ?_⟩
  · rw [hs]
    exact add_mem (add_mem hx₁ hx₂) hx₃
  · rw [hc, pow_two]
    exact add_mem (add_mem (Ideal.mul_mem_mul hx₁ hx₂) (Ideal.mul_mem_mul hx₁ hx₃))
      (Ideal.mul_mem_mul hx₂ hx₃)

/-! ### A tangent quadratic with no root -/

/-- **When the tangent quadratic has no root, the sum of two points with singular reduction has
nonsingular reduction.** Here the reduction of the integral model is singular at the origin and its
tangent quadratic `T² + a₁ T − a₂` has no root in the residue field. When the residue field is
perfect, or `b₂` is a unit, the singular point is then a node whose tangent directions are not
rational, and for a discrete valuation, on a minimal equation, this is nonsplit multiplicative
reduction. Over an imperfect residue field of characteristic `2` the singular point may instead be
a cusp. -/
theorem add_mem_nonsingularReduction_of_tangentQuadratic_no_roots
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0)
    {P Q : W.Point} (hP : P ∉ W.nonsingularReduction v) (hQ : Q ∉ W.nonsingularReduction v) :
    P + Q ∈ W.nonsingularReduction v := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (zero_mem _) hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd (zero_mem _) hQ
  by_contra hPQ
  obtain ⟨ℓ, _, -, -, hℓ, -⟩ := exists_slope_of_notMem_nonsingularReduction v h₃ h₄ h₆ hP hQ hPQ
  exact hroot (residue _ ℓ) (by simpa using (residue_eq_zero_iff _).2 hℓ)

/-- **When the tangent quadratic has no root, `[E(F) : E₀(F)]` divides `2`.** Here the reduction of
the integral model is singular at the origin and its tangent quadratic `T² + a₁ T − a₂` has no root
in the residue field. When the residue field is perfect, or `b₂` is a unit, this is a nonsplit node;
for a discrete valuation, on a minimal equation with nonsplit multiplicative reduction of type
`Iₙ`, Tate's algorithm reports the local index `gcd(2, n)`. -/
theorem index_nonsingularReduction_dvd_two_of_tangentQuadratic_no_roots
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0) :
    (W.nonsingularReduction v).index ∣ 2 :=
  AddSubgroup.index_dvd_two_of_add_mem fun _ _ ↦
    add_mem_nonsingularReduction_of_tangentQuadratic_no_roots v h₃ h₄ h₆ hroot

/-- Over a Henselian local ring, the cubic `−ϖ X³ + e₂ X² − e₁ X − γ` with `ϖ, e₂ ∈ 𝔪` and `e₁` a
unit has a root `X`, at which its derivative `−3 ϖ X² + 2 e₂ X − e₁` is a unit: its reduction is
linear with unit coefficient. -/
private theorem exists_cubic_eq_zero {R : Type*} [CommRing R] [HenselianLocalRing R] {ϖ e₂ e₁ : R}
    (hϖ : ϖ ∈ maximalIdeal R) (he₂ : e₂ ∈ maximalIdeal R) (he₁ : IsUnit e₁) (γ : R) :
    ∃ X : R, -ϖ * X ^ 3 + e₂ * X ^ 2 - e₁ * X - γ = 0 ∧
      IsUnit (-3 * ϖ * X ^ 2 + 2 * e₂ * X - e₁) := by
  set p : R[X] := -C ϖ * X ^ 3 + C e₂ * X ^ 2 - C e₁ * X - C γ with hp
  have hder (z : R) : p.derivative.eval z = -3 * ϖ * z ^ 2 + 2 * e₂ * z - e₁ := by
    simp [hp]
    ring
  have hunit (z : R) : IsUnit (-3 * ϖ * z ^ 2 + 2 * e₂ * z - e₁) := by
    have hz : -3 * ϖ * z ^ 2 + 2 * e₂ * z - e₁ = -e₁ + (ϖ * (-3 * z ^ 2) + e₂ * (2 * z)) := by ring
    rw [hz, ← residue_ne_zero_iff_isUnit, map_add, (residue_eq_zero_iff _).2
      (add_mem ((maximalIdeal R).mul_mem_right _ hϖ) ((maximalIdeal R).mul_mem_right _ he₂)),
      add_zero, map_neg, neg_ne_zero, residue_ne_zero_iff_isUnit]
    exact he₁
  -- the root `X₀ = −γ / e₁` of the reduction
  set X₀ := -(γ * ↑he₁.unit⁻¹)
  have hX₀ : e₁ * X₀ = -γ := by
    rw [mul_neg, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  obtain ⟨X, hX, -⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R) p
    (a₀ := X₀) (by
      have hpX₀ : p.eval X₀ = ϖ * -X₀ ^ 3 + e₂ * X₀ ^ 2 := by
        simp only [hp, eval_sub, eval_add, eval_mul, eval_neg, eval_C, eval_pow, eval_X]
        linear_combination (-1 : R) * hX₀
      rw [hpX₀]
      exact add_mem ((maximalIdeal R).mul_mem_right _ hϖ) ((maximalIdeal R).mul_mem_right _ he₂))
    (by simpa [hder X₀] using (hunit X₀).map (Ideal.Quotient.mk (maximalIdeal R)))
  exact ⟨X, by simpa [hp] using hX.eq_zero, hunit X⟩

/-! ### The reduction symbol `III` -/

/-- **At the reduction symbol `III`, the sum of two points with singular reduction has nonsingular
reduction.** Here `ϖ` generates the maximal ideal of the valuation ring, and Tate's algorithm, run
on the integral model with uniformiser `ϖ`, stops with the symbol `III`: `ϖ ∣ b₂`, `ϖ ∣ a₃`,
`ϖ ∣ a₄`, `ϖ² ∣ a₆` and `ϖ³ ∤ b₈`. -/
theorem add_mem_nonsingularReduction_of_isTateTerminal_III {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .III) {P Q : W.Point}
    (hP : P ∉ W.nonsingularReduction v) (hQ : Q ∉ W.nonsingularReduction v) :
    P + Q ∈ W.nonsingularReduction v := by
  set Wo := integralModel v.valuationSubring W
  obtain ⟨hb₂, h₃, h₄, h₆, hb₈⟩ := isTateTerminal_III.1 h
  have key₂ (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ^ 2 ↔ ϖ ^ 2 ∣ z := by
    rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (zero_mem _) hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd (zero_mem _) hQ
  by_contra hPQ
  obtain ⟨ℓ, ν, -, hν, hℓ, hc⟩ := exists_slope_of_notMem_nonsingularReduction v
    ((mem_maximalIdeal_iff_dvd hϖ).2 h₃) ((mem_maximalIdeal_iff_dvd hϖ).2 h₄)
    ((mem_maximalIdeal_iff_dvd hϖ).2 ((dvd_pow_self ϖ two_ne_zero).trans h₆)) hP hQ hPQ
  -- the residue of `ℓ` is the double root of the tangent quadratic, whose discriminant is `b₂`
  have h2 : ϖ ∣ 2 * ℓ + Wo.a₁ := by
    refine (mem_maximalIdeal_iff_dvd hϖ).1
      ((maximalIdeal.isMaximal v.valuationSubring).isPrime.mem_of_pow_mem 2 ?_)
    have hsq : (2 * ℓ + Wo.a₁) ^ 2 = 4 * (ℓ ^ 2 + Wo.a₁ * ℓ - Wo.a₂) + Wo.b₂ := by
      rw [b₂]
      ring
    rw [hsq, mem_maximalIdeal_iff_dvd hϖ]
    exact dvd_add (((mem_maximalIdeal_iff_dvd hϖ).1 hℓ).mul_left 4) hb₂
  have h42 : ϖ ^ 2 ∣ Wo.a₄ - Wo.a₃ * ℓ := by
    have hsplit : Wo.a₄ - Wo.a₃ * ℓ =
        (Wo.a₄ - Wo.a₃ * ℓ - (2 * ℓ + Wo.a₁) * ν) + (2 * ℓ + Wo.a₁) * ν := by
      ring
    rw [hsplit]
    exact dvd_add ((key₂ _).1 hc) (sq ϖ ▸ mul_dvd_mul h2 ((mem_maximalIdeal_iff_dvd hϖ).1 hν))
  exact hb₈ (Wo.pow_three_dvd_b₈_of_sq_dvd_a₄_sub_a₃_mul hb₂ h₃ h₄ h₆
    ((mem_maximalIdeal_iff_dvd hϖ).1 hℓ) h42)

/-- **At the reduction symbol `III`, `[E(F) : E₀(F)]` divides `2`.** Here `ϖ` generates the
maximal ideal of the valuation ring, and Tate's algorithm, run on the integral model with
uniformiser `ϖ`, stops with the symbol `III`. -/
theorem index_nonsingularReduction_dvd_two_of_isTateTerminal_III {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .III) :
    (W.nonsingularReduction v).index ∣ 2 :=
  AddSubgroup.index_dvd_two_of_add_mem fun _ _ ↦
    add_mem_nonsingularReduction_of_isTateTerminal_III v hϖ h

/-- **At the reduction symbol `III`, some point has singular reduction**, when the valuation ring
is Henselian, for instance complete, and its residue field is perfect. Here `ϖ` generates the
maximal ideal of the valuation ring, and Tate's algorithm, run on the integral model with
uniformiser `ϖ`, stops with the symbol `III`. The point is `(ϖ X, ϖ s X)`, where `s` lifts the
double root of the tangent quadratic `T² + a₁ T − a₂` and `X` is a root of the Weierstrass equation
along the line `y = s x`, divided by `ϖ²`: a cubic whose reduction is linear with unit
coefficient. -/
theorem exists_notMem_nonsingularReduction_of_isTateTerminal_III
    [HenselianLocalRing v.valuationSubring] [PerfectField (ResidueField v.valuationSubring)]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .III) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v := by
  set Wo := integralModel v.valuationSubring W
  obtain ⟨hb₂, ⟨α, hα⟩, ⟨β, hβ⟩, ⟨γ, hγ⟩, hb₈⟩ := isTateTerminal_III.1 h
  -- `ϖ ≠ 0`, since otherwise `a₃ = a₄ = a₆ = 0` and then `b₈ = 0`
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hb₈ (by simp [b₈, hα, hβ, hγ])
  -- `s` lifts the double root of `T² + a₁ T − a₂`, whose discriminant is `b₂`
  obtain ⟨s, -, hs⟩ :=
    TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal
      (a := Wo.a₁) (b := Wo.a₂) ((mem_maximalIdeal_iff_dvd hϖ).2 (by rwa [b₂] at hb₂))
  have he₂ : s ^ 2 + Wo.a₁ * s - Wo.a₂ ∈ maximalIdeal v.valuationSubring := by
    convert neg_mem hs using 1
    ring
  -- `β − s α = (a₄ − a₃ s) / ϖ` is a unit, since otherwise `ϖ³ ∣ b₈`
  have he₁ : IsUnit (β - s * α) := by
    by_contra hne
    obtain ⟨d, hd⟩ := (mem_maximalIdeal_iff_dvd hϖ).1 ((mem_maximalIdeal _).2 hne)
    refine hb₈ (Wo.pow_three_dvd_b₈_of_sq_dvd_a₄_sub_a₃_mul hb₂ ⟨α, hα⟩ ⟨β, hβ⟩ ⟨γ, hγ⟩
      ((mem_maximalIdeal_iff_dvd hϖ).1 he₂) ⟨d, ?_⟩)
    rw [hβ, hα]
    linear_combination ϖ * hd
  -- the Weierstrass equation at `(ϖ X, ϖ s X)`, divided by `ϖ²`, has a root `X`
  obtain ⟨X, hX, hXd⟩ := exists_cubic_eq_zero ((mem_maximalIdeal_iff_dvd hϖ).2 dvd_rfl) he₂ he₁ γ
  have hns : Wo.toAffine.Nonsingular (ϖ * X) (ϖ * (s * X)) := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff]
      linear_combination ϖ ^ 2 * hX + ϖ * s * X * hα - ϖ * X * hβ - hγ, ?_⟩
    by_contra! hn
    obtain ⟨hx, hy⟩ := hn
    -- `ϖ` times the derivative of the cubic is `∂/∂x + s ∂/∂y` of the Weierstrass equation
    refine hϖ0 (hXd.mul_left_eq_zero.1 ?_)
    linear_combination hx + s * hy + hβ - s * hα
  have hF := (nonsingular_integralModel_iff v).1 hns
  have hmem (z : v.valuationSubring) : v ((ϖ * z : v.valuationSubring) : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1
      ((mem_maximalIdeal_iff_dvd hϖ).2 (dvd_mul_right ϖ z))
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v
    ((mem_maximalIdeal_iff_dvd hϖ).2 ⟨α, hα⟩) ((mem_maximalIdeal_iff_dvd hϖ).2 ⟨β, hβ⟩)
    ((mem_maximalIdeal_iff_dvd hϖ).2 ⟨ϖ * γ, by rw [hγ]; ring⟩) hF).2 ⟨hmem _, hmem _⟩⟩

/-- **At the reduction symbol `III`, `[E(F) : E₀(F)] = 2`**, when the valuation ring is Henselian,
for instance complete, and its residue field is perfect. This is the local index `c_v = 2` that
Tate's algorithm reports at `III`. Here `ϖ` generates the maximal ideal of the valuation ring, and
Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol `III`. -/
theorem index_nonsingularReduction_eq_two_of_isTateTerminal_III
    [HenselianLocalRing v.valuationSubring] [PerfectField (ResidueField v.valuationSubring)]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .III) :
    (W.nonsingularReduction v).index = 2 := by
  obtain ⟨P, hP⟩ := exists_notMem_nonsingularReduction_of_isTateTerminal_III v hϖ h
  exact AddSubgroup.index_eq_two_of_add_mem
    (fun _ _ ↦ add_mem_nonsingularReduction_of_isTateTerminal_III v hϖ h) hP

/-! ### The reduction symbol `III*` -/

omit [DecidableEq F] in
/-- At the symbol `III*`, the uniformiser is prime and the reduction is singular at the origin:
`a₃`, `a₄` and `a₆` lie in the maximal ideal. -/
private theorem prime_and_mem_maximalIdeal_of_isTateTerminal_IIIStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IIIStar) :
    Prime ϖ ∧ (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring := by
  obtain ⟨-, -, -, h₄, -, h₄'⟩ := isTateTerminal_IIIStar.1 h
  obtain ⟨-, d₃, d₄, d₆⟩ := h.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ fun _ ↦ nofun
  -- `ϖ ≠ 0`, since otherwise `a₄ = 0`
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h₄' (by simpa using h₄)
  refine ⟨(Ideal.span_singleton_prime hϖ0).1 (hϖ ▸ (maximalIdeal.isMaximal _).isPrime), ?_⟩
  simp only [hϖ, Ideal.mem_span_singleton]
  exact ⟨d₃, d₄, d₆⟩

/-- **At the reduction symbol `III*`, the sum of two points with singular reduction has
nonsingular reduction.** Here `ϖ` generates the maximal ideal of the valuation ring, and Tate's
algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol `III*`:
`ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`, `ϖ³ ∣ a₄`, `ϖ⁵ ∣ a₆` and `ϖ⁴ ∤ a₄`. -/
theorem add_mem_nonsingularReduction_of_isTateTerminal_IIIStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IIIStar) {P Q : W.Point}
    (hP : P ∉ W.nonsingularReduction v) (hQ : Q ∉ W.nonsingularReduction v) :
    P + Q ∈ W.nonsingularReduction v := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆, h₄'⟩ := isTateTerminal_IIIStar.1 h
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IIIStar v hϖ h
  by_contra hPQ
  obtain ⟨x₁, y₁, h₁', rfl, hx₁, hy₁⟩ := exists_eq_some_of_notMem_nonsingularReduction v m₃ m₄ m₆ hP
  obtain ⟨x₂, y₂, h₂', rfl, hx₂, hy₂⟩ := exists_eq_some_of_notMem_nonsingularReduction v m₃ m₄ m₆ hQ
  obtain ⟨x₃, y₃, ℓ, hN₃, -, -, hx₃, hy₃, hs, -, hc, -⟩ :=
    exists_chord_of_add_notMem_nonsingularReduction v m₃ m₄ m₆ hPQ
  rw [mem_maximalIdeal_iff_dvd hϖ] at hx₁ hy₁ hx₂ hy₂ hx₃ hy₃
  -- the three points on the chord have `ϖ² ∣ x` and `ϖ³ ∣ y`
  obtain ⟨d₁, e₁⟩ := sq_dvd_and_pow_three_dvd_of_equation _ hp h₁ h₂ h₃ h₄ h₆
    ((equation_integralModel_iff v).2 h₁'.left) hx₁ hy₁
  obtain ⟨d₂, -⟩ := sq_dvd_and_pow_three_dvd_of_equation _ hp h₁ h₂ h₃ h₄ h₆
    ((equation_integralModel_iff v).2 h₂'.left) hx₂ hy₂
  obtain ⟨d₃, -⟩ := sq_dvd_and_pow_three_dvd_of_equation _ hp h₁ h₂ h₃ h₄ h₆
    ((equation_integralModel_iff v).2 hN₃.left) hx₃ hy₃
  -- so the slope is divisible by `ϖ`, since `ℓ² = x₁ + x₂ + x₃ + a₂ − a₁ ℓ`
  have hℓ : ϖ ∣ ℓ := by
    refine hp.dvd_of_dvd_pow (n := 2) ?_
    rw [show ℓ ^ 2 = x₁ + x₂ + x₃ + (integralModel v.valuationSubring W).a₂ -
        (integralModel v.valuationSubring W).a₁ * ℓ by linear_combination hs]
    exact dvd_sub (dvd_add (dvd_add (dvd_add hx₁ hx₂) hx₃)
      ((dvd_pow_self ϖ two_ne_zero).trans h₂)) (h₁.mul_right ℓ)
  -- and then `ϖ⁴` divides every term of `a₄ = ∑ xᵢ xⱼ + a₃ ℓ + (2 ℓ + a₁) (y₁ − ℓ x₁)`
  refine h₄' ?_
  rw [show (integralModel v.valuationSubring W).a₄ = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ +
      (integralModel v.valuationSubring W).a₃ * ℓ +
        (2 * ℓ + (integralModel v.valuationSubring W).a₁) * (y₁ - ℓ * x₁) by
    linear_combination hc]
  have e₂ : ϖ ^ 4 = ϖ ^ 2 * ϖ ^ 2 := by ring
  have e₃ : ϖ ^ 4 = ϖ ^ 3 * ϖ := by ring
  have e₁' : ϖ ^ 3 = ϖ * ϖ ^ 2 := by ring
  refine dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_
  · exact e₂ ▸ mul_dvd_mul d₁ d₂
  · exact e₂ ▸ mul_dvd_mul d₁ d₃
  · exact e₂ ▸ mul_dvd_mul d₂ d₃
  · exact e₃ ▸ mul_dvd_mul h₃ hℓ
  · rw [show ϖ ^ 4 = ϖ * ϖ ^ 3 by ring]
    exact mul_dvd_mul (dvd_add (hℓ.mul_left 2) h₁) (dvd_sub e₁ (e₁' ▸ mul_dvd_mul hℓ d₁))

/-- **At the reduction symbol `III*`, `[E(F) : E₀(F)]` divides `2`.** Here `ϖ` generates the
maximal ideal of the valuation ring, and Tate's algorithm, run on the integral model with
uniformiser `ϖ`, stops with the symbol `III*`. -/
theorem index_nonsingularReduction_dvd_two_of_isTateTerminal_IIIStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IIIStar) :
    (W.nonsingularReduction v).index ∣ 2 :=
  AddSubgroup.index_dvd_two_of_add_mem fun _ _ ↦
    add_mem_nonsingularReduction_of_isTateTerminal_IIIStar v hϖ h

/-- **At the reduction symbol `III*`, some point has singular reduction**, when the valuation ring
is Henselian, for instance complete. Here `ϖ` generates the maximal ideal of the valuation ring,
and Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol
`III*`. The point is `(ϖ² X, 0)`, where `X` is a root of `x³ + a₂ x² + a₄ x + a₆` at
`x = ϖ² X`, divided by `ϖ⁵`: a cubic whose reduction is linear with the unit coefficient
`a₄ / ϖ³`. No hypothesis on the residue field is needed. -/
theorem exists_notMem_nonsingularReduction_of_isTateTerminal_IIIStar
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IIIStar) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v := by
  obtain ⟨-, ⟨A₂, hA₂⟩, -, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩, h₄'⟩ := isTateTerminal_IIIStar.1 h
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IIIStar v hϖ h
  -- `a₄ / ϖ³` is a unit, since `ϖ⁴ ∤ a₄`
  have he₁ : IsUnit A₄ := by
    by_contra hn
    obtain ⟨d, hd⟩ := (mem_maximalIdeal_iff_dvd hϖ).1 ((mem_maximalIdeal _).2 hn)
    exact h₄' ⟨d, by rw [hA₄, hd]; ring⟩
  -- the equation at `(ϖ² X, 0)`, divided by `ϖ⁵`, has a root `X`
  obtain ⟨X, hX, hXd⟩ := exists_cubic_eq_zero (e₂ := -(ϖ * A₂))
    ((mem_maximalIdeal_iff_dvd hϖ).2 dvd_rfl) ((mem_maximalIdeal_iff_dvd hϖ).2 ⟨-A₂, by ring⟩)
    he₁ A₆
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular (ϖ ^ 2 * X) 0 := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff, hA₂, hA₄, hA₆]
      linear_combination ϖ ^ 5 * hX, ?_⟩
    by_contra! hn
    obtain ⟨hx, -⟩ := hn
    rw [hA₂, hA₄] at hx
    -- `ϖ³` times the derivative of the cubic is `∂/∂x` of the Weierstrass equation
    exact pow_ne_zero 3 hp.ne_zero (hXd.mul_left_eq_zero.1 (by linear_combination hx))
  have hF := (nonsingular_integralModel_iff v).1 hns
  have hx : v ((ϖ ^ 2 * X : v.valuationSubring) : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1
      ((mem_maximalIdeal_iff_dvd hϖ).2 (Dvd.intro (ϖ * X) (by ring)))
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hF).2 ⟨hx, by simp⟩⟩

/-- **At the reduction symbol `III*`, `[E(F) : E₀(F)] = 2`**, when the valuation ring is Henselian,
for instance complete. This is the local index `c_v = 2` that Tate's algorithm reports at `III*`.
Here `ϖ` generates the maximal ideal of the valuation ring, and Tate's algorithm, run on the
integral model with uniformiser `ϖ`, stops with the symbol `III*`. -/
theorem index_nonsingularReduction_eq_two_of_isTateTerminal_IIIStar
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IIIStar) :
    (W.nonsingularReduction v).index = 2 := by
  obtain ⟨P, hP⟩ := exists_notMem_nonsingularReduction_of_isTateTerminal_IIIStar v hϖ h
  exact AddSubgroup.index_eq_two_of_add_mem
    (fun _ _ ↦ add_mem_nonsingularReduction_of_isTateTerminal_IIIStar v hϖ h) hP

end Affine

end WeierstrassCurve

end
