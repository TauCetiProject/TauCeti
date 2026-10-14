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
-- Proof-only: index two from the sums of points outside a subgroup.
import TauCeti.GroupTheory.Index.Two
-- Proof-only: Hensel's lemma for a polynomial that is not monic.
import TauCeti.RingTheory.Henselian.Basic
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
symbol `III`, where `c_v = 2`, and shows that it divides `2` when the tangent quadratic at the
singular point has no root in the residue field. Over a perfect residue field this is a nonsplit
node, where `c_v` is `1` or `2`.

The points of `W(F)` outside `E₀(F)` are the affine points `(x, y)` with `x, y ∈ 𝔪`
(`WeierstrassCurve.Affine.some_notMem_nonsingularReduction_iff`). Let `P = (x₁, y₁)` and
`Q = (x₂, y₂)` be two of them with `P + Q ≠ O`, let `ℓ` be the slope of the line through them, and
suppose that `P + Q = -(x₃, y₃)` lies outside `E₀(F)` as well. Then `ℓ` is integral, since
`ℓ² + a₁ ℓ − a₂ = x₁ + x₂ + x₃`, and comparing the coefficients of `X` in the factorisation of the
Weierstrass cubic restricted to the line, with `ν = y₁ − ℓ x₁`,

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
(`TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal`).

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

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial

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

/-- **The chord through two points with singular reduction whose sum has singular reduction.** At
a reduction singular at the origin, the slope `ℓ = W.slope x₁ x₂ y₁ y₂` of the line through the two
points `(x₁, y₁)` and `(x₂, y₂)` is integral and its residue is a root of the tangent quadratic
`T² + a₁ T − a₂`, and with `ν = y₁ − ℓ x₁ ∈ 𝔪` the coefficient `a₄ − a₃ ℓ − (2 ℓ + a₁) ν` of the
Weierstrass cubic restricted to the line lies in `𝔪²`. -/
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
  set O := v.valuationSubring
  set Wo := integralModel O W
  obtain ⟨hx₁, hy₁⟩ := (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ h₁).1 hP
  obtain ⟨hx₂, -⟩ := (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ h₂).1 hQ
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
    rintro ⟨rfl, rfl⟩
    exact hPQ (by rw [Point.add_of_Y_eq rfl rfl]; exact zero_mem _)
  rw [Point.add_some hxy] at hPQ
  obtain ⟨hx₃, -⟩ := (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ _).1 hPQ
  set ℓ := W.slope x₁ x₂ y₁ y₂
  set x₃ := W.addX x₁ x₂ ℓ with hx₃def
  have hO {z : F} (hz : v z < 1) : z ∈ O := (v.mem_valuationSubring_iff z).2 hz.le
  set X₁ : O := ⟨x₁, hO hx₁⟩
  set X₂ : O := ⟨x₂, hO hx₂⟩
  set X₃ : O := ⟨x₃, hO hx₃⟩
  set Y₁ : O := ⟨y₁, hO hy₁⟩
  have hX₁ : X₁ ∈ maximalIdeal O := (Valuation.mem_maximalIdeal_iff (v := v)).2 hx₁
  have hX₂ : X₂ ∈ maximalIdeal O := (Valuation.mem_maximalIdeal_iff (v := v)).2 hx₂
  have hX₃ : X₃ ∈ maximalIdeal O := (Valuation.mem_maximalIdeal_iff (v := v)).2 hx₃
  have hY₁ : Y₁ ∈ maximalIdeal O := (Valuation.mem_maximalIdeal_iff (v := v)).2 hy₁
  have hℓ : ℓ ∈ O := (v.mem_valuationSubring_iff ℓ).2
    (valuation_le_one_of_valuation_addX_le_one v hx₁.le hx₂.le hx₃.le)
  set L : O := ⟨ℓ, hℓ⟩
  -- the coefficient of `X` in `W(X, ℓ (X − x₁) + y₁) = −(X − x₁) (X − x₂) (X − x₃)`
  have hc : 2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ + (-W.a₁ * y₁ + W.a₄) =
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ := by
    have key := W.addPolynomial_slope h₁.left h₂.left hxy
    rw [addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj] at key
    exact congrArg Cubic.c ((Cubic.toPoly_injective _ _).1 key)
  refine ⟨L, Y₁ - L * X₁, rfl, sub_mem hY₁ ((maximalIdeal O).mul_mem_left _ hX₁), ?_, ?_⟩
  · have hs : L ^ 2 + Wo.a₁ * L - Wo.a₂ = X₁ + X₂ + X₃ := by
      apply Subtype.ext
      push_cast
      rw [coe_integralModel_a₁, coe_integralModel_a₂]
      simp only [L, X₁, X₂, X₃, hx₃def, addX]
      ring
    rw [hs]
    exact add_mem (add_mem hX₁ hX₂) hX₃
  · have hs : Wo.a₄ - Wo.a₃ * L - (2 * L + Wo.a₁) * (Y₁ - L * X₁) =
        X₁ * X₂ + X₁ * X₃ + X₂ * X₃ := by
      apply Subtype.ext
      push_cast
      have h2 : ((2 : O) : F) = 2 := by simpa using map_ofNat (algebraMap O F) 2
      rw [coe_integralModel_a₁, coe_integralModel_a₃, coe_integralModel_a₄, h2]
      simp only [L, X₁, X₂, X₃, Y₁]
      linear_combination hc
    rw [hs, pow_two]
    exact add_mem (add_mem (Ideal.mul_mem_mul hX₁ hX₂) (Ideal.mul_mem_mul hX₁ hX₃))
      (Ideal.mul_mem_mul hX₂ hX₃)

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
  obtain ⟨X, hX, -⟩ := TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal p
    (a₀ := X₀) (by
      have hpX₀ : p.eval X₀ = ϖ * -X₀ ^ 3 + e₂ * X₀ ^ 2 := by
        simp only [hp, eval_sub, eval_add, eval_mul, eval_neg, eval_C, eval_pow, eval_X]
        linear_combination (-1 : R) * hX₀
      rw [hpX₀]
      exact add_mem ((maximalIdeal R).mul_mem_right _ hϖ) ((maximalIdeal R).mul_mem_right _ he₂))
    (hder X₀ ▸ hunit X₀)
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
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  have key₂ (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ^ 2 ↔ ϖ ^ 2 ∣ z := by
    rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (zero_mem _) hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd (zero_mem _) hQ
  by_contra hPQ
  obtain ⟨ℓ, ν, -, hν, hℓ, hc⟩ := exists_slope_of_notMem_nonsingularReduction v ((key _).2 h₃)
    ((key _).2 h₄) ((key _).2 ((dvd_pow_self ϖ two_ne_zero).trans h₆)) hP hQ hPQ
  -- the residue of `ℓ` is the double root of the tangent quadratic, whose discriminant is `b₂`
  have h2 : ϖ ∣ 2 * ℓ + Wo.a₁ := by
    refine (key _).1 ((maximalIdeal.isMaximal v.valuationSubring).isPrime.mem_of_pow_mem 2 ?_)
    have hsq : (2 * ℓ + Wo.a₁) ^ 2 = 4 * (ℓ ^ 2 + Wo.a₁ * ℓ - Wo.a₂) + Wo.b₂ := by
      rw [b₂]
      ring
    rw [hsq, key]
    exact dvd_add (((key _).1 hℓ).mul_left 4) hb₂
  have h42 : ϖ ^ 2 ∣ Wo.a₄ - Wo.a₃ * ℓ := by
    have hsplit : Wo.a₄ - Wo.a₃ * ℓ =
        (Wo.a₄ - Wo.a₃ * ℓ - (2 * ℓ + Wo.a₁) * ν) + (2 * ℓ + Wo.a₁) * ν := by
      ring
    rw [hsplit]
    exact dvd_add ((key₂ _).1 hc) (sq ϖ ▸ mul_dvd_mul h2 ((key _).1 hν))
  exact hb₈ (Wo.pow_three_dvd_b₈_of_sq_dvd_a₄_sub_a₃_mul hb₂ h₃ h₄ h₆ ((key _).1 hℓ) h42)

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
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  -- `ϖ ≠ 0`, since otherwise `a₃ = a₄ = a₆ = 0` and then `b₈ = 0`
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hb₈ (by simp [b₈, hα, hβ, hγ])
  -- `s` lifts the double root of `T² + a₁ T − a₂`, whose discriminant is `b₂`
  obtain ⟨s, -, hs⟩ :=
    TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal
      (a := Wo.a₁) (b := Wo.a₂) ((key _).2 (by rwa [b₂] at hb₂))
  have he₂ : s ^ 2 + Wo.a₁ * s - Wo.a₂ ∈ maximalIdeal v.valuationSubring := by
    convert neg_mem hs using 1
    ring
  -- `β − s α = (a₄ − a₃ s) / ϖ` is a unit, since otherwise `ϖ³ ∣ b₈`
  have he₁ : IsUnit (β - s * α) := by
    by_contra hne
    obtain ⟨d, hd⟩ := (key _).1 ((mem_maximalIdeal _).2 hne)
    refine hb₈ (Wo.pow_three_dvd_b₈_of_sq_dvd_a₄_sub_a₃_mul hb₂ ⟨α, hα⟩ ⟨β, hβ⟩ ⟨γ, hγ⟩
      ((key _).1 he₂) ⟨d, ?_⟩)
    rw [hβ, hα]
    linear_combination ϖ * hd
  -- the Weierstrass equation at `(ϖ X, ϖ s X)`, divided by `ϖ²`, has a root `X`
  obtain ⟨X, hX, hXd⟩ := exists_cubic_eq_zero ((key ϖ).2 dvd_rfl) he₂ he₁ γ
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
  have hF : W.Nonsingular ((ϖ * X : v.valuationSubring) : F)
      ((ϖ * (s * X) : v.valuationSubring) : F) := by
    have := (Wo.toAffine.map_nonsingular (IsFractionRing.injective _ F) _ _).mpr hns
    rwa [← baseChange_integralModel_eq v.valuationSubring W]
  have hmem (z : v.valuationSubring) : v ((ϖ * z : v.valuationSubring) : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 (dvd_mul_right ϖ z))
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v ((key _).2 ⟨α, hα⟩)
    ((key _).2 ⟨β, hβ⟩) ((key _).2 ⟨ϖ * γ, by rw [hγ]; ring⟩) hF).2 ⟨hmem _, hmem _⟩⟩

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

end Affine

end WeierstrassCurve

end
