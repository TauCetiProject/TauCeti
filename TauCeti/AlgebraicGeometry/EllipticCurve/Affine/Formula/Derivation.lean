/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations and the addition law on a Weierstrass curve

Let `W` be a Weierstrass curve over `R`, let `K` be an `R`-algebra and let `D : Derivation R K M` be
a derivation on `K` over `R`. Writing `W_X` and `W_Y` for the partial derivatives `polynomialX` and
`polynomialY` of the Weierstrass polynomial, this file records how `D` interacts with the points of
`W⁄K` and with the formulae of the addition law.

## Main statements

* `Equation.evalEval_polynomialX_smul_add_evalEval_polynomialY_smul_eq_zero` (in the namespace
  `WeierstrassCurve.Affine`): at a point `(x, y)` of `W⁄K`, `W_X(x, y) • D x + W_Y(x, y) • D y = 0`,
  the differential of the Weierstrass equation, over any commutative ring `K`.
* `WeierstrassCurve.Affine.derivation_evalEval_polynomialX`,
  `WeierstrassCurve.Affine.derivation_evalEval_polynomialY` and
  `WeierstrassCurve.Affine.derivation_addX`: the chain rule for `W_X`, `W_Y` and `addX`.
* `WeierstrassCurve.Affine.Equation.derivation_Y_eq_smul_derivation_X`: over a field, at a point
  where `W_Y` does not vanish, `D y = (-W_X(x, y) / W_Y(x, y)) • D x`.
* `WeierstrassCurve.Affine.derivation_slope_of_X_ne` and
  `WeierstrassCurve.Affine.derivation_slope_self_of_Y_ne`: the chain rule for the chord and the
  tangent slope.
* `WeierstrassCurve.Affine.derivation_addX_slope`: if `(x₃, y₃)` is the sum of two points
  `(x₁, y₁)` and `(x₂, y₂)` of `W⁄K` at which `W_Y` does not vanish (when `x₁ ≠ x₂`), then
  `D x₃ = W_Y(x₃, y₃) • (W_Y(x₁, y₁)⁻¹ • D x₁ + W_Y(x₂, y₂)⁻¹ • D x₂)`; when `W_Y(x₃, y₃)` is
  nonzero as well, `WeierstrassCurve.Affine.inv_smul_derivation_addX_slope` divides by it:
  `W_Y(x₃, y₃)⁻¹ • D x₃ = W_Y(x₁, y₁)⁻¹ • D x₁ + W_Y(x₂, y₂)⁻¹ • D x₂`.

The last two identities are the additivity of the differential `dx / W_Y`, with and without the
denominator at the sum cleared. On an elliptic curve `dx / W_Y` is the invariant differential, and
the identity is the computation behind the additivity of its pullback along a sum of morphisms
(Silverman, *The Arithmetic of Elliptic Curves*, III.5.2); the version for two points of `W⁄K` and
their sum is in `Affine/Point/Derivation.lean`. Everything is stated for an arbitrary derivation,
so that it applies to the Kähler differentials of a function field without any further hypothesis.

## Provenance

The identity for two points with distinct `x`-coordinates generalises the computation
`kaehlerD_addPullback_x_eq_one_add_smul_omega` of `HasseWeil/RouteBGeneral.lean` in
[AINTLIB](https://github.com/CBirkbeck/AINTLIB) (commit `513e83879e2f8cbc626eb9e04d660e92be16ccba`,
Apache 2.0), where the first point is the generic point of the curve and the second its image under
an endomorphism, from the Kähler differential to an arbitrary derivation.
-/

public section

open WeierstrassCurve

namespace WeierstrassCurve.Affine

/-! ### Two formulae, and the coefficient identities

The coefficient identities are between elements of the base field: they are the coefficients of
`D x₁` and `D x₂` in the derivation of the sum's `x`-coordinate, computed by the chain rule from
the addition formulae, compared with the coefficients in `derivation_addX_slope`. -/

section Formula

variable {K : Type*} [CommRing K] (W : WeierstrassCurve.Affine K)

/-- **The difference between a point and its negative is `W_Y`**: `y - negY x y = W_Y(x, y)`. -/
theorem sub_negY (x y : K) : y - W.negY x y = W.polynomialY.evalEval x y := by
  rw [evalEval_polynomialY, negY]
  ring

/-- **`W_Y` does not vanish at a point which is not its own negative.** -/
theorem evalEval_polynomialY_ne_zero_of_Y_ne {x y : K} (hy : y ≠ W.negY x y) :
    W.polynomialY.evalEval x y ≠ 0 :=
  fun h ↦ hy (sub_eq_zero.1 ((W.sub_negY x y).trans h))

end Formula

section coefficients

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

private theorem chord_coeff₁ {x₁ x₂ y₁ y₂ : K} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) (hu₁ : W.polynomialY.evalEval x₁ y₁ ≠ 0) :
    (2 * ((y₁ - y₂) / (x₁ - x₂)) + W.a₁) * ((x₁ - x₂)⁻¹ ^ 2 *
        ((x₁ - x₂) * (-W.polynomialX.evalEval x₁ y₁ / W.polynomialY.evalEval x₁ y₁) -
          (y₁ - y₂))) - 1 =
      W.polynomialY.evalEval (W.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂)))
          (W.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂))) / W.polynomialY.evalEval x₁ y₁ := by
  rw [equation_iff] at h₁ h₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
  rw [evalEval_polynomialY (W.addX _ _ _)]
  simp only [addX, addY, negAddY, negY]
  generalize hu : W.polynomialY.evalEval x₁ y₁ = u at hu₁ ⊢
  generalize hn : y₁ - y₂ = n
  generalize hdd : x₁ - x₂ = d at hd ⊢
  field_simp [hd, hu₁]
  subst hu hn hdd
  rw [evalEval_polynomialX, evalEval_polynomialY]
  linear_combination (-(2 * (y₁ - y₂) + W.a₁ * (x₁ - x₂))) * h₁ +
    (2 * (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * h₂

private theorem chord_coeff₂ {x₁ x₂ y₁ y₂ : K} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) (hu₂ : W.polynomialY.evalEval x₂ y₂ ≠ 0) :
    (2 * ((y₁ - y₂) / (x₁ - x₂)) + W.a₁) * ((x₁ - x₂)⁻¹ ^ 2 *
        ((y₁ - y₂) -
          (x₁ - x₂) * (-W.polynomialX.evalEval x₂ y₂ / W.polynomialY.evalEval x₂ y₂))) - 1 =
      W.polynomialY.evalEval (W.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂)))
          (W.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂))) / W.polynomialY.evalEval x₂ y₂ := by
  rw [equation_iff] at h₁ h₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
  rw [evalEval_polynomialY (W.addX _ _ _)]
  simp only [addX, addY, negAddY, negY]
  generalize hu : W.polynomialY.evalEval x₂ y₂ = u at hu₂ ⊢
  generalize hn : y₁ - y₂ = n
  generalize hdd : x₁ - x₂ = d at hd ⊢
  field_simp [hd, hu₂]
  subst hu hn hdd
  rw [evalEval_polynomialX, evalEval_polynomialY]
  linear_combination (2 * (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * h₁ -
    (2 * (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * h₂

private theorem tangent_coeff {x y N u : K}
    (hN : N = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) (hu : u = 2 * y + W.a₁ * x + W.a₃)
    (hu0 : u ≠ 0) :
    (2 * (N / u) + W.a₁) * (u⁻¹ ^ 2 * (u * ((3 * (x + x) + 2 * W.a₂) - W.a₁ * (N / u)) -
      N * (2 * (N / u) + W.a₁))) - (1 + 1) =
      (2 * W.addY x x y (N / u) + W.a₁ * W.addX x x (N / u) + W.a₃) * (u⁻¹ + u⁻¹) := by
  simp only [addX, addY, negAddY, negY]
  field_simp [hu0]
  subst hN hu
  ring

end coefficients

/-! ### Derivations at the points of a base change -/

section CommRing

variable {R K M : Type*} [CommRing R] [CommRing K] [Algebra R K] [AddCommGroup M] [Module R M]
  [Module K M] {W : WeierstrassCurve R} (D : Derivation R K M)

/-- **The differential of the Weierstrass equation.** At a point `(x, y)` of `W⁄K`, every
derivation `D` on `K` over `R` satisfies `W_X(x, y) • D x + W_Y(x, y) • D y = 0`. -/
theorem Equation.evalEval_polynomialX_smul_add_evalEval_polynomialY_smul_eq_zero {x y : K}
    (h : (W⁄K).toAffine.Equation x y) :
    (W⁄K).toAffine.polynomialX.evalEval x y • D x +
      (W⁄K).toAffine.polynomialY.evalEval x y • D y = 0 := by
  have h0 := congrArg D (((W⁄K).toAffine.equation_iff' x y).1 h)
  have h2 : D (2 : K) = 0 := by simpa using D.map_natCast 2
  have h3 : D (3 : K) = 0 := by simpa using D.map_natCast 3
  rw [evalEval_polynomialX, evalEval_polynomialY]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, sq, pow_three,
    map_zero, map_sub, map_add, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
    add_zero] at h0 ⊢
  linear_combination (norm := module) h0

/-- **The chain rule for `W_X`**: `D (W_X(x, y)) = a₁ • D y - (6x + 2a₂) • D x`. -/
@[simp]
theorem derivation_evalEval_polynomialX (x y : K) :
    D ((W⁄K).toAffine.polynomialX.evalEval x y) =
      (W⁄K).toAffine.a₁ • D y - (6 * x + 2 * (W⁄K).toAffine.a₂) • D x := by
  have h2 : D (2 : K) = 0 := by simpa using D.map_natCast 2
  have h3 : D (3 : K) = 0 := by simpa using D.map_natCast 3
  simp only [evalEval_polynomialX, WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₄, sq, map_sub,
    map_add, Derivation.leibniz, Derivation.map_algebraMap, h2, h3, smul_zero, add_zero]
  module

/-- **The chain rule for `W_Y`**: `D (W_Y(x, y)) = 2 • D y + a₁ • D x`. -/
@[simp]
theorem derivation_evalEval_polynomialY (x y : K) :
    D ((W⁄K).toAffine.polynomialY.evalEval x y) = 2 • D y + (W⁄K).toAffine.a₁ • D x := by
  have h2 : D (2 : K) = 0 := by simpa using D.map_natCast 2
  simp only [evalEval_polynomialY, WeierstrassCurve.baseChange, map_a₁, map_a₃, map_add,
    Derivation.leibniz, Derivation.map_algebraMap, h2, smul_zero, add_zero]
  module

variable (W) in
/-- **The chain rule for `addX`**: `D (addX x₁ x₂ ℓ) = (2ℓ + a₁) • D ℓ - D x₁ - D x₂`. -/
theorem derivation_addX (x₁ x₂ ℓ : K) :
    D ((W⁄K).toAffine.addX x₁ x₂ ℓ) = (2 * ℓ + (W⁄K).toAffine.a₁) • D ℓ - D x₁ - D x₂ := by
  simp only [addX, WeierstrassCurve.baseChange, map_a₁, map_a₂, sq, map_sub, map_add,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  module

end CommRing

section Field

variable {R K M : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module R M]
  [Module K M] {W : WeierstrassCurve R} (D : Derivation R K M)

/-- **The derivation of the `y`-coordinate is determined by that of the `x`-coordinate**: at a
point of `W⁄K` where `W_Y` does not vanish, `D y = (-W_X(x, y) / W_Y(x, y)) • D x`. -/
theorem Equation.derivation_Y_eq_smul_derivation_X {x y : K} (h : (W⁄K).toAffine.Equation x y)
    (hu : (W⁄K).toAffine.polynomialY.evalEval x y ≠ 0) :
    D y = (-(W⁄K).toAffine.polynomialX.evalEval x y / (W⁄K).toAffine.polynomialY.evalEval x y) •
      D x := by
  have e : (W⁄K).toAffine.polynomialY.evalEval x y • D y =
      -((W⁄K).toAffine.polynomialX.evalEval x y • D x) :=
    eq_neg_of_add_eq_zero_right
      (h.evalEval_polynomialX_smul_add_evalEval_polynomialY_smul_eq_zero D)
  rw [neg_div, neg_smul, div_eq_inv_mul, mul_smul, ← smul_neg, ← e, smul_smul, inv_mul_cancel₀ hu,
    one_smul]

/-- **The chain rule for the chord slope**: for `x₁ ≠ x₂`,
`D ℓ = (x₁ - x₂)⁻² • ((x₁ - x₂) • (D y₁ - D y₂) - (y₁ - y₂) • (D x₁ - D x₂))`. -/
theorem derivation_slope_of_X_ne [DecidableEq K] {x₁ x₂ y₁ y₂ : K} (hx : x₁ ≠ x₂) :
    D ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂) =
      (x₁ - x₂)⁻¹ ^ 2 • ((x₁ - x₂) • (D y₁ - D y₂) - (y₁ - y₂) • (D x₁ - D x₂)) := by
  rw [slope_of_X_ne hx, D.leibniz_div, map_sub, map_sub]

/-- **The chain rule for the tangent slope** `-W_X / W_Y` at a point which is not its own
negative. -/
theorem derivation_slope_self_of_Y_ne [DecidableEq K] {x y : K}
    (hy : y ≠ (W⁄K).toAffine.negY x y) :
    D ((W⁄K).toAffine.slope x x y y) =
      ((W⁄K).toAffine.polynomialY.evalEval x y)⁻¹ ^ 2 •
        ((W⁄K).toAffine.polynomialY.evalEval x y • D (-(W⁄K).toAffine.polynomialX.evalEval x y) -
          (-(W⁄K).toAffine.polynomialX.evalEval x y) •
            D ((W⁄K).toAffine.polynomialY.evalEval x y)) := by
  rw [slope_of_Y_ne_eq_evalEval rfl hy, D.leibniz_div]

private theorem derivation_addX_slope_of_X_ne [DecidableEq K] {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W⁄K).toAffine.Equation x₁ y₁) (h₂ : (W⁄K).toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂)
    (hu₁ : (W⁄K).toAffine.polynomialY.evalEval x₁ y₁ ≠ 0)
    (hu₂ : (W⁄K).toAffine.polynomialY.evalEval x₂ y₂ ≠ 0) :
    D ((W⁄K).toAffine.addX x₁ x₂ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂)) =
      (W⁄K).toAffine.polynomialY.evalEval
          ((W⁄K).toAffine.addX x₁ x₂ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂))
          ((W⁄K).toAffine.addY x₁ x₂ y₁ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂)) •
        (((W⁄K).toAffine.polynomialY.evalEval x₁ y₁)⁻¹ • D x₁ +
          ((W⁄K).toAffine.polynomialY.evalEval x₂ y₂)⁻¹ • D x₂) := by
  have c₁ := (W⁄K).toAffine.chord_coeff₁ h₁ h₂ hx hu₁
  have c₂ := (W⁄K).toAffine.chord_coeff₂ h₁ h₂ hx hu₂
  rw [derivation_addX W D, derivation_slope_of_X_ne D hx,
    h₁.derivation_Y_eq_smul_derivation_X D hu₁, h₂.derivation_Y_eq_smul_derivation_X D hu₂,
    slope_of_X_ne hx]
  linear_combination (norm := module) c₁ • D x₁ + c₂ • D x₂

private theorem derivation_addX_slope_of_Y_ne [DecidableEq K] {x y : K}
    (h : (W⁄K).toAffine.Equation x y) (hy : y ≠ (W⁄K).toAffine.negY x y) :
    D ((W⁄K).toAffine.addX x x ((W⁄K).toAffine.slope x x y y)) =
      (W⁄K).toAffine.polynomialY.evalEval ((W⁄K).toAffine.addX x x ((W⁄K).toAffine.slope x x y y))
          ((W⁄K).toAffine.addY x x y ((W⁄K).toAffine.slope x x y y)) •
        (((W⁄K).toAffine.polynomialY.evalEval x y)⁻¹ • D x +
          ((W⁄K).toAffine.polynomialY.evalEval x y)⁻¹ • D x) := by
  have hu := (W⁄K).toAffine.evalEval_polynomialY_ne_zero_of_Y_ne hy
  have c := (W⁄K).toAffine.tangent_coeff (x := x) (y := y)
    (N := -(W⁄K).toAffine.polynomialX.evalEval x y) (u := (W⁄K).toAffine.polynomialY.evalEval x y)
    (by rw [evalEval_polynomialX]; ring) (evalEval_polynomialY x y) hu
  rw [derivation_addX W D, derivation_slope_self_of_Y_ne D hy, map_neg,
    derivation_evalEval_polynomialX, derivation_evalEval_polynomialY,
    h.derivation_Y_eq_smul_derivation_X D hu, slope_of_Y_ne_eq_evalEval rfl hy,
    evalEval_polynomialY ((W⁄K).toAffine.addX _ _ _)]
  linear_combination (norm := module) c • D x

/-- **The derivation of the `x`-coordinate of a sum of points.** Let `(x₁, y₁)` and `(x₂, y₂)` be
points of `W⁄K` whose sum `(x₃, y₃)` is affine, at both of which `W_Y = 2Y + a₁X + a₃` does not
vanish when `x₁ ≠ x₂` (in the tangent case `x₁ = x₂` it cannot vanish). Then every derivation `D`
on `K` over `R` satisfies
`D x₃ = W_Y(x₃, y₃) • (W_Y(x₁, y₁)⁻¹ • D x₁ + W_Y(x₂, y₂)⁻¹ • D x₂)`, the additivity of the
differential `dx / W_Y` with the denominator at the sum cleared. -/
theorem derivation_addX_slope [DecidableEq K] {x₁ x₂ y₁ y₂ : K} (h₁ : (W⁄K).toAffine.Equation x₁ y₁)
    (h₂ : (W⁄K).toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = (W⁄K).toAffine.negY x₂ y₂))
    (hu₁ : x₁ ≠ x₂ → (W⁄K).toAffine.polynomialY.evalEval x₁ y₁ ≠ 0)
    (hu₂ : x₁ ≠ x₂ → (W⁄K).toAffine.polynomialY.evalEval x₂ y₂ ≠ 0) :
    D ((W⁄K).toAffine.addX x₁ x₂ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂)) =
      (W⁄K).toAffine.polynomialY.evalEval
          ((W⁄K).toAffine.addX x₁ x₂ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂))
          ((W⁄K).toAffine.addY x₁ x₂ y₁ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂)) •
        (((W⁄K).toAffine.polynomialY.evalEval x₁ y₁)⁻¹ • D x₁ +
          ((W⁄K).toAffine.polynomialY.evalEval x₂ y₂)⁻¹ • D x₂) := by
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · obtain rfl : y₁ = y₂ := (W⁄K).toAffine.Y_eq_of_Y_ne h₁ h₂ rfl fun hy ↦ hxy ⟨rfl, hy⟩
    exact derivation_addX_slope_of_Y_ne D h₁ fun hy ↦ hxy ⟨rfl, hy⟩
  · exact derivation_addX_slope_of_X_ne D h₁ h₂ hx (hu₁ hx) (hu₂ hx)

/-- **The differential `dx / W_Y` is additive**: under the hypotheses of `derivation_addX_slope`,
if `W_Y` does not vanish at the sum either, then
`W_Y(x₃, y₃)⁻¹ • D x₃ = W_Y(x₁, y₁)⁻¹ • D x₁ + W_Y(x₂, y₂)⁻¹ • D x₂`. -/
theorem inv_smul_derivation_addX_slope [DecidableEq K] {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W⁄K).toAffine.Equation x₁ y₁) (h₂ : (W⁄K).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W⁄K).toAffine.negY x₂ y₂))
    (hu₁ : x₁ ≠ x₂ → (W⁄K).toAffine.polynomialY.evalEval x₁ y₁ ≠ 0)
    (hu₂ : x₁ ≠ x₂ → (W⁄K).toAffine.polynomialY.evalEval x₂ y₂ ≠ 0)
    (hu₃ : (W⁄K).toAffine.polynomialY.evalEval
      ((W⁄K).toAffine.addX x₁ x₂ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂))
      ((W⁄K).toAffine.addY x₁ x₂ y₁ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂)) ≠ 0) :
    ((W⁄K).toAffine.polynomialY.evalEval
        ((W⁄K).toAffine.addX x₁ x₂ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂))
        ((W⁄K).toAffine.addY x₁ x₂ y₁ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂)))⁻¹ •
      D ((W⁄K).toAffine.addX x₁ x₂ ((W⁄K).toAffine.slope x₁ x₂ y₁ y₂)) =
      ((W⁄K).toAffine.polynomialY.evalEval x₁ y₁)⁻¹ • D x₁ +
        ((W⁄K).toAffine.polynomialY.evalEval x₂ y₂)⁻¹ • D x₂ := by
  rw [derivation_addX_slope D h₁ h₂ hxy hu₁ hu₂, smul_smul, inv_mul_cancel₀ hu₃, one_smul]

end Field

end WeierstrassCurve.Affine

end
