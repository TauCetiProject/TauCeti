/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Translation by a point of order two, and the `x`-coordinate of a double

Let `W` be a Weierstrass curve over a field `F`, and let `T = (e, t)` be an affine point of order
two, so that `ψ₂(e, t) = 2t + a₁e + a₃` vanishes. Write

`c_T = -W_X(e, t) = 3e² + 2a₂e + a₄ - a₁t`

for the value at `T` of minus the partial derivative of the Weierstrass polynomial in `X`. It is
nonzero, since `T` is nonsingular and the other partial derivative `ψ₂(e, t)` vanishes; when the
equation is `y² = (x - e)(x - e')(x - e'')`, it is `(e - e')(e - e'')`.

This file records the formulas in which `c_T` appears, valid in every characteristic.

* Translation by `T` inverts `x - e` up to `c_T`: for an affine point `P = (x, y)` with `x ≠ e`,
  `(x(P + T) - e)(x - e) = c_T`, and `ψ₂(P + T)(x - e) = -ψ₂(P)(x(P + T) - e)`.
* The `x`-coordinate of a double is `e` plus a square: for `P = (x, y)` with `ψ₂(x, y) ≠ 0`,
  `(x(2P) - e) ψ₂(x, y)² = ((x - e)² - c_T)²`.
* Two distinct points `T = (e, t)` and `T₀ = (e₀, t₀)` of order two have
  `c_T + c_{T₀} = (e - e₀)²`.

The second formula says that `x - e`, as a function on the curve, becomes a square after pulling
back along multiplication by `2`, with square root `((x - e)² - c_T) / ψ₂`; the first says how that
root transforms under translation by the points of order two. Together they compute the Kummer map
of multiplication by `2` (Silverman X.1.4).

## Main results

* `WeierstrassCurve.Affine.evalEval_polynomialX_add_evalEval_polynomialX`: for two distinct points
  of order two, `c_T + c_{T₀} = (e - e₀)²`.
* `WeierstrassCurve.Affine.xCoord_add_sub_mul_sub`: `(x(P + T) - e)(x - e) = c_T`.
* `WeierstrassCurve.Affine.evalEval_polynomialY_add_mul_sub`:
  `ψ₂(P + T)(x - e) = -ψ₂(P)(x(P + T) - e)`.
* `WeierstrassCurve.Affine.xCoord_add_self_sub_mul_sq`:
  `(x(2P) - e) ψ₂(P)² = ((x - e)² - c_T)²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3 and X.1.4.
-/

public section

namespace WeierstrassCurve.Affine

open Point

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {e t x y : F}

omit [DecidableEq F] in
/-- **A point with `ψ₂ ≠ 0` does not lie over a point of order two**: if `ψ₂(e, t) = 0` and
`ψ₂(x, y) ≠ 0`, then `x ≠ e`, since the only points over `e` are `(e, t)` and `-(e, t) = (e, t)`. -/
theorem X_ne_of_evalEval_polynomialY_ne_zero (hT : W.Equation e t)
    (hψ : W.polynomialY.evalEval e t = 0) (h : W.Equation x y)
    (hy : W.polynomialY.evalEval x y ≠ 0) : x ≠ e := by
  rintro rfl
  have ht : t = W.negY x t := by
    rw [evalEval_polynomialY] at hψ
    rw [negY]
    linear_combination hψ
  rcases Y_eq_of_X_eq h hT rfl with rfl | rfl
  · exact hy hψ
  · rw [← ht] at hy
    exact hy hψ

omit [DecidableEq F] in
/-- **Two distinct points of order two**: if `(e, t)` and `(e₀, t₀)` both have `ψ₂ = 0` and
`e₀ ≠ e`, then `W_X(e, t) + W_X(e₀, t₀) = -(e - e₀)²`, that is `c_T + c_{T₀} = (e - e₀)²`. When the
equation is `y² = (x - e)(x - e₀)(x - e'')`, this is
`(e - e₀)(e - e'') + (e₀ - e)(e₀ - e'') = (e - e₀)²`. -/
theorem evalEval_polynomialX_add_evalEval_polynomialX {e₀ t₀ : F} (hT : W.Equation e t)
    (hψ : W.polynomialY.evalEval e t = 0) (hT₀ : W.Equation e₀ t₀)
    (hψ₀ : W.polynomialY.evalEval e₀ t₀ = 0) (he : e₀ ≠ e) :
    W.polynomialX.evalEval e t + W.polynomialX.evalEval e₀ t₀ = -(e - e₀) ^ 2 := by
  rw [equation_iff] at hT hT₀
  rw [evalEval_polynomialY] at hψ hψ₀
  rw [evalEval_polynomialX, evalEval_polynomialX]
  apply mul_left_cancel₀ (sub_ne_zero.2 he)
  linear_combination 2 * hT₀ - 2 * hT - (t₀ - t) * hψ - (t₀ - t) * hψ₀

/-- **Translating by a point of order two inverts `x - e` up to `c_T`**: if `T = (e, t)` has
`ψ₂(e, t) = 0` and `P = (x, y)` has `x ≠ e`, then `(x(P + T) - e)(x - e) = -W_X(e, t)`. -/
theorem xCoord_add_sub_mul_sub (hT : W.Nonsingular e t) (hψ : W.polynomialY.evalEval e t = 0)
    (h : W.Nonsingular x y) (hx : x ≠ e) :
    ((some x y h + some e t hT).xCoord - e) * (x - e) = -W.polynomialX.evalEval e t := by
  have key : (y - t) / (x - e) * (x - e) = y - t := div_mul_cancel₀ _ (sub_ne_zero.2 hx)
  have h₁ := (equation_iff ..).1 h.1
  have h₂ := (equation_iff ..).1 hT.1
  rw [evalEval_polynomialY] at hψ
  rw [add_of_X_ne hx, xCoord_some, slope_of_X_ne hx, evalEval_polynomialX]
  set ℓ := (y - t) / (x - e)
  apply mul_left_cancel₀ (sub_ne_zero.2 hx)
  simp only [addX]
  linear_combination h₁ - h₂ + (ℓ * (x - e) + (y - t) + W.a₁ * (x - e)) * key - (y - t) * hψ

/-- **`ψ₂` under translation by a point of order two**: if `T = (e, t)` has `ψ₂(e, t) = 0` and
`P = (x, y)` has `x ≠ e`, then `ψ₂(P + T)(x - e) = -ψ₂(P)(x(P + T) - e)`. -/
theorem evalEval_polynomialY_add_mul_sub (hT : W.Nonsingular e t)
    (hψ : W.polynomialY.evalEval e t = 0) (h : W.Nonsingular x y) (hx : x ≠ e) :
    W.polynomialY.evalEval (some x y h + some e t hT).xCoord (some x y h + some e t hT).yCoord *
        (x - e) =
      -W.polynomialY.evalEval x y * ((some x y h + some e t hT).xCoord - e) := by
  have key : (y - t) / (x - e) * (x - e) = y - t := div_mul_cancel₀ _ (sub_ne_zero.2 hx)
  rw [evalEval_polynomialY] at hψ
  rw [add_of_X_ne hx, xCoord_some, yCoord_some, slope_of_X_ne hx, evalEval_polynomialY,
    evalEval_polynomialY]
  set ℓ := (y - t) / (x - e)
  simp only [addY, addX, negAddY, negY]
  linear_combination (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x - e - x) * hψ -
    2 * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x - e - x) * key

/-- **The `x`-coordinate of a double is `e` plus a square**: if `T = (e, t)` has `ψ₂(e, t) = 0` and
`P = (x, y)` has `ψ₂(x, y) ≠ 0`, then `(x(2P) - e) ψ₂(x, y)² = ((x - e)² + W_X(e, t))²`. -/
theorem xCoord_add_self_sub_mul_sq (hT : W.Equation e t) (hψ : W.polynomialY.evalEval e t = 0)
    (h : W.Nonsingular x y) (hy : W.polynomialY.evalEval x y ≠ 0) :
    ((some x y h + some x y h).xCoord - e) * W.polynomialY.evalEval x y ^ 2 =
      ((x - e) ^ 2 + W.polynomialX.evalEval e t) ^ 2 := by
  have hne : y ≠ W.negY x y := fun hy' ↦ hy <| by
    rw [negY] at hy'
    rw [evalEval_polynomialY]
    linear_combination hy'
  have hψxy : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by rw [negY]; ring
  have h₁ := (equation_iff ..).1 h.1
  have h₂ := (equation_iff ..).1 hT
  rw [evalEval_polynomialY] at hψ hy
  rw [add_self_of_Y_ne hne, xCoord_some, slope_of_Y_ne rfl hne, hψxy, evalEval_polynomialY,
    evalEval_polynomialX]
  have key : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃) *
      (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y :=
    div_mul_cancel₀ _ hy
  set ℓ := (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)
  set ψ := 2 * y + W.a₁ * x + W.a₃
  set N := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  simp only [addX]
  linear_combination (ℓ * ψ + N + W.a₁ * ψ) * key -
    (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x + 4 * e) * h₁ + (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x + 4 * e) * h₂ +
    (-(2 * x + e + W.a₂) * (2 * t + W.a₁ * e + W.a₃) -
      W.a₁ * ((x - e) ^ 2 - (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄ - W.a₁ * t))) * hψ

end WeierstrassCurve.Affine
