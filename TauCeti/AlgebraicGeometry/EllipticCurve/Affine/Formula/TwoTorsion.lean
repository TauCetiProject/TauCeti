/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.Derivation

/-!
# Points of order two on the Weierstrass equation

Let `W` be a Weierstrass curve over a field `F`, and let `T = (e, t)` be a solution of the
Weierstrass equation at which `ψ₂(e, t) = 2t + a₁e + a₃` vanishes, so that `T` is its own negative.
Write

`c_T = -W_X(e, t) = 3e² + 2a₂e + a₄ - a₁t`

for the value at `T` of minus the partial derivative of the Weierstrass polynomial in `X`. It is
nonzero when `T` is nonsingular, since the other partial derivative `ψ₂(e, t)` vanishes; when the
equation is `y² = (x - e)(x - e')(x - e'')`, it is `(e - e')(e - e'')`.

This file records the facts about such solutions that do not involve the group law, valid in every
characteristic: `(e, t)` is the only solution over `e`, and two of them `T = (e, t)` and
`T₀ = (e₀, t₀)` with `e₀ ≠ e` have `c_T + c_{T₀} = (e - e₀)²`. The formulas for translation by a
point of order two are in `TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion`.

## Main results

* `WeierstrassCurve.Affine.evalEval_polynomialY_eq_zero_iff`: `ψ₂(x, y) = 0` exactly when
  `y = negY x y`.
* `WeierstrassCurve.Affine.Y_eq_of_evalEval_polynomialY_eq_zero`: if `ψ₂(e, t) = 0`, the only
  solution over `e` is `(e, t)`.
* `WeierstrassCurve.Affine.evalEval_polynomialX_add_evalEval_polynomialX`: for two distinct
  points of order two, `c_T + c_{T₀} = (e - e₀)²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.4.
-/

public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {e t x y : F}

/-- **`ψ₂` vanishes exactly at the points that are their own negatives**:
`ψ₂(x, y) = 0 ↔ y = negY x y`. -/
theorem evalEval_polynomialY_eq_zero_iff : W.polynomialY.evalEval x y = 0 ↔ y = W.negY x y := by
  rw [← W.sub_negY, sub_eq_zero]

/-- **The only point over a point of order two is itself**: if `ψ₂(e, t) = 0` and `(e, t₀)` lies
on the curve, then `t₀ = t`. -/
theorem Y_eq_of_evalEval_polynomialY_eq_zero (hT : W.Equation e t)
    (hψ : W.polynomialY.evalEval e t = 0) {t₀ : F} (hT₀ : W.Equation e t₀) : t₀ = t := by
  rcases Y_eq_of_X_eq hT₀ hT rfl with h | h
  · exact h
  · rwa [← evalEval_polynomialY_eq_zero_iff.1 hψ] at h

/-- **A point with `ψ₂ ≠ 0` does not lie over a point of order two**: if `ψ₂(e, t) = 0` and
`ψ₂(x, y) ≠ 0`, then `x ≠ e`, since the only point over `e` is `(e, t)`. -/
theorem X_ne_of_evalEval_polynomialY_ne_zero (hT : W.Equation e t)
    (hψ : W.polynomialY.evalEval e t = 0) (h : W.Equation x y)
    (hy : W.polynomialY.evalEval x y ≠ 0) : x ≠ e := by
  rintro rfl
  obtain rfl := Y_eq_of_evalEval_polynomialY_eq_zero hT hψ h
  exact hy hψ

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

end WeierstrassCurve.Affine
