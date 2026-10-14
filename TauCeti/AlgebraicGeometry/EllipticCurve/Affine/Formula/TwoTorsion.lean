/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.Derivation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Translation by a point of order two, and the `x`-coordinate of a double

Let `W` be a Weierstrass curve over a field `F`, and let `T = (e, t)` be an affine point of order
two, so that `ψ₂(e, t) = 2t + a₁e + a₃` vanishes. Write

`c_T = -W_X(e, t) = 3e² + 2a₂e + a₄ - a₁t`

for the value at `T` of minus the partial derivative of the Weierstrass polynomial in `X`. It is
nonzero, since `T` is nonsingular and the other partial derivative `ψ₂(e, t)` vanishes; when the
equation is `y² = (x - e)(x - e')(x - e'')`, it is `(e - e')(e - e'')`.

An affine point `(x, y)` has order two exactly when `ψ₂(x, y) = 0`, and the points `S` with
`2S = O` (the `2`-torsion) are `O`, `T` and the points `(e₀, t₀)` with `ψ₂(e₀, t₀) = 0` and
`e₀ ≠ e`. This file records these facts and the formulas in which `c_T` appears, valid in every
characteristic.

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

* `WeierstrassCurve.Affine.some_add_self_eq_zero_iff`: `(x, y)` has order two exactly when
  `ψ₂(x, y) = 0`.
* `WeierstrassCurve.Affine.eq_zero_or_eq_or_exists_of_add_self_eq_zero`: a point `S` with
  `2S = O` is `O`, `T`, or a point of order two over another root.
* `WeierstrassCurve.Affine.evalEval_polynomialX_add_evalEval_polynomialX`: for two distinct points
  of order two, `c_T + c_{T₀} = (e - e₀)²`.
* `WeierstrassCurve.Affine.xCoord_add_sub_mul_sub`: `(x(P + T) - e)(x - e) = c_T`.
* `WeierstrassCurve.Affine.evalEval_polynomialY_add_mul_sub`:
  `ψ₂(P + T)(x - e) = -ψ₂(P)(x(P + T) - e)`.
* `WeierstrassCurve.Affine.xCoord_add_self_sub_mul_sq`:
  `(x(2P) - e) ψ₂(P)² = ((x - e)² - c_T)²`.
* `WeierstrassCurve.Affine.sq_xCoord_add_sub_add_evalEval_polynomialX_div`: the square root
  `((x - e)² - c_T) / ψ₂` of `x(2P) - e` is fixed by translation by `O` and `T`, and changes sign
  under translation by the other two points of order two.
* `WeierstrassCurve.Affine.xCoord_add_sub`: when `(x - e)² = c_T`, translation by a point of order
  two sends `x - e` to `±(x - e)`, with the same signs.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3 and X.1.4.
-/

public section

namespace WeierstrassCurve.Affine

open Point

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {e t x y : F}

omit [DecidableEq F] in
/-- **`ψ₂` vanishes exactly at the points that are their own negatives**:
`ψ₂(x, y) = 0 ↔ y = negY x y`. -/
theorem evalEval_polynomialY_eq_zero_iff : W.polynomialY.evalEval x y = 0 ↔ y = W.negY x y := by
  rw [← W.sub_negY, sub_eq_zero]

/-- **An affine point has order two exactly when `ψ₂` vanishes there.** -/
theorem some_add_self_eq_zero_iff (h : W.Nonsingular x y) :
    some x y h + some x y h = 0 ↔ W.polynomialY.evalEval x y = 0 := by
  refine ⟨fun hS ↦ by_contra fun hy ↦ ?_, fun hy ↦
    add_self_of_Y_eq (evalEval_polynomialY_eq_zero_iff.1 hy)⟩
  rw [add_self_of_Y_ne (mt evalEval_polynomialY_eq_zero_iff.2 hy)] at hS
  exact some_ne_zero _ hS

omit [DecidableEq F] in
/-- **The only point over a point of order two is itself**: if `ψ₂(e, t) = 0` and `(e, t₀)` lies
on the curve, then `t₀ = t`. -/
theorem Y_eq_of_evalEval_polynomialY_eq_zero (hT : W.Equation e t)
    (hψ : W.polynomialY.evalEval e t = 0) {t₀ : F} (hT₀ : W.Equation e t₀) : t₀ = t := by
  rcases Y_eq_of_X_eq hT₀ hT rfl with h | h
  · exact h
  · rwa [← evalEval_polynomialY_eq_zero_iff.1 hψ] at h

omit [DecidableEq F] in
/-- **A point with `ψ₂ ≠ 0` does not lie over a point of order two**: if `ψ₂(e, t) = 0` and
`ψ₂(x, y) ≠ 0`, then `x ≠ e`, since the only point over `e` is `(e, t)`. -/
theorem X_ne_of_evalEval_polynomialY_ne_zero (hT : W.Equation e t)
    (hψ : W.polynomialY.evalEval e t = 0) (h : W.Equation x y)
    (hy : W.polynomialY.evalEval x y ≠ 0) : x ≠ e := by
  rintro rfl
  obtain rfl := Y_eq_of_evalEval_polynomialY_eq_zero hT hψ h
  exact hy hψ

/-- **The points of order two, seen from one of them**: if `T = (e, t)` has `ψ₂(e, t) = 0`, a point
`S` with `2S = O` is `O`, `T`, or a point `(e₀, t₀)` with `ψ₂(e₀, t₀) = 0` and `e₀ ≠ e`. -/
theorem eq_zero_or_eq_or_exists_of_add_self_eq_zero (hT : W.Nonsingular e t)
    (hψ : W.polynomialY.evalEval e t = 0) {S : W.Point} (hS : S + S = 0) :
    S = 0 ∨ S = some e t hT ∨ ∃ (e₀ t₀ : F) (hT₀ : W.Nonsingular e₀ t₀),
      W.polynomialY.evalEval e₀ t₀ = 0 ∧ e₀ ≠ e ∧ S = some e₀ t₀ hT₀ := by
  rcases S with _ | ⟨e₀, t₀, hT₀⟩
  · exact Or.inl rfl
  have hψ₀ := (some_add_self_eq_zero_iff hT₀).1 hS
  by_cases he : e₀ = e
  · subst he
    obtain rfl := Y_eq_of_evalEval_polynomialY_eq_zero hT.1 hψ hT₀.1
    exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨e₀, t₀, hT₀, hψ₀, he, rfl⟩)

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
  have hne : y ≠ W.negY x y := mt evalEval_polynomialY_eq_zero_iff.2 hy
  have h₁ := (equation_iff ..).1 h.1
  have h₂ := (equation_iff ..).1 hT
  rw [evalEval_polynomialY] at hψ hy
  rw [add_self_of_Y_ne hne, xCoord_some, slope_of_Y_ne rfl hne, sub_negY, evalEval_polynomialY,
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

/-- **Translating a point with `ψ₂ ≠ 0` by a point of order two keeps `ψ₂ ≠ 0`.** -/
theorem evalEval_polynomialY_add_ne_zero (h : W.Nonsingular x y)
    (hy : W.polynomialY.evalEval x y ≠ 0) {S : W.Point} (hS : S + S = 0) :
    W.polynomialY.evalEval (some x y h + S).xCoord (some x y h + S).yCoord ≠ 0 := by
  rcases S with _ | ⟨e₀, t₀, hT₀⟩
  · rwa [← zero_def, add_zero, xCoord_some, yCoord_some]
  have hψ₀ := (some_add_self_eq_zero_iff hT₀).1 hS
  have hx := X_ne_of_evalEval_polynomialY_ne_zero hT₀.1 hψ₀ h.1 hy
  have hA := xCoord_add_sub_mul_sub hT₀ hψ₀ h hx
  have hB := evalEval_polynomialY_add_mul_sub hT₀ hψ₀ h hx
  have hc : W.polynomialX.evalEval e₀ t₀ ≠ 0 := hT₀.2.resolve_right (not_not.2 hψ₀)
  intro h0
  rw [h0, zero_mul, neg_mul, zero_eq_neg, mul_eq_zero] at hB
  refine hB.elim hy fun hx' ↦ hc ?_
  rw [hx', zero_mul, zero_eq_neg] at hA
  exact hA

/-- **The square root of `x(2P) - e` under translation by `E[2]`**: if `T = (e, t)` has
`ψ₂(e, t) = 0`, `P = (x, y)` has `ψ₂(x, y) ≠ 0` and `2S = O`, then `r(P + S) = ±r(P)` for
`r = ((x - e)² + W_X(e, t)) / ψ₂`, with the sign `+` exactly when `S ∈ {O, T}`. -/
theorem sq_xCoord_add_sub_add_evalEval_polynomialX_div (hT : W.Nonsingular e t)
    (hψ : W.polynomialY.evalEval e t = 0) (h : W.Nonsingular x y)
    (hy : W.polynomialY.evalEval x y ≠ 0) {S : W.Point} (hS : S + S = 0) :
    (((some x y h + S).xCoord - e) ^ 2 + W.polynomialX.evalEval e t) /
        W.polynomialY.evalEval (some x y h + S).xCoord (some x y h + S).yCoord =
      (if S = 0 ∨ S = some e t hT then 1 else -1) *
        (((x - e) ^ 2 + W.polynomialX.evalEval e t) / W.polynomialY.evalEval x y) := by
  have hy' := evalEval_polynomialY_add_ne_zero h hy hS
  rcases eq_zero_or_eq_or_exists_of_add_self_eq_zero hT hψ hS with
    rfl | rfl | ⟨e₀, t₀, hT₀, hψ₀, he, rfl⟩
  · simp
  · rw [ite_eq_left (Or.inr rfl), one_mul, div_eq_div_iff hy' hy]
    have hx := X_ne_of_evalEval_polynomialY_ne_zero hT.1 hψ h.1 hy
    have hA := xCoord_add_sub_mul_sub hT hψ h hx
    have hB := evalEval_polynomialY_add_mul_sub hT hψ h hx
    set x' := (some x y h + some e t hT).xCoord
    set ψ := W.polynomialY.evalEval x y
    set c := W.polynomialX.evalEval e t
    apply mul_left_cancel₀ (sub_ne_zero.2 hx)
    linear_combination -((x - e) ^ 2 + c) * hB + ψ * ((x - e) + (x' - e)) * hA
  · rw [ite_eq_right (by simp [he]), neg_one_mul, ← neg_div, div_eq_div_iff hy' hy]
    have hx := X_ne_of_evalEval_polynomialY_ne_zero hT₀.1 hψ₀ h.1 hy
    have hA := xCoord_add_sub_mul_sub hT₀ hψ₀ h hx
    have hB := evalEval_polynomialY_add_mul_sub hT₀ hψ₀ h hx
    have hC := evalEval_polynomialX_add_evalEval_polynomialX hT.1 hψ hT₀.1 hψ₀ he
    set x' := (some x y h + some e₀ t₀ hT₀).xCoord
    set ψ := W.polynomialY.evalEval x y
    set c := W.polynomialX.evalEval e t
    apply mul_left_cancel₀ (sub_ne_zero.2 hx)
    linear_combination ((x - e) ^ 2 + c) * hB + ψ * ((x - e₀) - (x' - e₀)) * hC -
      ψ * ((x - e₀) - (x' - e₀)) * hA

/-- **The square root of `c_T` under translation by `E[2]`**: if `T = (e, t)` has `ψ₂(e, t) = 0`,
`P = (x, y)` has `ψ₂(x, y) ≠ 0` and `(x - e)² = c_T`, as when `2P = T`, and `2S = O`, then
`x(P + S) - e = ±(x - e)`, with the sign `+` exactly when `S ∈ {O, T}`. -/
theorem xCoord_add_sub (hT : W.Nonsingular e t) (hψ : W.polynomialY.evalEval e t = 0)
    (h : W.Nonsingular x y) (hy : W.polynomialY.evalEval x y ≠ 0)
    (hx2 : (x - e) ^ 2 + W.polynomialX.evalEval e t = 0) {S : W.Point} (hS : S + S = 0) :
    (some x y h + S).xCoord - e = (if S = 0 ∨ S = some e t hT then 1 else -1) * (x - e) := by
  rcases eq_zero_or_eq_or_exists_of_add_self_eq_zero hT hψ hS with
    rfl | rfl | ⟨e₀, t₀, hT₀, hψ₀, he, rfl⟩
  · simp
  · rw [ite_eq_left (Or.inr rfl), one_mul]
    have hx := X_ne_of_evalEval_polynomialY_ne_zero hT.1 hψ h.1 hy
    have hA := xCoord_add_sub_mul_sub hT hψ h hx
    apply mul_right_cancel₀ (sub_ne_zero.2 hx)
    linear_combination hA - hx2
  · rw [ite_eq_right (by simp [he]), neg_one_mul]
    have hx := X_ne_of_evalEval_polynomialY_ne_zero hT₀.1 hψ₀ h.1 hy
    have hA := xCoord_add_sub_mul_sub hT₀ hψ₀ h hx
    have hC := evalEval_polynomialX_add_evalEval_polynomialX hT.1 hψ hT₀.1 hψ₀ he
    apply mul_right_cancel₀ (sub_ne_zero.2 hx)
    linear_combination hA - hC + hx2

end WeierstrassCurve.Affine
