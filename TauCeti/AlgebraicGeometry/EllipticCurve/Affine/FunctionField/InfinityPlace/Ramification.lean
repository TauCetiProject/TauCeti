/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic

/-!
# The place at infinity of `F(W)` over `F(x)`

For a Weierstrass curve `W` over a field `F`, the place at infinity of the function field `F(W)`
lies over the place at infinity of the rational function field `F(x)`, with ramification index
`2`: the valuation at infinity of a rational function of `x` is `exp` of twice its degree.

## Main results

* `TauCeti.Place.restrict_infinity`: the place at infinity of `F(W)` restricts to `∞` on `F(x)`.
* `TauCeti.Place.ramificationIdx_infinity`: its ramification index over `F(x)` is `2`.
-/

public section

open Polynomial WeierstrassCurve

open scoped RatFunc

namespace TauCeti.Place

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **The place at infinity of `F(W)` lies over the place at infinity of `F(x)`.** -/
@[simp]
theorem restrict_infinity : (infinity W).restrict F (RatFunc F) = infty F := by
  rw [restrict_eq_iff_exists_ord_eq]
  refine ⟨2, two_pos, fun r ↦ ?_⟩
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [ord_def, valuation_infinity, Affine.infinityPlace_algebraMap_ratFunc W hr, ord_infty,
      WithZero.log_exp]
    push_cast
    ring

/-- **The place at infinity of `F(W)` has ramification index `2` over `F(x)`.** -/
@[simp]
theorem ramificationIdx_infinity : ramificationIdx (RatFunc F) (infinity W) = 2 := by
  refine ramificationIdx_eq_of_forall_ord_eq F (RatFunc F) (infinity W) fun r ↦ ?_
  rw [restrict_infinity]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [ord_def, valuation_infinity, Affine.infinityPlace_algebraMap_ratFunc W hr, ord_infty,
      WithZero.log_exp]
    push_cast
    ring

end TauCeti.Place
