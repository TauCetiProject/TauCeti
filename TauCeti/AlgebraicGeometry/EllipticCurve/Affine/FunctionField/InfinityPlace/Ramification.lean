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
`2`: the order at infinity of a rational function of `x` is twice its order at infinity in
`F(x)`. When the coordinate ring of `W` is a Dedekind domain, for instance when `W` is an elliptic
curve, it is the only place of `F(W)` over that place.

## Main results

* `TauCeti.Place.ord_infinity_algebraMap`: the order at infinity of a rational function of `x` is
  twice its order at `∞`.
* `TauCeti.Place.restrict_infinity`: the place at infinity of `F(W)` restricts to `∞` on `F(x)`.
* `TauCeti.Place.ramificationIdx_infinity`: its ramification index over `F(x)` is `2`.
* `TauCeti.Place.restrict_eq_infty_iff`: for a Dedekind coordinate ring, it is the only place of
  `F(W)` over `∞`.
-/

public section

open Polynomial WeierstrassCurve

open scoped RatFunc

namespace TauCeti.Place

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **The order at infinity of a rational function of `x`** is twice its order at the place at
infinity of `F(x)`. -/
@[simp]
theorem ord_infinity_algebraMap (r : RatFunc F) :
    (infinity W).ord (algebraMap (RatFunc F) W.FunctionField r) = 2 * (infty F).ord r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [ord_def, valuation_infinity, Affine.infinityPlace_algebraMap_ratFunc W hr, ord_infty,
      WithZero.log_exp]
    ring

/-- **The place at infinity of `F(W)` lies over the place at infinity of `F(x)`.** -/
@[simp]
theorem restrict_infinity : (infinity W).restrict F (RatFunc F) = infty F :=
  (restrict_eq_iff_exists_ord_eq (P' := infinity W) (P := infty F) F (RatFunc F)).mpr
    ⟨2, two_pos, fun r ↦ by rw [ord_infinity_algebraMap]; norm_num⟩

/-- **The place at infinity of `F(W)` has ramification index `2` over `F(x)`.** -/
@[simp]
theorem ramificationIdx_infinity : ramificationIdx (RatFunc F) (infinity W) = 2 :=
  ramificationIdx_eq_of_forall_ord_eq F (RatFunc F) (infinity W) fun r ↦ by
    rw [restrict_infinity, ord_infinity_algebraMap]
    norm_num

/-- **The place at infinity is the only place of `F(W)` over the place at infinity of `F(x)`**:
every other place comes from a height-one prime of the coordinate ring, so `x` is regular there,
while `x` has a pole at `∞`. -/
@[simp]
theorem restrict_eq_infty_iff [IsDedekindDomain W.CoordinateRing] (Q : Place F W.FunctionField) :
    Q.restrict F (RatFunc F) = infty F ↔ Q = infinity W := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ restrict_infinity W⟩
  rcases eq_infinity_or_existsUnique_eq_ofPrime Q with hQ | ⟨𝔭, h𝔭, -⟩
  · exact hQ
  · exfalso
    have hx : Q.valuation (algebraMap F[X] W.FunctionField X) ≤ 1 :=
      (exists_eq_ofPrime_iff_valuation_X_le_one Q).mp ⟨𝔭, h𝔭⟩
    have hmem : (RatFunc.X : RatFunc F) ∈ (Q.restrict F (RatFunc F)).integers := by
      rw [mem_integers_restrict_iff, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply]
      exact Q.mem_integers_iff.mpr hx
    rw [h, mem_integers_iff_ord_nonneg, ord_infty, RatFunc.intDegree_X] at hmem
    omega

end TauCeti.Place
