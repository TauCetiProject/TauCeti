/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Weierstrass curves with a marked point

A pointed Weierstrass curve over a commutative ring `R` is a Weierstrass curve `W` together with an
element of its point group `W⟮R⟯`, a nonsingular affine point or the point at infinity
(`TauCeti.PointedWeierstrassCurve`). Changes of variables act on pointed curves: `C` sends
`(W, P)` to `(C • W, Q)`, where `Q` is the point of `C • W` that the change of variables
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` carries to `P`. Two pointed curves are isomorphic, in the
sense that an isomorphism of Weierstrass curves carries one marked point to the other, exactly when
they lie in the same orbit, so the orbits are the isomorphism classes of pointed curves.

Changes of variables preserve ellipticity over any commutative ring
(`WeierstrassCurve.isElliptic_smul_iff`). Over a field the bijection of point groups is a group
isomorphism, so they also preserve the order of the marked point. The pointed elliptic curves whose
marked point has exact order `N` therefore form a sub-action
(`TauCeti.PointedWeierstrassCurve.exactOrder`); its orbits are the isomorphism classes of elliptic
curves with a point of exact order `N`, the moduli problem of the congruence subgroup `Γ₁(N)`.

## Main definitions

* `TauCeti.PointedWeierstrassCurve R`: a Weierstrass curve over `R` with a marked point.
* `TauCeti.PointedWeierstrassCurve.instMulActionVariableChange`: the action of changes of variables.
* `TauCeti.PointedWeierstrassCurve.exactOrder F N`: over a field `F`, the elliptic curves with a
  marked point of exact order `N`, as a sub-action.

## Main results

* `TauCeti.PointedWeierstrassCurve.equivVariableChange_smul_point`: the change of variables `C`
  carries the marked point of `C • X` to that of `X`.
* `TauCeti.PointedWeierstrassCurve.smul_mk_some_eq_mk_some_iff`: a change of variables between
  affine pointed curves, in coordinates.
* `TauCeti.PointedWeierstrassCurve.addOrderOf_smul_point`: over a field, changes of variables
  preserve the order of the marked point.
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine.Point

/-- A **pointed Weierstrass curve** over `R`: a Weierstrass curve together with a point of its
point group, that is, a nonsingular affine point or the point at infinity. -/
structure PointedWeierstrassCurve (R : Type*) [CommRing R] where
  /-- The underlying Weierstrass curve. -/
  curve : WeierstrassCurve R
  /-- The marked point. -/
  point : curve.toAffine.Point

namespace PointedWeierstrassCurve

variable {R : Type*} [CommRing R]

/-- Two pointed curves are equal when their curves are equal and the transport of the first
marked point along this equality is the second marked point. -/
theorem ext_cast {X Y : PointedWeierstrassCurve R} (h : X.curve = Y.curve)
    (hP : cast (congrArg (fun V : WeierstrassCurve R ↦ V.toAffine.Point) h) X.point = Y.point) :
    X = Y := by
  obtain ⟨W, P⟩ := X
  obtain ⟨W', P'⟩ := Y
  dsimp only at h hP
  subst h
  simp_all

/-- Pointed curves with the same underlying curve are equal exactly when their marked points are.
This is `PointedWeierstrassCurve.mk.injEq` without the heterogeneous equality. -/
theorem mk_inj {W : WeierstrassCurve R} {P Q : W.toAffine.Point} :
    (⟨W, P⟩ : PointedWeierstrassCurve R) = ⟨W, Q⟩ ↔ P = Q := by
  simp

/-- A pointed curve whose curve is `W` has the form `(W, P)`. -/
theorem exists_eq_mk {X : PointedWeierstrassCurve R} {W : WeierstrassCurve R}
    (h : X.curve = W) : ∃ P : W.toAffine.Point, X = ⟨W, P⟩ := by
  cases X
  subst h
  exact ⟨_, rfl⟩

/-- Changes of variables act on pointed curves: `C` sends `(W, P)` to `(C • W, Q)`, where `Q`
is the point of `C • W` that `(x, y) ↦ (u²x + r, u³y + u²sx + t)` carries to `P`. -/
instance instSMulVariableChange : SMul (VariableChange R) (PointedWeierstrassCurve R) where
  smul C X := ⟨C • X.curve, (equivVariableChange X.curve C).symm X.point⟩

variable (C : VariableChange R) (X : PointedWeierstrassCurve R)

@[simp]
theorem smul_curve : (C • X).curve = C • X.curve := rfl

theorem smul_point : (C • X).point = (equivVariableChange X.curve C).symm X.point := rfl

/-- The change of variables `C` carries the marked point of `C • X` to that of `X`. -/
@[simp]
theorem equivVariableChange_smul_point : equivVariableChange X.curve C (C • X).point = X.point :=
  Equiv.apply_symm_apply _ _

/-- The marked point of `C • X` is the point at infinity exactly when that of `X` is. -/
@[simp]
theorem smul_point_eq_zero_iff : (C • X).point = 0 ↔ X.point = 0 := by
  rw [smul_point, Equiv.symm_apply_eq, equivVariableChange_zero]

/-- A change of variables acts on a pointed curve `(W, P)` by `(C • W, Q)`, with `Q` the point
of `C • W` carried to `P`. -/
theorem smul_mk (W : WeierstrassCurve R) (P : W.toAffine.Point) :
    C • (⟨W, P⟩ : PointedWeierstrassCurve R) =
      ⟨C • W, (equivVariableChange W C).symm P⟩ :=
  (rfl)

/-- **Changes of variables between affine pointed curves in coordinates.** `C` carries
`(W, (x, y))` to `(W', (x', y'))` exactly when `C • W = W'` and
`(x, y) = (u² x' + r, u³ y' + u² s x' + t)`. -/
theorem smul_mk_some_eq_mk_some_iff {W W' : WeierstrassCurve R} {x y x' y' : R}
    (h : W.toAffine.Nonsingular x y) (h' : W'.toAffine.Nonsingular x' y') :
    C • (⟨W, .some x y h⟩ : PointedWeierstrassCurve R) = ⟨W', .some x' y' h'⟩ ↔
      C • W = W' ∧ (C.u : R) ^ 2 * x' + C.r = x ∧
        (C.u : R) ^ 3 * y' + (C.u : R) ^ 2 * C.s * x' + C.t = y := by
  constructor
  · intro hC
    obtain rfl : C • W = W' := congrArg curve hC
    rw [smul_mk, mk_inj, Equiv.symm_apply_eq, equivVariableChange_some, some.injEq] at hC
    exact ⟨rfl, hC.1.symm, hC.2.symm⟩
  · rintro ⟨rfl, hx, hy⟩
    rw [smul_mk, mk_inj, Equiv.symm_apply_eq, equivVariableChange_some, some.injEq]
    exact ⟨hx.symm, hy.symm⟩

/-- **Changes of variables act on pointed curves**, the action of `C * C'` being that of `C'`
followed by that of `C`. -/
instance instMulActionVariableChange :
    MulAction (VariableChange R) (PointedWeierstrassCurve R) where
  one_smul X := ext_cast (one_smul _ X.curve) (by
    rw [← equivVariableChange_one, equivVariableChange_smul_point])
  mul_smul C C' X := ext_cast (mul_smul C C' X.curve) (by
    rw [smul_point C (C' • X), Equiv.eq_symm_apply, smul_point C' X, Equiv.eq_symm_apply]
    exact (equivVariableChange_mul X.curve C C' _).symm.trans
      (equivVariableChange_smul_point _ _))

section Field

variable {F : Type*} [Field F] [DecidableEq F] (C : VariableChange F)
  (X : PointedWeierstrassCurve F)

/-- Over a field, changes of variables preserve the order of the marked point. -/
@[simp]
theorem addOrderOf_smul_point : addOrderOf (C • X).point = addOrderOf X.point := by
  rw [smul_point, ← coe_addEquivVariableChange_symm, AddEquiv.addOrderOf_eq]

/-- Over a field, a change of variables preserves which multiples of the marked point vanish. -/
@[simp]
theorem nsmul_smul_point_eq_zero_iff (n : ℕ) : n • (C • X).point = 0 ↔ n • X.point = 0 := by
  rw [smul_point, ← coe_addEquivVariableChange_symm, ← map_nsmul, AddEquiv.map_eq_zero_iff]

variable (F) in
/-- The **elliptic curves over `F` with a marked point of exact order `N`**, as a sub-action of the
pointed Weierstrass curves. Its orbits under changes of variables are the isomorphism classes of
such pairs. -/
def exactOrder (N : ℕ) : SubMulAction (VariableChange F) (PointedWeierstrassCurve F) where
  carrier := {X | X.curve.IsElliptic ∧ addOrderOf X.point = N}
  smul_mem' C X hX := ⟨(isElliptic_smul_iff C X.curve).mpr hX.1,
    (addOrderOf_smul_point C X).trans hX.2⟩

@[simp]
theorem mem_exactOrder_iff {N : ℕ} :
    X ∈ exactOrder F N ↔ X.curve.IsElliptic ∧ addOrderOf X.point = N :=
  Iff.rfl

end Field

end PointedWeierstrassCurve

end TauCeti
