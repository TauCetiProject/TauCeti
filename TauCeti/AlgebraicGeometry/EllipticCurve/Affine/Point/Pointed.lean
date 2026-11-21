/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.ZMod.ValMinAbs
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
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
curves with a point of exact order `N`. Here `exactOrder F 0` marks points of infinite order.
For `N > 0`, these points specify constant cyclic markings, the point-marked moduli problem
of the congruence subgroup `Γ₁(N)`.
Multiplying the marked point by an integer commutes with changes of variables. This gives the two
operations on pointed curves. At positive levels, the units `d` modulo `N` act by
`P ↦ d • P`, the diamond action. For `M ≠ 0`, the map `P ↦ M • P` lowers exact order from `N * M`
to `N`, which corresponds to the inclusion `Γ₁(N M) ≤ Γ₁(N)`.

## Main definitions

* `TauCeti.PointedWeierstrassCurve R`: a Weierstrass curve over `R` with a marked point.
* `TauCeti.PointedWeierstrassCurve.instMulActionVariableChange`: the action of changes of variables.
* `TauCeti.PointedWeierstrassCurve.exactOrder F N`: over a field `F`, the elliptic curves with a
  marked point of exact order `N`, as a sub-action.
* `TauCeti.PointedWeierstrassCurve.instMulActionUnitsZModExactOrder`: the action of `(ℤ/Nℤ)ˣ` on
  these by multiplying the marked point, commuting with changes of variables.
* `TauCeti.PointedWeierstrassCurve.instMulActionUnitsZModExactOrderQuotient`: the induced
  diamond action on isomorphism classes.
* `TauCeti.PointedWeierstrassCurve.nsmulExactOrder N M`: multiplying the marked point by `M`, as
  an equivariant map from exact order `N * M` to exact order `N`.

## Main results

* `TauCeti.PointedWeierstrassCurve.equivVariableChange_smul_point`: the change of variables `C`
  carries the marked point of `C • X` to that of `X`.
* `TauCeti.PointedWeierstrassCurve.smul_mk_some_eq_mk_some_iff`: a change of variables between
  affine pointed curves, in coordinates.
* `TauCeti.PointedWeierstrassCurve.addOrderOf_smul_point`: over a field, changes of variables
  preserve the order of the marked point.
* `TauCeti.PointedWeierstrassCurve.smul_mk_zsmul_point`: over a field, changes of variables
  commute with multiplying the marked point by `n`.
* `TauCeti.PointedWeierstrassCurve.val_units_smul_of_intCast_eq`: a unit modulo `N` multiplies the
  marked point by any integer representative.
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

/-- Over a field, a change of variables commutes with multiplying the marked point by `n`. -/
theorem smul_mk_zsmul_point (n : ℤ) :
    C • (⟨X.curve, n • X.point⟩ : PointedWeierstrassCurve F) =
      ⟨(C • X).curve, n • (C • X).point⟩ := by
  -- The curves agree by `smul_curve`, which `rw` cannot apply under the dependent point.
  rw [smul_mk]
  refine mk_inj.mpr ?_
  rw [smul_point, ← coe_addEquivVariableChange_symm, map_zsmul]

variable {N : ℕ}

/-- Multiplying a marked point of exact order `N` by an integer `n` that is a unit modulo `N`
gives a point of exact order `N`. -/
theorem mk_zsmul_point_mem_exactOrder (hX : X ∈ exactOrder F N) {n : ℤ}
    (hn : IsUnit (n : ZMod N)) :
    (⟨X.curve, n • X.point⟩ : PointedWeierstrassCurve F) ∈ exactOrder F N := by
  obtain ⟨hE, hN⟩ := (mem_exactOrder_iff X).mp hX
  refine (mem_exactOrder_iff _).mpr ⟨hE, ?_⟩
  rw [← addOrderOf_nsmul_natAbs, Nat.Coprime.addOrderOf_nsmul, hN]
  rw [hN]
  exact Int.isCoprime_iff_gcd_eq_one.mp ((ZMod.isUnit_intCast_iff_isCoprime n N).mp hn)

/-- Multiplying a marked point of exact order `N * M` by `M ≠ 0` gives a point of exact order
`N`. -/
theorem mk_nsmul_point_mem_exactOrder_of_mem_mul {M : ℕ} (hM : M ≠ 0)
    (hX : X ∈ exactOrder F (N * M)) :
    (⟨X.curve, M • X.point⟩ : PointedWeierstrassCurve F) ∈ exactOrder F N := by
  obtain ⟨hE, hN⟩ := (mem_exactOrder_iff X).mp hX
  refine (mem_exactOrder_iff _).mpr ⟨hE, ?_⟩
  rw [addOrderOf_nsmul_of_dvd hM (hN ▸ dvd_mul_left M N), hN, Nat.mul_div_cancel _ (by omega)]

variable (N) in
/-- **Lowering the level**: for `M ≠ 0`, multiplying the marked point by `M` sends an elliptic
curve with a point of exact order `N * M` to one with a point of exact order `N`. For `N > 0`,
these points specify constant cyclic markings, and the map corresponds to
`Γ₁(N M) ≤ Γ₁(N)`. Over ℂ at these positive levels, choosing compatible primitive roots
`ζ_N = ζ_{NM}^M` identifies them with embeddings `α : μ_{NM} ↪ E[NM]`; the map then restricts
`α` to `μ_N`. The point operation commutes with changes of variables also at `N = 0`,
where it preserves infinite order. -/
def nsmulExactOrder (M : ℕ) [NeZero M] :
    exactOrder F (N * M) →[VariableChange F] exactOrder F N where
  toFun X := ⟨⟨X.val.curve, M • X.val.point⟩,
    mk_nsmul_point_mem_exactOrder_of_mem_mul X.val (NeZero.ne M) X.property⟩
  map_smul' C X := Subtype.ext <| by
    dsimp only [id_eq]
    rw [SubMulAction.val_smul, SubMulAction.val_smul]
    have h := smul_mk_zsmul_point C X.val M
    simp only [natCast_zsmul] at h
    exact h.symm

@[simp]
theorem val_nsmulExactOrder_apply (M : ℕ) [NeZero M] (X : exactOrder F (N * M)) :
    (nsmulExactOrder N M X : PointedWeierstrassCurve F) =
      ⟨X.val.curve, M • X.val.point⟩ :=
  (rfl)

section Units

/-- On a point of exact order `N`, multiplication by `n : ℤ` only depends on `n` modulo `N`. -/
private theorem zsmul_point_eq_of_intCast_eq (hX : X ∈ exactOrder F N) {m n : ℤ}
    (h : (m : ZMod N) = n) : m • X.point = n • X.point := by
  rw [zsmul_eq_zsmul_iff_modEq, ((mem_exactOrder_iff X).mp hX).2, ← ZMod.intCast_eq_intCast_iff,
    h]

/-- **Multiplying the marked point by a unit modulo `N`**: `d ∈ (ℤ/Nℤ)ˣ` sends an elliptic
curve `E` with a point `P` of exact order `N` to `(E, d • P)`, where `d` acts on `P` through any
integer representative (`TauCeti.PointedWeierstrassCurve.val_units_smul_of_intCast_eq`).
At positive level this acts on constant cyclic markings. Over ℂ, after choosing a primitive
`N`-th root `ζ_N`, the embedding `α : μ_N ↪ E[N]` with `α(ζ_N) = P` transforms as
`α ↦ α ∘ [d]`, the diamond operator `⟨d⟩`. -/
instance instSMulUnitsZModExactOrder : SMul (ZMod N)ˣ (exactOrder F N) where
  smul d X := ⟨⟨X.val.curve, (d : ZMod N).valMinAbs • X.val.point⟩,
    mk_zsmul_point_mem_exactOrder X.val X.property (by rw [ZMod.coe_valMinAbs]; exact d.isUnit)⟩

variable (d : (ZMod N)ˣ) (Y : exactOrder F N)

/-- The unit `d` multiplies the marked point by the representative `(d : ZMod N).valMinAbs`. -/
@[simp]
theorem val_units_smul :
    ((d • Y : exactOrder F N) : PointedWeierstrassCurve F) =
      ⟨Y.val.curve, (d : ZMod N).valMinAbs • Y.val.point⟩ :=
  (rfl)

/-- The unit `d` multiplies the marked point by any integer representative of `d`. -/
theorem val_units_smul_of_intCast_eq {n : ℤ} (hn : (n : ZMod N) = d) :
    ((d • Y : exactOrder F N) : PointedWeierstrassCurve F) = ⟨Y.val.curve, n • Y.val.point⟩ := by
  rw [val_units_smul, mk_inj]
  exact zsmul_point_eq_of_intCast_eq Y.val Y.property (by rw [ZMod.coe_valMinAbs, hn])

/-- The units modulo `N` act on the elliptic curves with a point of exact order `N` by
multiplying the marked point. -/
instance instMulActionUnitsZModExactOrder : MulAction (ZMod N)ˣ (exactOrder F N) where
  one_smul X := Subtype.ext <| by
    rw [val_units_smul_of_intCast_eq 1 X (n := 1) (by simp), one_zsmul]
  mul_smul d e X := Subtype.ext <| by
    have h : (((d : ZMod N).valMinAbs * (e : ZMod N).valMinAbs : ℤ) : ZMod N) = (d * e : _) := by
      rw [Int.cast_mul, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, Units.val_mul]
    rw [val_units_smul_of_intCast_eq (d * e) X h, val_units_smul d, val_units_smul e, mul_zsmul]

/-- Changes of variables commute with multiplying the marked point by a unit modulo `N`, so the
units act on the isomorphism classes of elliptic curves with a point of exact order `N`. -/
instance instSMulCommClassVariableChangeUnitsZModExactOrder :
    SMulCommClass (VariableChange F) (ZMod N)ˣ (exactOrder F N) where
  smul_comm C d X := Subtype.ext <| by
    rw [SubMulAction.val_smul, val_units_smul, val_units_smul, SubMulAction.val_smul]
    exact smul_mk_zsmul_point C X.val _

/-- Units modulo `N` act on isomorphism classes of elliptic curves with a point of exact
order `N`, through their commuting action on marked curves. -/
instance instSMulUnitsZModExactOrderQuotient :
    SMul (ZMod N)ˣ (MulAction.orbitRel.Quotient (VariableChange F) (exactOrder F N)) where
  smul d :=
    let f : exactOrder F N →[VariableChange F] exactOrder F N :=
      ⟨(d • ·), fun C X ↦ (smul_comm C d X).symm⟩
    f.orbitRelQuotientMap

/-- The diamond action on isomorphism classes multiplies the marked point on representatives. -/
@[simp]
theorem units_smul_quotient_mk (d : (ZMod N)ˣ) (X : exactOrder F N) :
    d • (Quotient.mk'' X : MulAction.orbitRel.Quotient (VariableChange F) (exactOrder F N)) =
      Quotient.mk'' (d • X) :=
  MulActionHom.orbitRelQuotientMap_mk _ X

/-- The unit action on marked curves descends to an action on their isomorphism classes. -/
instance instMulActionUnitsZModExactOrderQuotient :
    MulAction (ZMod N)ˣ
      (MulAction.orbitRel.Quotient (VariableChange F) (exactOrder F N)) where
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h X => rw [units_smul_quotient_mk, one_smul]
  mul_smul d e q := by
    induction q using Quotient.inductionOn with
    | h X => rw [units_smul_quotient_mk, units_smul_quotient_mk, units_smul_quotient_mk, mul_smul]

/-- Multiplication of the marked point by `M` commutes with diamonds after reducing
units from modulus `N * M` to modulus `N`. -/
theorem nsmulExactOrder_units_smul (M : ℕ) [NeZero M] (d : (ZMod (N * M))ˣ)
    (X : exactOrder F (N * M)) :
    nsmulExactOrder N M (d • X) =
      ZMod.unitsMap (dvd_mul_right N M) d • nsmulExactOrder N M X := by
  have hd : (((d : ZMod (N * M)).valMinAbs : ℤ) : ZMod N) =
      ZMod.unitsMap (dvd_mul_right N M) d := by
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_ofClass]
    simpa only [map_intCast] using congrArg (ZMod.castHom (dvd_mul_right N M) (ZMod N))
      (ZMod.coe_valMinAbs (d : ZMod (N * M)))
  apply Subtype.ext
  rw [val_nsmulExactOrder_apply, val_units_smul,
    val_units_smul_of_intCast_eq _ _ hd, val_nsmulExactOrder_apply]
  exact mk_inj.mpr (smul_comm _ _ _)

/-- Level lowering on isomorphism classes commutes with diamonds, reducing the unit
modulo `N`. -/
theorem nsmulExactOrder_orbitRelQuotientMap_units_smul (M : ℕ) [NeZero M]
    (d : (ZMod (N * M))ˣ)
    (q : MulAction.orbitRel.Quotient (VariableChange F) (exactOrder F (N * M))) :
    (nsmulExactOrder N M).orbitRelQuotientMap (d • q) =
      ZMod.unitsMap (dvd_mul_right N M) d • (nsmulExactOrder N M).orbitRelQuotientMap q := by
  induction q using Quotient.inductionOn with
  | h X =>
    rw [units_smul_quotient_mk, MulActionHom.orbitRelQuotientMap_mk,
      MulActionHom.orbitRelQuotientMap_mk, units_smul_quotient_mk, nsmulExactOrder_units_smul]

end Units

end Field

end PointedWeierstrassCurve

end TauCeti
