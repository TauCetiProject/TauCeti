/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Pointed.Units

/-!
# Diamond action on isomorphism classes of marked elliptic curves

Over a field `F`, the units modulo `N` act on the elliptic curves with a marked point of exact
order `N` by multiplying the marked point, commuting with changes of variables. This file descends
that action to the isomorphism classes, the orbits of the changes of variables, and shows that
lowering the level by multiplying the marked point by `M` commutes with it on classes.

## Main definitions

* `TauCeti.PointedWeierstrassCurve.instMulActionUnitsZModExactOrderQuotient`: the induced
  diamond action on isomorphism classes.

## Main results

* `TauCeti.PointedWeierstrassCurve.units_smul_quotient_mk`: the diamond action multiplies the
  marked point of a representative.
* `TauCeti.PointedWeierstrassCurve.nsmulExactOrder_orbitRelQuotientMap_units_smul`: level
  lowering on isomorphism classes commutes with diamonds, reducing the unit.
-/

public section

namespace TauCeti

open WeierstrassCurve

namespace PointedWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {N : ℕ}

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

/-- Level lowering on isomorphism classes commutes with diamonds, reducing the unit
modulo `N`. -/
@[simp]
theorem nsmulExactOrder_orbitRelQuotientMap_units_smul (M : ℕ) [NeZero M]
    (d : (ZMod (N * M))ˣ)
    (q : MulAction.orbitRel.Quotient (VariableChange F) (exactOrder F (N * M))) :
    (nsmulExactOrder N M).orbitRelQuotientMap (d • q) =
      ZMod.unitsMap (dvd_mul_right N M) d • (nsmulExactOrder N M).orbitRelQuotientMap q := by
  induction q using Quotient.inductionOn with
  | h X =>
    rw [units_smul_quotient_mk, MulActionHom.orbitRelQuotientMap_mk,
      MulActionHom.orbitRelQuotientMap_mk, units_smul_quotient_mk, nsmulExactOrder_units_smul]

end PointedWeierstrassCurve

end TauCeti
