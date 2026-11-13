/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Topology
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic

/-!
# The group of projective Weierstrass points is a topological group

Over a topological field `F`, the native nonsingular projective points of a Weierstrass curve,
with their analytic topology induced from the projective plane, form a topological group. The
points are the quotient of the nonsingular homogeneous representatives by an open quotient map,
so continuity of the group law may be checked on representatives. There negation is linear, and
the sum is given near each pair of points by one of two polynomial addition laws: Mathlib's
`addXYZ`, attached to the line `Z = 0`, or the Bosma–Lenstra law `dblAddXYZ` attached to the
line `Y = 0`. At every pair of nonsingular representatives one of the two laws is nonzero, and
a nonzero value represents the sum. The proof uses no analytic structure on `F` beyond the
continuity of its ring operations, so it applies to complex, real and `p`-adic points alike.

A change of variables acts on homogeneous coordinates by an invertible matrix, so the group
isomorphism between the points of `C • W` and of `W` is a homeomorphism.

## Main results

* `WeierstrassCurve.Projective.Point.instIsTopologicalAddGroup`: the points form a topological
  group.
* `WeierstrassCurve.Projective.Point.continuousAddEquivVariableChange`: the change of variables
  `C` is an isomorphism of topological groups between the points of `C • W` and of `W`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.2 and III.3.
-/

public section

open Matrix Topology

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {W' : Projective R}

/-- The negation formula on homogeneous coordinates is continuous. -/
@[fun_prop]
protected theorem continuous_neg : Continuous W'.neg := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [neg, negY] <;> fun_prop

/-- The addition law `addXYZ` attached to the line `Z = 0` is continuous in both arguments. -/
@[fun_prop]
theorem continuous_addXYZ :
    Continuous fun PQ : (Fin 3 → R) × (Fin 3 → R) ↦ W'.addXYZ PQ.1 PQ.2 := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [addXYZ, addX, addY, negAddY, addZ, negY] <;> fun_prop

/-- The Bosma–Lenstra addition law `dblAddXYZ` attached to the line `Y = 0` is continuous in
both arguments. -/
@[fun_prop]
theorem continuous_dblAddXYZ :
    Continuous fun PQ : (Fin 3 → R) × (Fin 3 → R) ↦ W'.dblAddXYZ PQ.1 PQ.2 := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dblAddXYZ_X, dblAddXYZ_Y, dblAddXYZ_Z,
      dblAddX, dblAddY, dblAddZ] <;> fun_prop

namespace Point

variable {F : Type*} [Field F] {W : Projective F}

/-- A representative of the sum `add P Q` of two nonsingular representatives represents the sum
of their points. -/
private theorem exists_mk_eq_mk_add_mk {P Q R : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hR : R ≈ W.add P Q) :
    ∃ h : W.Nonsingular R, Point.mk ((nonsingularLift_iff R).mpr h) =
      Point.mk ((nonsingularLift_iff P).mpr hP) + Point.mk ((nonsingularLift_iff Q).mpr hQ) := by
  refine ⟨(nonsingular_of_equiv hR).mpr (nonsingular_add hP hQ), ?_⟩
  rw [Point.ext_iff, add_point, addMap_eq]
  exact Quotient.sound hR

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Negation of points is continuous: on homogeneous coordinates it is a linear map. -/
instance : ContinuousNeg W.Point := by
  refine ⟨isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr ?_⟩
  have h := continuous_mk (W := W) (Projective.continuous_neg.comp continuous_subtype_val)
    fun P : {P : Fin 3 → F // W.Nonsingular P} ↦ nonsingular_neg P.2
  convert h using 2 with P
  rw [Point.ext_iff]
  exact negMap_eq P.1

/-- Addition of points is continuous: near each pair of points it is given on homogeneous
coordinates by one of the two polynomial addition laws `addXYZ` and `dblAddXYZ`. -/
instance [T1Space F] : ContinuousAdd W.Point := by
  refine ⟨(isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).isQuotientMap.continuous_iff.mpr
    (continuous_iff_continuousAt.mpr fun PQ₀ ↦ ?_)⟩
  -- Near each pair of representatives one of the two addition laws stays nonzero and gives
  -- continuous homogeneous coordinates of the sum.
  let p : {P : Fin 3 → F // W.Nonsingular P} × {P : Fin 3 → F // W.Nonsingular P} →
      (Fin 3 → F) × (Fin 3 → F) := fun PQ ↦ (PQ.1.1, PQ.2.1)
  have hp : Continuous p := by fun_prop
  rcases addXYZ_ne_zero_or_dblAddXYZ_ne_zero PQ₀.1.2 PQ₀.2.2 with h | h
  · have hc := (continuous_addXYZ (W' := W)).comp hp
    refine continuousAt_of_eventually_eq_mk hc.continuousAt ?_
    filter_upwards [hc.continuousAt.eventually_ne h] with PQ hPQ
    exact exists_mk_eq_mk_add_mk PQ.1.2 PQ.2.2 (add_of_addXYZ_ne_zero hPQ ▸ Setoid.refl _)
  · have hc := (continuous_dblAddXYZ (W' := W)).comp hp
    refine continuousAt_of_eventually_eq_mk hc.continuousAt ?_
    filter_upwards [hc.continuousAt.eventually_ne h] with PQ hPQ
    exact exists_mk_eq_mk_add_mk PQ.1.2 PQ.2.2 (dblAddXYZ_equiv_add PQ.1.2 PQ.2.2 hPQ)

/-- **The points of a Weierstrass curve over a topological field form a topological group**, in
the analytic topology induced from the projective plane. -/
instance instIsTopologicalAddGroup [T1Space F] : IsTopologicalAddGroup W.Point where

section VariableChange

variable (W : WeierstrassCurve F) (C : VariableChange F)

/-- **A change of variables is an isomorphism of topological groups**: the group isomorphism
`Point.addEquivVariableChange` from the points of `C • W` to those of `W`, given on homogeneous
coordinates by the invertible matrix `C.toMatrix`, is a homeomorphism. -/
noncomputable def continuousAddEquivVariableChange :
    (C • W).toProjective.Point ≃ₜ+ W.toProjective.Point where
  toAddEquiv := addEquivVariableChange W C
  continuous_toFun := by
    refine isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr ?_
    simpa only [Function.comp_def, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
      AddEquiv.coe_toEquiv, addEquivVariableChange_mk] using
      continuous_mk ((continuous_const.matrix_mulVec continuous_subtype_val))
        fun P : {P : Fin 3 → F // (C • W).toProjective.Nonsingular P} ↦
          (nonsingular_variableChange W C P.1).mp P.2
  continuous_invFun := by
    refine isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr ?_
    simpa only [Function.comp_def, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
      AddEquiv.coe_toEquiv_symm, addEquivVariableChange_symm_mk] using
      continuous_mk ((continuous_const.matrix_mulVec continuous_subtype_val))
        fun P : {P : Fin 3 → F // W.toProjective.Nonsingular P} ↦
          (nonsingular_variableChange W C _).mpr (by
            rw [mulVec_mulVec, VariableChange.toMatrix_mul_toMatrix_inv, one_mulVec]
            exact P.2)

@[simp]
theorem coe_continuousAddEquivVariableChange :
    ⇑(continuousAddEquivVariableChange W C) = addEquivVariableChange W C :=
  (rfl)

@[simp]
theorem coe_continuousAddEquivVariableChange_symm :
    ⇑(continuousAddEquivVariableChange W C).symm = (addEquivVariableChange W C).symm :=
  (rfl)

end VariableChange

end Point

end WeierstrassCurve.Projective
