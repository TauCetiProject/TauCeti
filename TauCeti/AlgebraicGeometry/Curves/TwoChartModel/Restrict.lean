/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AlgHom
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.AlgebraicGeometry.Scheme.Place.Hom

/-!
# Morphisms of two-chart models act on points by restricting places

Let `F' / F` be an extension of algebraic function fields over `k`, and `x ∈ F`, `x' ∈ F'`
transcendental over `k`. Such an extension is always algebraic
(`TauCeti.IsFunctionField.isAlgebraic_of_isFunctionField`); the statements carry this as the
hypothesis `Algebra.IsIntegral F F'`, under which the place `P'.restrict k F` below a place `P'` of
`F'` is defined. The embedding `F → F'` induces the dominant `k`-morphism
`homOfAlgHom : X' ⟶ X` of the two-chart models `X' = twoChartModel hF' hx'` and
`X = twoChartModel hF hx`, and the codimension-one points of `X'` and `X` are the places of `F'`
and `F` (`TauCeti.AlgebraicGeometry.twoChartModel.equivPlace`). This file proves that under these
identifications the morphism sends the point of a place `P'` of `F'` to the point of the place
`P'.restrict k F` of `F` that `P'` lies over.

A function of `F` regular at the image point pulls back to a function regular at the point of
`P'`, so the valuation ring of the image point is carried into the valuation ring of `P'`, which
characterizes the place below `P'` (`TauCeti.Place.restrict_eq_iff_integers_le`). The image point
is not the generic point, because `F'` is algebraic over `F` and so some function of `F` has a
pole at `P'`.

Thus on points the morphism of curves induced by an extension of function fields is restriction
of places, as in Stichtenoth's dictionary between places and points.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_equivPlace_symm`: the point of `P'` is
  sent to the point of `P'.restrict k F`.
* `TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_equivPlace_symm_eq_iff`: the point of `P'`
  is sent to the point of `P` exactly when `P'` lies over `P`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1 and Appendix B.
-/

public section

open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
  (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F} (hx : x ≠ 0) {x' : F'}
  (hx' : x' ≠ 0) {hxt : Transcendental k x} {hx't : Transcendental k x'}

/-- **The morphism of two-chart models induced by `F → F'` restricts places**: it sends the
codimension-one point of a place `P'` of `F'` to the codimension-one point of the place
`P'.restrict k F` of `F` that `P'` lies over. -/
@[simp]
theorem homOfAlgHom_equivPlace_symm (P' : Place k F') :
    homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F')
        ((equivPlace hx't).symm P' : twoChartModel hF' hx') =
      ((equivPlace hxt).symm (P'.restrict k F) : twoChartModel hF hx) := by
  set f := homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F')
  set p' := (equivPlace hx't).symm P'
  have := isDiscreteValuationRing_stalk (hF := hF') (hx := hx') hx't p'
  -- Read through `k(X) ≃ F` and `k(X') ≃ F'`, the pullback along `f` is `F → F'` and the
  -- valuation ring of the place of `p'` is the valuation ring of `P'`.
  have hpull (z : F) : functionFieldEquiv hx't (f.functionFieldMap
      ((functionFieldEquiv hxt).symm z)) = algebraMap F F' z := by
    rw [functionFieldEquiv_functionFieldMap_homOfAlgHom, IsScalarTower.coe_toAlgHom']
  have hmem (w : (twoChartModel hF' hx').functionField) :
      w ∈ ((twoChartModel hF' hx').toPlace (k := k) (p' : twoChartModel hF' hx')).integers ↔
        functionFieldEquiv hx't w ∈ P'.integers := by
    conv_rhs => rw [← (equivPlace (hF := hF') (hx := hx') hx't).apply_symm_apply P']
    rw [equivPlace_apply, Place.mem_integers_map_iff, AlgEquiv.symm_apply_apply]
  -- Some function of `F` has a pole at `P'`, so `f p'` is not the generic point.
  obtain ⟨g, hg⟩ : ∃ g : F, algebraMap F F' g ∉ P'.integers := by
    by_contra! h
    exact (P'.restrict k F).integers_ne_top
      (eq_top_iff.mpr fun g _ ↦ (Place.mem_integers_restrict_iff k F P' g).mpr (h g))
  have hcoh : Order.coheight (f p') = 1 :=
    (Scheme.coheight_eq_one_iff_ne_genericPoint (topologicalKrullDim_eq_one hxt).le).mpr <|
      f.ne_genericPoint_of_functionFieldMap_notMem_toPlace_integers (k := k) p'
        (z := (functionFieldEquiv hxt).symm g) (by rwa [hmem, hpull])
  -- The valuation ring of the place of `f p'` is carried into the valuation ring of `P'`.
  let q : CodimensionOnePoint (twoChartModel hF hx) := ⟨f p', hcoh⟩
  have hq : equivPlace hxt q = P'.restrict k F := by
    refine ((Place.restrict_eq_iff_integers_le k F P' _).mpr fun g hg ↦ ?_).symm
    obtain ⟨a, rfl⟩ := (mem_integers_equivPlace_iff hxt q g).mp hg
    rw [← hpull, AlgEquiv.symm_apply_apply, ← hmem]
    exact f.functionFieldMap_algebraMap_mem_toPlace_integers p' a
  rw [← hq, Equiv.symm_apply_apply]

/-- **The point of `P'` is sent to the point of `P` exactly when `P'` lies over `P`**, for the
morphism of two-chart models induced by `F → F'`. -/
theorem homOfAlgHom_equivPlace_symm_eq_iff (P' : Place k F') (P : Place k F) :
    homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F')
        ((equivPlace hx't).symm P' : twoChartModel hF' hx') =
      ((equivPlace hxt).symm P : twoChartModel hF hx) ↔ P'.restrict k F = P := by
  rw [homOfAlgHom_equivPlace_symm, Subtype.val_inj, Equiv.apply_eq_iff_eq]

end TauCeti.AlgebraicGeometry.twoChartModel
