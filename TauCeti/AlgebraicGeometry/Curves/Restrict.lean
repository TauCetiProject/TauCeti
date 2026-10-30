/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Category
public import TauCeti.AlgebraicGeometry.Scheme.Place.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.AlgebraicGeometry.Scheme.Place.Hom
import TauCeti.AlgebraicGeometry.Scheme.Place.Injective
import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# Morphisms of regular proper curves act on points by restricting places

Let `f : X ⟶ Y` be a dominant `k`-morphism of regular proper curves over a field `k`, with
pullback of rational functions `f^* : k(Y) → k(X)`. A codimension-one point `x` of `X` has a place
`P_x` of `k(X)`, whose valuation ring is the local ring of `X` at `x`. This file proves that `f`
sends `x` to the codimension-one point `y` of `Y` exactly when the valuation of `P_x`, restricted
to `k(Y)` along `f^*`, is equivalent to the valuation of `P_y`; that is, when `P_x` lies over
`P_y`.

A function regular at `f x` pulls back to a function regular at `x`, so the valuation ring at
`f x` is carried into the valuation ring of `P_x`, which characterizes the place below `P_x`
(`TauCeti.Place.restrict_eq_iff_integers_le`). The point `f x` is not the generic point of `Y`,
because `k(X)` is algebraic over `f^* k(Y)` and so some function of `k(Y)` pulls back to one with a
pole at `x`. Distinct codimension-one points of the separated scheme `Y` have distinct places.

This is Stichtenoth's dictionary between places and points, for morphisms: on points, the
morphism of curves induced by an embedding of function fields is restriction of places. The
special case of the two-chart model is
`TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_equivPlace_symm`.

## Main results

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.hom_apply_eq_iff_isEquiv_comap`: `f x = y`
  exactly when the valuation of the place of `x`, restricted along `f^*`, is equivalent to the
  valuation of the place of `y`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1 and Appendix B.
-/

public section

open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.RegularProperCurveCat

universe u

variable {k : Type u} [Field k] {X Y : RegularProperCurveCat k}

/-- **A morphism of regular proper curves restricts places**: a dominant `k`-morphism
`f : X ⟶ Y` sends the codimension-one point `x` to the codimension-one point `y` exactly when the
valuation of the place of `x`, restricted to `k(Y)` along the pullback of rational functions `f^*`,
is equivalent to the valuation of the place of `y`. -/
theorem hom_apply_eq_iff_isEquiv_comap (f : X ⟶ Y) (x : CodimensionOnePoint X.toScheme)
    (y : CodimensionOnePoint Y.toScheme) :
    f.hom (x : X.toScheme) = y ↔
      ((X.toScheme.toPlace (k := k) (x : X.toScheme)).valuation.comap
        (f.hom.functionFieldAlgHom k).toRingHom).IsEquiv
          (Y.toScheme.toPlace (k := k) (y : Y.toScheme)).valuation := by
  -- Regard `k(X)` as an extension of `k(Y)` through `f^*`; it is algebraic, as both are function
  -- fields of one variable over `k`.
  let : Algebra Y.toScheme.functionField X.toScheme.functionField :=
    (f.hom.functionFieldAlgHom k).toRingHom.toAlgebra
  have : IsScalarTower k Y.toScheme.functionField X.toScheme.functionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((f.hom.functionFieldAlgHom k).commutes c).symm
  have : Algebra.IsAlgebraic Y.toScheme.functionField X.toScheme.functionField :=
    IsFunctionField.isAlgebraic_of_isFunctionField
      (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y.toScheme))
      (Scheme.IsCurveOver.isFunctionField (k := k) (X := X.toScheme))
  have : Y.toScheme.IsSeparated :=
    Scheme.IsSeparated.of_isSeparated (Y.toScheme ↘ Spec (.of k))
  have halg (g : Y.toScheme.functionField) :
      algebraMap Y.toScheme.functionField X.toScheme.functionField g =
        f.hom.functionFieldMap g := by
    simp [RingHom.algebraMap_toAlgebra]
  set P' := X.toScheme.toPlace (k := k) (x : X.toScheme)
  -- Some function of `k(Y)` has a pole at `x`, so `f x` is not the generic point.
  obtain ⟨g, hg⟩ : ∃ g : Y.toScheme.functionField, f.hom.functionFieldMap g ∉ P'.integers := by
    by_contra! h
    exact (P'.restrict k Y.toScheme.functionField).integers_ne_top
      (eq_top_iff.mpr fun g _ ↦ (Place.mem_integers_restrict_iff k _ P' g).mpr (halg g ▸ h g))
  have hcoh : Order.coheight (f.hom (x : X.toScheme)) = 1 :=
    (Scheme.coheight_eq_one_iff_ne_genericPoint
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y.toScheme) k).le).mpr <|
      f.hom.ne_genericPoint_of_functionFieldMap_notMem_toPlace_integers (k := k) _ hg
  -- The valuation ring at `f x` is carried into the valuation ring of `P'`.
  let q : CodimensionOnePoint Y.toScheme := ⟨_, hcoh⟩
  have : IsDiscreteValuationRing (Y.toScheme.presheaf.stalk (q : Y.toScheme)) :=
    Y.isDiscreteValuationRing_stalk q
  have hq : Y.toScheme.toPlace (k := k) (q : Y.toScheme) =
      P'.restrict k Y.toScheme.functionField := by
    refine ((Place.restrict_eq_iff_integers_le k _ P' _).mpr fun g hg ↦ ?_).symm
    obtain ⟨a, rfl⟩ :=
      (Y.toScheme.mem_toPlace_integers_iff_exists_stalk (k := k) (q : Y.toScheme) g).mp hg
    rw [halg]
    exact f.hom.functionFieldMap_algebraMap_mem_toPlace_integers (k := k) _ a
  rw [← RingHom.algebraMap_toAlgebra (f.hom.functionFieldAlgHom k).toRingHom,
    ← Place.restrict_eq_iff_isEquiv_comap, ← hq]
  exact toPlace_eq_iff.symm

end TauCeti.AlgebraicGeometry.RegularProperCurveCat
