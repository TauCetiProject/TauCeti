/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AlgHom
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Curve

/-!
# Every regular proper curve is the two-chart model of its function field

Let `X` be a curve over a field `k` (an integral scheme, proper and of dimension one over `k`)
which is regular, in the sense that its local rings away from the generic point are discrete
valuation rings, and let `K = k(X)` be its function field. For any `x ∈ K` transcendental over
`k`, the two-chart model `M = twoChartModel hF hx` of `K`, glued from the
normalizations of `k[x]` and `k[x⁻¹]` in `K`, is a regular proper curve over `k` with function
field `K`. This file proves that **`X` is isomorphic to `M`** over `k`, by the unique isomorphism
whose pullback of rational functions is the identification `k(M) ≃ₐ[k] K`
(`TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv`).

Both `X` and `M` are integral, have valuation rings as local rings (the function field at the
generic point, a discrete valuation ring elsewhere), and are proper over `k`. So the
morphism `Spec K ⟶ M` through the generic point extends uniquely to a `k`-morphism `X ⟶ M`, and
the morphism `Spec K ⟶ X` through the generic point extends uniquely to a `k`-morphism `M ⟶ X`
(`AlgebraicGeometry.Scheme.homOfFunctionField`). Both composites restrict to the identity at the
generic point, and a morphism into a separated scheme is determined there, so they are inverse
isomorphisms.

Thus every regular proper curve over `k` is, up to a canonical isomorphism, the normalization of
the projective line in its function field. This is the object half of the correspondence between
function fields of one variable and regular proper curves; the morphism half, for two-chart
models, is `TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom`.

## Main definitions

* `AlgebraicGeometry.Scheme.isoTwoChartModel`: the isomorphism of a regular proper curve `X` over
  `k` with the two-chart model of `k(X)` built from a transcendental `x ∈ k(X)`.

## Main results

* the instances `(X.isoTwoChartModel …).hom.IsOver (Spec k)` and
  `(X.isoTwoChartModel …).inv.IsOver (Spec k)`.
* `AlgebraicGeometry.Scheme.functionFieldMap_isoTwoChartModel_hom`: the pullback of rational
  functions along the isomorphism `X ⟶ M` is the identification `k(M) ≃ₐ[k] k(X)`, and
  `AlgebraicGeometry.Scheme.functionFieldMap_isoTwoChartModel_inv` the same for its inverse.
* `AlgebraicGeometry.Scheme.eq_isoTwoChartModel_hom_iff`: a dominant `k`-morphism `X ⟶ M` is this
  isomorphism exactly when its pullback of rational functions is that identification.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem I.6.9 and
  Corollary I.6.12.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]
  {x : X.functionField} (hx : x ≠ 0) (hxt : Transcendental k x)

/-- The identification of the function field of the two-chart model of `k(X)` with `k(X)`, as an
isomorphism of rings. -/
private noncomputable def functionFieldIso :
    (twoChartModel (IsCurveOver.isFunctionField (k := k) (X := X)) hx).functionField ≅
      X.functionField :=
  (twoChartModel.functionFieldEquiv hxt).toRingEquiv.toCommRingCatIso

variable [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- **A regular proper curve is the two-chart model of its function field**: for a curve `X` over
`k` whose codimension-one local rings are discrete valuation rings and `x ∈ k(X)` transcendental
over `k`, the isomorphism of `X` with
the two-chart model of `k(X)` built from `x`. It is the unique dominant `k`-morphism whose
pullback of rational functions is the identification of the function field of the model with
`k(X)` (`eq_isoTwoChartModel_hom_iff`). -/
noncomputable def isoTwoChartModel :
    X ≅ twoChartModel (IsCurveOver.isFunctionField (k := k) (X := X)) hx :=
  have := twoChartModel.isProper (hF := IsCurveOver.isFunctionField (k := k) (X := X)) (hx := hx)
    hxt
  { hom := homOfFunctionField
      (IsCurveOver.valuationRing_stalk k X) _
      (specMap_comp_fromSpecStalk_genericPoint_comp_over k (functionFieldIso X hx hxt).hom
        (twoChartModel.functionFieldEquiv hxt).commutes)
    inv := homOfFunctionField (twoChartModel.valuationRing_stalk hxt) _
      (specMap_comp_fromSpecStalk_genericPoint_comp_over k (functionFieldIso X hx hxt).inv
        (twoChartModel.functionFieldEquiv hxt).symm.commutes)
    hom_inv_id := by
      refine ext_of_isDominant_of_isSeparated' (Spec (.of k))
        (X.fromSpecStalk (genericPoint X)) ?_
      simp [← Spec.map_comp_assoc, -Spec.map_comp]
    inv_hom_id := by
      refine ext_of_isDominant_of_isSeparated' (Spec (.of k))
        ((twoChartModel _ hx).fromSpecStalk (genericPoint _)) ?_
      simp [← Spec.map_comp_assoc, -Spec.map_comp] }

/-- The isomorphism `X ⟶ M` of `isoTwoChartModel` is a morphism over `k`. -/
instance : (X.isoTwoChartModel hx hxt).hom.IsOver (Spec (.of k)) := by
  have := twoChartModel.isProper (hF := IsCurveOver.isFunctionField (k := k) (X := X)) (hx := hx)
    hxt
  -- Instance search does not see through `isoTwoChartModel` to `Scheme.homOfFunctionField`, so the
  -- instance is applied by name.
  exact isOver_homOfFunctionField _ _ _

/-- The isomorphism `M ⟶ X` of `isoTwoChartModel` is a morphism over `k`. -/
instance : (X.isoTwoChartModel hx hxt).inv.IsOver (Spec (.of k)) := by
  -- As for the forward morphism, the instance is applied by name.
  exact isOver_homOfFunctionField _ _ _

/-- On function fields, the isomorphism `X ⟶ M` of `isoTwoChartModel` pulls back along
`functionFieldIso`. -/
private theorem functionFieldMap_isoTwoChartModel_hom_eq :
    (X.isoTwoChartModel hx hxt).hom.functionFieldMap = (functionFieldIso X hx hxt).hom := by
  have := twoChartModel.isProper (hF := IsCurveOver.isFunctionField (k := k) (X := X)) (hx := hx)
    hxt
  refine ((Hom.eq_functionFieldMap_iff _ _).mpr ?_).symm
  exact (fromSpecStalk_homOfFunctionField _ _ _).symm

/-- **The pullback of rational functions along `X ≅ M` is the identification of function
fields**: under the identification `k(M) ≃ₐ[k] k(X)` of the function field of the two-chart model
of `k(X)`, the pullback along the isomorphism `X ⟶ M` of `isoTwoChartModel` is the identity. -/
@[simp]
theorem functionFieldMap_isoTwoChartModel_hom (z : X.functionField) :
    (X.isoTwoChartModel hx hxt).hom.functionFieldMap
      ((twoChartModel.functionFieldEquiv hxt).symm z) = z := by
  rw [functionFieldMap_isoTwoChartModel_hom_eq]
  exact (twoChartModel.functionFieldEquiv hxt).apply_symm_apply z

/-- The pullback of rational functions along the isomorphism `M ⟶ X` of `isoTwoChartModel` is the
identification `k(X) ≃ₐ[k] k(M)` of `k(X)` with the function field of the two-chart model. -/
@[simp]
theorem functionFieldMap_isoTwoChartModel_inv (z : X.functionField) :
    (X.isoTwoChartModel hx hxt).inv.functionFieldMap z =
      (twoChartModel.functionFieldEquiv hxt).symm z := by
  conv_lhs => rw [← functionFieldMap_isoTwoChartModel_hom X hx hxt z]
  rw [← CommRingCat.comp_apply, ← Hom.functionFieldMap_comp]
  simp

/-- **A regular proper curve is the two-chart model of its function field in exactly one way**: a
dominant `k`-morphism `f : X ⟶ M` to the two-chart model of `k(X)` is the isomorphism of
`isoTwoChartModel` exactly when, under the identification `k(M) ≃ₐ[k] k(X)`, its pullback of
rational functions is the identity. -/
theorem eq_isoTwoChartModel_hom_iff
    (f : X ⟶ twoChartModel (IsCurveOver.isFunctionField (k := k) (X := X)) hx)
    [f.IsOver (Spec (.of k))] [IsDominant f] :
    f = (X.isoTwoChartModel hx hxt).hom ↔
      ∀ z, f.functionFieldMap ((twoChartModel.functionFieldEquiv hxt).symm z) = z := by
  refine ⟨fun h ↦ h ▸ functionFieldMap_isoTwoChartModel_hom X hx hxt, fun h ↦ ?_⟩
  have := twoChartModel.isProper (hF := IsCurveOver.isFunctionField (k := k) (X := X)) (hx := hx)
    hxt
  refine Hom.ext_of_functionFieldMap_eq (Spec (.of k)) ?_
  ext a
  obtain ⟨z, rfl⟩ := (twoChartModel.functionFieldEquiv hxt).symm.surjective a
  rw [h, functionFieldMap_isoTwoChartModel_hom]

end AlgebraicGeometry.Scheme
