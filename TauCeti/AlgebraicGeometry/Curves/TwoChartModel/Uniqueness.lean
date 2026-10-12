/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AlgHom

/-!
# Every regular proper curve is a two-chart model

Let `F / k` be an algebraic function field and `x ∈ F` transcendental over `k`. The two-chart
model `twoChartModel hF hx`, glued from the normalizations of `k[x]` and `k[x⁻¹]` in `F`, is an
integral scheme proper over `k` with function field `F`, all of whose local rings are valuation
rings. This file proves that it is the only such scheme: **every integral scheme `X` proper over
`k`, whose local rings are valuation rings and whose function field is `k`-isomorphic to `F`, is
isomorphic over `k` to `twoChartModel hF hx`**
(`TauCeti.AlgebraicGeometry.twoChartModel.isoOfFunctionFieldAlgEquiv`).

The hypotheses hold for every regular integral curve `X` proper over `k`: its local rings are the
discrete valuation rings at the closed points and the function field at the generic point. Its
function field is an algebraic function field over `k`
(`TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff`), so for every transcendental
`x ∈ k(X)` the curve `X` is the two-chart model of its own function field. Together with the
description of the morphisms of two-chart models by the embeddings of their function fields
(`TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom`), this is the correspondence between
regular proper curves over `k` and algebraic function fields over `k`, on objects.

The isomorphism is the one induced by the isomorphism `k(X) ≃ F ≃ k(twoChartModel hF hx)` of
function fields (`AlgebraicGeometry.Scheme.isoOfFunctionFieldAlgEquiv`), so its pullback of rational
functions is that isomorphism.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.isoOfFunctionFieldAlgEquiv`: the isomorphism of
  `k`-schemes `X ≅ twoChartModel hF hx` induced by a `k`-isomorphism `k(X) ≃ F`.

## Main results

* the instances `(isoOfFunctionFieldAlgEquiv …).hom.IsOver (Spec k)` and
  `(isoOfFunctionFieldAlgEquiv …).inv.IsOver (Spec k)`.
* `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldMap_isoOfFunctionFieldAlgEquiv_hom` and
  `functionFieldEquiv_functionFieldMap_isoOfFunctionFieldAlgEquiv_inv` (in the same namespace):
  under `k(twoChartModel hF hx) ≃ F`, the pullbacks of rational functions along the isomorphism and
  its inverse are the given isomorphism `k(X) ≃ F` and its inverse.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Corollary I.6.12.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford Graduate Texts in Mathematics 6,
  Oxford University Press, 2002, Section 7.3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] (hF : IsFunctionField k F) {x : F}
  (hx : x ≠ 0) (hxt : Transcendental k x) {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] (hX : ∀ y : X, ValuationRing (X.presheaf.stalk y))
  (e : X.functionField ≃ₐ[k] F)

/-- **An integral scheme proper over `k` whose local rings are valuation rings is the two-chart
model of its function field**: the isomorphism of `k`-schemes `X ≅ twoChartModel hF hx` induced by
a `k`-isomorphism `e : k(X) ≃ F`, for any transcendental `x ∈ F`. -/
noncomputable def isoOfFunctionFieldAlgEquiv : X ≅ twoChartModel hF hx :=
  have := isProper (hF := hF) (hx := hx) hxt
  Scheme.isoOfFunctionFieldAlgEquiv hX (valuationRing_stalk hxt)
    ((functionFieldEquiv hxt).trans e.symm)

/-- The isomorphism `isoOfFunctionFieldAlgEquiv` is a morphism over `k`. -/
instance : (isoOfFunctionFieldAlgEquiv hF hx hxt hX e).hom.IsOver (Spec (.of k)) := by
  have := isProper (hF := hF) (hx := hx) hxt
  rw [isoOfFunctionFieldAlgEquiv]
  infer_instance

/-- The inverse of the isomorphism `isoOfFunctionFieldAlgEquiv` is a morphism over `k`. -/
instance : (isoOfFunctionFieldAlgEquiv hF hx hxt hX e).inv.IsOver (Spec (.of k)) := by
  have := isProper (hF := hF) (hx := hx) hxt
  rw [isoOfFunctionFieldAlgEquiv]
  infer_instance

/-- **The pullback of rational functions along `isoOfFunctionFieldAlgEquiv e` is `e⁻¹`**, read
through the identification `k(twoChartModel hF hx) ≃ F`. -/
@[simp]
theorem functionFieldMap_isoOfFunctionFieldAlgEquiv_hom (z : F) :
    (isoOfFunctionFieldAlgEquiv hF hx hxt hX e).hom.functionFieldMap
      ((functionFieldEquiv hxt).symm z) = e.symm z := by
  have := isProper (hF := hF) (hx := hx) hxt
  simp [isoOfFunctionFieldAlgEquiv]

/-- **The pullback of rational functions along the inverse of `isoOfFunctionFieldAlgEquiv e` is
`e`**, read through the identification `k(twoChartModel hF hx) ≃ F`. -/
@[simp]
theorem functionFieldEquiv_functionFieldMap_isoOfFunctionFieldAlgEquiv_inv
    (a : X.functionField) :
    functionFieldEquiv hxt ((isoOfFunctionFieldAlgEquiv hF hx hxt hX e).inv.functionFieldMap a) =
      e a := by
  have := isProper (hF := hF) (hx := hx) hxt
  simp [isoOfFunctionFieldAlgEquiv]

end TauCeti.AlgebraicGeometry.twoChartModel
