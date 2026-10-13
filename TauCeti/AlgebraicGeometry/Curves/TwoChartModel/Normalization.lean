/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteMap
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Regular
public import TauCeti.AlgebraicGeometry.Normalization.IsIso
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# The two-chart model is a relative normalization

Let `F' / F` be an integral extension of algebraic function fields over `k`, let `x ∈ F` be
transcendental over `k`, and let `x' ∈ F'` be its image. The morphism of two-chart models
`map : twoChartModel hF' hx' ⟶ twoChartModel hF hx` is finite
(`TauCeti.AlgebraicGeometry.twoChartModel.isFinite_map`), and the local rings of
`twoChartModel hF' hx'` are valuation rings, hence integrally closed. So `twoChartModel hF' hx'` is
the normalization of `twoChartModel hF hx` in its function field `F'`, along the generic point
`Spec k(X') ⟶ X' ⟶ X`, where `X = twoChartModel hF hx` and `X' = twoChartModel hF' hx'`.

Through `normalizationIso`, Mathlib's universal property of relative normalization
(`AlgebraicGeometry.Scheme.Hom.normalizationDesc` and
`AlgebraicGeometry.Scheme.Hom.normalization.hom_ext`) applies to the two-chart model: if the generic
point of `X'` factors through an integral morphism `T ⟶ X`, then `X' ⟶ X` factors uniquely
through `T` compatibly with it.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.normalizationIso`: the isomorphism over `X` from the
  normalization of `X` in the function field of `X'` to `X'`.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.normalizationIso_hom_map`: `normalizationIso` lies over
  `X`.
* `TauCeti.AlgebraicGeometry.twoChartModel.toNormalization_normalizationIso_hom`: it is compatible
  with the generic point of `X'`.
* `TauCeti.AlgebraicGeometry.twoChartModel.normalizationIso_inv_fromNormalization` and
  `TauCeti.AlgebraicGeometry.twoChartModel.fromSpecStalk_normalizationIso_inv`: the same
  compatibilities for the inverse.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.2 and
  Appendix B.
* The Stacks Project, Tag 035H (relative normalization).
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
  (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F} (hx : x ≠ 0)
  {x' : F'} (hx' : x' ≠ 0) (h : algebraMap F F' x = x')

/-- **The two-chart model of `F'` is the normalization of the two-chart model of `F` in `F'`.** The
morphism from the relative normalization of `twoChartModel hF hx` in the function field of
`twoChartModel hF' hx'`, along the generic point composed with `map`, to `twoChartModel hF' hx'`
is an isomorphism. -/
noncomputable def normalizationIso (hxt : Transcendental k x) :
    ((twoChartModel hF' hx').fromSpecStalk (genericPoint _) ≫
      map hF hF' hx hx' h).normalization ≅ twoChartModel hF' hx' :=
  have := isFinite_map hF hF' hx hx' h hxt
  have hxt' : Transcendental k x' := by
    rw [← h]
    exact (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hxt
  -- The local rings of the model of `F'` are valuation rings, hence integrally closed.
  have := isIso_normalizationDesc_fromSpecStalk_genericPoint
    (fun p ↦ have := valuationRing_stalk (hF := hF') (hx := hx') hxt' p; inferInstance)
    (map hF hF' hx hx' h)
  asIso (Scheme.Hom.normalizationDesc _ _ (map hF hF' hx hx' h) rfl)

/-- `normalizationIso` lies over the two-chart model of `F`. -/
@[reassoc (attr := simp)]
theorem normalizationIso_hom_map (hxt : Transcendental k x) :
    (normalizationIso hF hF' hx hx' h hxt).hom ≫ map hF hF' hx hx' h =
      Scheme.Hom.fromNormalization _ :=
  have := isFinite_map hF hF' hx hx' h hxt
  Scheme.Hom.normalizationDesc_comp _ _ _ rfl

/-- `normalizationIso` carries the canonical morphism into the relative normalization to the generic
point of the two-chart model of `F'`. -/
@[reassoc (attr := simp)]
theorem toNormalization_normalizationIso_hom (hxt : Transcendental k x) :
    Scheme.Hom.toNormalization _ ≫ (normalizationIso hF hF' hx hx' h hxt).hom =
      (twoChartModel hF' hx').fromSpecStalk (genericPoint _) :=
  have := isFinite_map hF hF' hx hx' h hxt
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ rfl

/-- The inverse of `normalizationIso` lies over the two-chart model of `F`. -/
@[reassoc (attr := simp)]
theorem normalizationIso_inv_fromNormalization (hxt : Transcendental k x) :
    (normalizationIso hF hF' hx hx' h hxt).inv ≫ Scheme.Hom.fromNormalization _ =
      map hF hF' hx hx' h := by
  rw [Iso.inv_comp_eq, normalizationIso_hom_map]

/-- The inverse of `normalizationIso` carries the generic point of the two-chart model of `F'` to
the canonical morphism into the relative normalization. -/
@[reassoc (attr := simp)]
theorem fromSpecStalk_normalizationIso_inv (hxt : Transcendental k x) :
    (twoChartModel hF' hx').fromSpecStalk (genericPoint _) ≫
        (normalizationIso hF hF' hx hx' h hxt).inv =
      Scheme.Hom.toNormalization _ := by
  rw [Iso.comp_inv_eq, toNormalization_normalizationIso_hom]

end TauCeti.AlgebraicGeometry.twoChartModel
