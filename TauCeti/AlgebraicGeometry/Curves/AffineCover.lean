/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

/-!
# Two affine opens covering a regular proper curve

A regular proper integral curve over a field is covered by two affine opens. Indeed, a
transcendental rational function identifies the curve with the two-chart model of its function
field, and the two normalization charts pull back to the required opens.

The result is also stated directly for smooth proper geometrically connected curves of relative
dimension one. It requires neither a rational point nor a perfect base field. The cover is the
geometric input for computing quasi-coherent cohomology by the two-open Mayer–Vietoris sequence;
the intersection is affine because a proper curve is separated.

The construction uses `Scheme.isoTwoChartModel` and the two affine charts of `twoChartModel`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter I, Theorem 6.9 and Corollary 6.12
  (proper nonsingular curves and their function fields).
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- A proper integral curve whose codimension-one local rings are discrete valuation rings is
covered by two affine open subsets. -/
theorem exists_two_affine_opens (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))] :
    ∃ U V : X.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  obtain ⟨x, hx⟩ := (IsCurveOver.isFunctionField (k := k) (X := X)).exists_transcendental
  let hF := IsCurveOver.isFunctionField (k := k) (X := X)
  let e := X.isoTwoChartModel hx.ne_zero hx
  let U := (twoChartModel.ιFinite hF hx.ne_zero).opensRange
  let V := (twoChartModel.ιInfinity hF hx.ne_zero).opensRange
  have hUV : U ⊔ V = ⊤ := by
    apply TopologicalSpace.Opens.ext
    exact twoChartModel.range_ιFinite_union_range_ιInfinity hF hx.ne_zero
  refine ⟨e.hom ⁻¹ᵁ U, e.hom ⁻¹ᵁ V,
    (isAffineOpen_opensRange _).preimage_of_isIso e.hom,
    (isAffineOpen_opensRange _).preimage_of_isIso e.hom, ?_⟩
  rw [← Hom.preimage_sup, hUV, Hom.preimage_top]

/-- A smooth proper geometrically connected curve over any field admits a cover by two affine
open subsets, without a rational-point hypothesis. -/
theorem exists_two_affine_opens_of_smooth (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] :
    ∃ U V : X.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : X.IsCurveOver k :=
    { topologicalKrullDim_eq_one :=
        topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) }
  exact X.exists_two_affine_opens (k := k)

end AlgebraicGeometry.Scheme
