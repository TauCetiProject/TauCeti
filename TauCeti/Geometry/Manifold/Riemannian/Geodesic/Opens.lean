/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Christoffel

/-!
# Geodesic equations on open subsets of normed spaces

For a smooth Riemannian metric on an open subset of a finite-dimensional real normed space,
this file expresses the native geodesic equation using the second-kind Christoffel map of a
coordinate bilinear-form field. The time domain need only have unique derivatives.

Adapted from the open-domain connection bridge in Yangyang Li's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/tree/b442a9f3077a4be3823b712ec92b2335dd34e771/ForTauCeti/Geometry/Manifold/Riemannian/Surface/Revolution).
-/

public noncomputable section

open Bundle FiberBundle Manifold Set TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Opens E} [RiemannianBundle (fun p : U ↦ TangentSpace 𝓘(ℝ, E) p)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun p : U ↦ TangentSpace 𝓘(ℝ, E) p)]

local notation "IP" => 𝓘(ℝ, E)

-- Avoid the expensive global smooth-to-C¹ instance search for open-subset tangent bundles.
local instance (priority := 10000) :
    IsContMDiffRiemannianBundle IP 1 E (fun p : U ↦ TangentSpace IP p) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by norm_num)

/-- On a time domain with unique derivatives, the native geodesic equation is the
second-order coordinate equation of the given metric, using derivatives within the domain. -/
theorem isGeodesicCurveOn_iff_christoffelSecondKind
    {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
      G p.val
        (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p w))
        (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p z)))
    {γ : ℝ → U} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    IsGeodesicCurveOn IP γ s ↔ ContMDiffOn 𝓘(ℝ) IP 2 γ s ∧ ∀ t ∈ s,
      derivWithin (derivWithin (fun r ↦ (γ r).val) s) s t +
        christoffelSecondKind G (γ t).val
          (derivWithin (fun r ↦ (γ r).val) s t)
          (derivWithin (fun r ↦ (γ r).val) s t) = 0 := by
  rw [isGeodesicCurveOn_iff_chart hs]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro t _
  have hchart : (extChartAt IP (γ t) ∘ γ) = fun r ↦ (γ r).val :=
    funext fun r ↦ Opens.extChartAt_opens_apply U (γ t) (γ r)
  have hLC :=
    ContMDiffNondegenerateMetric.isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection IP U
  rw [hchart, hLC.christoffelMap_opens_apply_eq_christoffelSecondKind
    (Module.finBasis ℝ E) (by simpa only [ContMDiffNondegenerateMetric.ofRiemannianBundle_apply]
      using hmetric)]

end TauCeti.Manifold
