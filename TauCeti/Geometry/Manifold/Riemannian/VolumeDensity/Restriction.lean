/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic

/-!
# Relative volume density under restriction

This file proves that restricting both metrics to an open submanifold or to `M × [a, b]`
preserves their relative volume density, including at the interval endpoints. These identities
localize relative-volume comparisons to open submanifolds and restrict metric families on
`M × ℝ` to closed slabs `M × [a, b]` with boundary.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace Bundle.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Restricting both metrics to an open submanifold preserves their relative volume density. -/
@[simp]
theorem relativeVolumeDensity_restrictOpenTangentSpace
    (g g' : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (U : TopologicalSpace.Opens M) (x : U) :
    relativeVolumeDensity (g.restrictOpenTangentSpace U) (g'.restrictOpenTangentSpace U) x =
      relativeVolumeDensity g g' x.val := by
  exact relativeVolumeDensity_eq_of_linearEquiv _ _ g g'
    (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv
    (fun v w ↦ restrictOpenTangentSpace_inner g U x v w)
    (fun v w ↦ restrictOpenTangentSpace_inner g' U x v w)

end Bundle.RiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

open Bundle.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n n' : ℕ∞ω}

/-- Restricting both metrics to a closed time interval preserves their relative volume density,
including at the endpoints. -/
@[simp]
theorem relativeVolumeDensity_restrictIcc {a b : ℝ} [Fact (a < b)]
    (g : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p))
    (g' : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n' (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)) (p : M × Set.Icc a b) :
    relativeVolumeDensity (g.restrictIcc a b).toRiemannianMetric
      (g'.restrictIcc a b).toRiemannianMetric p =
      relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric (p.1, p.2) := by
  rw [restrictIcc_eq_pullback, restrictIcc_eq_pullback]
  exact relativeVolumeDensity_pullback g g' _ _ _ _ p
    (TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc p).surjective

end Bundle.ContMDiffRiemannianMetric
