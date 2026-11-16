/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic

/-!
# Relative volume density under pullback and restriction

Transporting two metrics through a tangent-space linear equivalence preserves their relative
volume density. In particular, pulling back by a map whose differential is bijective preserves
the density, as does restricting both metrics to an open submanifold or a closed time interval.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n n' : ℕ∞ω}

/-- Restricting both metrics to an open submanifold preserves their relative volume density. -/
@[simp]
theorem relativeVolumeDensity_restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (U : TopologicalSpace.Opens M) (x : U) :
    relativeVolumeDensity (g.restrictOpenTangentSpace U) (g'.restrictOpenTangentSpace U) x =
      relativeVolumeDensity g g' x.val := by
  rw [restrictOpenTangentSpace_eq_pullback, restrictOpenTangentSpace_eq_pullback]
  apply relativeVolumeDensity_pullback
  rw [TauCeti.Manifold.mfderiv_subtype_val]
  exact (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).surjective

/-- Restricting both metrics to a closed time interval preserves their relative volume density,
including at the endpoints. -/
@[simp]
theorem relativeVolumeDensity_restrictIcc {a b : ℝ} [Fact (a < b)]
    (g : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p))
    (g' : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n' (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)) (p : M × Set.Icc a b) :
    relativeVolumeDensity (g.restrictIcc a b) (g'.restrictIcc a b) p =
      relativeVolumeDensity g g' (p.1, p.2) := by
  rw [restrictIcc_eq_pullback, restrictIcc_eq_pullback]
  exact relativeVolumeDensity_pullback g g' _ _ _ _ p
    (TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc p).surjective

end Bundle.ContMDiffRiemannianMetric
