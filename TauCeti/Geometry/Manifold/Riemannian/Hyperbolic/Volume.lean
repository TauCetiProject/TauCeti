/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total

/-!
# Volumes of hyperbolic metrics

This file connects the bundled `TauCeti.HyperbolicMetric` with the Riemannian volume API.  A
hyperbolic metric is data, so its volume is defined as the total volume of the carried Riemannian
metric.  Metric-independence is the volume consequence of Mostow rigidity.

The construction follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 2.

## Main definitions

* `TauCeti.hypVolumeOfMetric`: total Riemannian volume of a bundled hyperbolic metric.
-/

public section

open Bundle

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [LindelofSpace M]

/-- The total Riemannian volume carried by a bundled complete constant-curvature `-1` metric. -/
noncomputable def hypVolumeOfMetric (g : HyperbolicMetric (I := I) (M := M)) : ℝ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.metric.toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  exact riemannianTotalVolume I M

omit [T2Space (TangentBundle I M)] [LindelofSpace M] in
/-- `hypVolumeOfMetric` is the total volume for the metric carried by `g`. -/
theorem hypVolumeOfMetric_def (g : HyperbolicMetric (I := I) (M := M)) :
    hypVolumeOfMetric (I := I) g =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
          (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
      riemannianTotalVolume I M := by
  rfl

omit [T2Space (TangentBundle I M)] [LindelofSpace M] in
/-- Hyperbolic volume is nonnegative, as a total Riemannian volume. -/
theorem hypVolumeOfMetric_nonneg (g : HyperbolicMetric (I := I) (M := M)) :
    0 ≤ hypVolumeOfMetric (I := I) g := by
  unfold hypVolumeOfMetric
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.metric.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  exact riemannianTotalVolume_nonneg (I := I) (M := M)

end TauCeti
