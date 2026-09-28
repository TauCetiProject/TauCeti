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
hyperbolic metric is data, so its volume is first defined as the total volume of the carried
Riemannian metric.  The metric-independent `hypVolume` is then obtained by choosing a hyperbolic
metric; its independence is exposed as the separate proposition `HyperbolicVolumeIndependent`.
This separation leaves Mostow rigidity as the theorem that supplies that proposition, rather than
silently making a choice of metric part of the definition.

The construction follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 2;
the volume-independence statement is the volume consequence of Mostow rigidity.  No external
formalization is vendored here.

## Main definitions

* `TauCeti.hypVolumeOfMetric`: total Riemannian volume of a bundled hyperbolic metric.
* `TauCeti.HyperbolicVolumeIndependent`: all bundled hyperbolic metrics have the same volume.
* `TauCeti.hypVolume`: the volume obtained from a chosen hyperbolic metric.

## Main results

* `TauCeti.hypVolumeOfMetric_eq_of_hyperbolicVolumeIndependent` proves choice-independence under
  the Mostow-volume proposition.
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

/-- The volume consequence of Mostow rigidity: hyperbolic metrics on `M` have equal volume. -/
def HyperbolicVolumeIndependent : Prop :=
  ∀ g g' : HyperbolicMetric (I := I) (M := M),
    hypVolumeOfMetric (I := I) g = hypVolumeOfMetric (I := I) g'

/-- The volume of a hyperbolic manifold, obtained by choosing one bundled hyperbolic metric. -/
noncomputable def hypVolume
    (h : Nonempty (HyperbolicMetric (I := I) (M := M))) : ℝ :=
  hypVolumeOfMetric (I := I) (Classical.choice h)

omit [T2Space (TangentBundle I M)] [LindelofSpace M] in
/-- Any hyperbolic metric has the chosen `hypVolume` when volumes are Mostow-independent. -/
theorem hypVolumeOfMetric_eq_of_hyperbolicVolumeIndependent
    (h : Nonempty (HyperbolicMetric (I := I) (M := M)))
    (hind : HyperbolicVolumeIndependent (I := I) (M := M))
    (g : HyperbolicMetric (I := I) (M := M)) :
    hypVolumeOfMetric (I := I) g = hypVolume h := by
  exact hind g (Classical.choice h)

end TauCeti
