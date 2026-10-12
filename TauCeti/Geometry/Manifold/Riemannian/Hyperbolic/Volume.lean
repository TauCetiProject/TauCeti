/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Mostow
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total

/-!
# Volumes of hyperbolic metrics

This file connects the bundled `TauCeti.HyperbolicMetric` with the Riemannian volume API.  A
hyperbolic metric is data, so its volume is defined as the total volume of the carried Riemannian
metric.  Metric-independence is the volume consequence of Mostow rigidity, which is taken here as
the hypothesis `TauCeti.IsMostowRigid` rather than proved.

The volume construction follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Chapter 2. Metric-independence uses Mostow rigidity in J. Ratcliffe, *Foundations of Hyperbolic
Manifolds*, 3rd ed., Theorem 11.8.5.

## Main definitions

* `TauCeti.hypVolumeOfMetric`: total Riemannian volume of a bundled hyperbolic metric.
* `TauCeti.hypVolume`: the volume obtained from a hyperbolic structure; under
  `TauCeti.IsMostowRigid` this is independent of the chosen metric in dimension at least three.
-/

public section

open Bundle

open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

namespace TauCeti

variable {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [PreconnectedSpace M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [LindelofSpace M]

/-- The total Riemannian volume carried by a bundled complete constant-curvature `-1` metric. -/
noncomputable def hypVolumeOfMetric (g : HyperbolicMetric (I := I) (M := M)) : ℝ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.metric.toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  exact riemannianTotalVolume I M

omit [LindelofSpace M] in
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

omit [LindelofSpace M] in
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

omit [LindelofSpace M] in
/-- The volume is preserved by any bundled hyperbolic-metric isometry. -/
theorem hypVolumeOfMetric_eq_of_isometry
    (g g' : HyperbolicMetric (I := I) (M := M))
    (Φ : HyperbolicMetric.Isometry g g') :
    hypVolumeOfMetric (I := I) g = hypVolumeOfMetric (I := I) g' := by
  let gBundle : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.metric.toRiemannianMetric⟩
  let gCont : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  let g'Bundle : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g'.metric.toRiemannianMetric⟩
  let g'Cont : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  rw [hypVolumeOfMetric_def g, hypVolumeOfMetric_def g']
  exact @RiemannianIsometry.riemannianTotalVolume_eq E _ _ _ H _ I M _ _ _ _ _ _
    gBundle gCont H _ I M _ _ _ _ _ _ g'Bundle g'Cont Φ

omit [LindelofSpace M] in
/-- Mostow rigidity identifies the total volumes of any two bundled hyperbolic metrics. -/
theorem hypVolumeOfMetric_eq_of_mostow [BoundarylessManifold I M]
    (hConn : ConnectedSpace M)
    (hdim : 3 ≤ Module.finrank ℝ E)
    (h : IsMostowRigid (I := I) (M := M))
    (g g' : HyperbolicMetric (I := I) (M := M)) :
    hypVolumeOfMetric (I := I) g = hypVolumeOfMetric (I := I) g' := by
  let _ : ConnectedSpace M := hConn
  obtain ⟨Φ⟩ := h.isometry (hdim := hdim) g g'
  exact hypVolumeOfMetric_eq_of_isometry g g' Φ

/-! ### Metric-independent hyperbolic volume -/

/-- The hyperbolic volume of a compact manifold carrying a hyperbolic metric.

The definition chooses one bundled hyperbolic metric. On a closed connected manifold of
dimension at least three, `TauCeti.hypVolume_eq_hypVolumeOfMetric` shows that, under the
Mostow-rigidity hypothesis `TauCeti.IsMostowRigid`, the result equals the volume of every
hyperbolic metric. Mostow rigidity itself is not proved in this file. -/
noncomputable def hypVolume (h : IsHyperbolic (I := I) (M := M)) : ℝ :=
  hypVolumeOfMetric (I := I) (Classical.choice (isHyperbolic_iff.mp h))

omit [LindelofSpace M] in
/-- Hyperbolic volume is the volume of the chosen bundled hyperbolic metric. -/
theorem hypVolume_def (h : IsHyperbolic (I := I) (M := M)) :
    hypVolume (I := I) h =
      hypVolumeOfMetric (I := I) (Classical.choice (isHyperbolic_iff.mp h)) :=
  (rfl)

omit [LindelofSpace M] in
/-- The hyperbolic volume of a compact hyperbolic manifold is nonnegative. -/
theorem hypVolume_nonneg (h : IsHyperbolic (I := I) (M := M)) :
    0 ≤ hypVolume (I := I) h := by
  rw [hypVolume_def]
  exact hypVolumeOfMetric_nonneg (Classical.choice (isHyperbolic_iff.mp h))

omit [LindelofSpace M] in
/-- On a closed connected manifold of dimension at least three, Mostow rigidity makes
hyperbolic volume independent of the metric chosen in its definition. -/
theorem hypVolume_eq_hypVolumeOfMetric [BoundarylessManifold I M]
    (hConn : ConnectedSpace M)
    (hdim : 3 ≤ Module.finrank ℝ E)
    (hMostow : IsMostowRigid (I := I) (M := M))
    (h : IsHyperbolic (I := I) (M := M))
    (g : HyperbolicMetric (I := I) (M := M)) :
    hypVolume (I := I) h = hypVolumeOfMetric (I := I) g := by
  rw [hypVolume_def]
  exact hypVolumeOfMetric_eq_of_mostow hConn hdim hMostow
    (Classical.choice (isHyperbolic_iff.mp h)) g

end TauCeti
