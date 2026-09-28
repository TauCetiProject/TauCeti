/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Volume

/-!
# Metric-independent hyperbolic volume

Mostow rigidity makes the volume of a compact hyperbolic manifold independent of the chosen
complete metric of sectional curvature `-1` in dimension at least three.  The analytic proof is
outside this library, so this module records the exact volume-independence statement at the
manifold interface currently available and builds the metric-independent volume interface that
consumes it.  The bundled metric remains explicit in `hypVolumeOfMetric`; `hypVolume` is only
available together with a proof of the stated rigidity.

The formulation follows Ratcliffe, *Foundations of Hyperbolic Manifolds*, Theorem 11.8.5, and the
volume convention follows Lee, *Introduction to Riemannian Manifolds*, Chapter 2.

## Main definitions

* `MostowVolumeRigidity`: in dimension at least three, all bundled hyperbolic metrics on a compact
  manifold have the same total volume.
* `hypVolume`: the resulting metric-independent hyperbolic volume, using a chosen rigidity proof.

## Main results

* `hypVolume_eq_of_metric`: the metric-independent volume agrees with the volume of every chosen
  hyperbolic metric.
* `hypVolume_nonneg`: hyperbolic volume is nonnegative.
-/

public section

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [LindelofSpace M]

/-- The volume-independence assertion supplied by Mostow rigidity.

The dimension hypothesis is stated explicitly rather than hidden in a typeclass.  This is a
statement interface: proving it is the geometric Mostow theorem, while its consequence for the
volume API below is formal. -/
def MostowVolumeRigidity : Prop :=
  3 ≤ Module.finrank ℝ E →
    ∀ g g' : HyperbolicMetric (I := I) (M := M),
      hypVolumeOfMetric (I := I) g = hypVolumeOfMetric (I := I) g'

/-- Metric-independent hyperbolic volume, once Mostow volume-independence is available. -/
noncomputable def hypVolume (h : IsHyperbolic (I := I) (M := M))
    (hMostow : MostowVolumeRigidity (I := I) (M := M)) : ℝ :=
  let _ := hMostow
  let h' : Nonempty (HyperbolicMetric (I := I) (M := M)) := by
    exact isHyperbolic_iff_nonempty.mp h
  hypVolumeOfMetric (I := I) (Classical.choice h')

omit [T2Space (TangentBundle I M)] [LindelofSpace M] in
/-- The metric-independent volume agrees with the volume of any chosen hyperbolic metric. -/
theorem hypVolume_eq_of_metric (h : IsHyperbolic (I := I) (M := M))
    (hMostow : MostowVolumeRigidity (I := I) (M := M))
    (hDim : 3 ≤ Module.finrank ℝ E) (g : HyperbolicMetric (I := I) (M := M)) :
    hypVolume (I := I) h hMostow = hypVolumeOfMetric (I := I) g := by
  let h' : Nonempty (HyperbolicMetric (I := I) (M := M)) := by
    exact isHyperbolic_iff_nonempty.mp h
  unfold hypVolume
  exact hMostow hDim (Classical.choice h') g

omit [T2Space (TangentBundle I M)] [LindelofSpace M] in
/-- Hyperbolic volume is nonnegative. -/
theorem hypVolume_nonneg (h : IsHyperbolic (I := I) (M := M))
    (hMostow : MostowVolumeRigidity (I := I) (M := M))
    (hDim : 3 ≤ Module.finrank ℝ E) :
    0 ≤ hypVolume (I := I) h hMostow := by
  let h' : Nonempty (HyperbolicMetric (I := I) (M := M)) := by
    exact isHyperbolic_iff_nonempty.mp h
  rw [hypVolume_eq_of_metric h hMostow hDim (Classical.choice h')]
  exact hypVolumeOfMetric_nonneg (I := I) (Classical.choice h')

end TauCeti
