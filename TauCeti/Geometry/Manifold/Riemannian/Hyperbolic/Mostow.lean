/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic

/-!
# Mostow rigidity for hyperbolic metrics

This file records the metric-level statement of Mostow rigidity for closed hyperbolic manifolds.
`HyperbolicMetric.Isometry` specializes the generic `RiemannianIsometry` API to two bundled
metrics, with each metric supplying its own Riemannian bundle instance.  The resulting relation
supports comparing the total volumes carried by different hyperbolic metrics.

The formulation follows Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Theorem
11.8.5.
-/

public section

open Manifold Bundle
open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

namespace TauCeti

variable {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace HyperbolicMetric

variable [PreconnectedSpace M]

/-- A bundled hyperbolic-metric comparison represented by the generic Riemannian isometry API,
with each metric supplying its own Riemannian bundle instance. -/
abbrev Isometry (g g' : HyperbolicMetric (I := I) (M := M)) :=
  @RiemannianIsometry E _ _ H _ E _ _ H _ I I M M _ _
    ⟨g.metric.toRiemannianMetric⟩ _ _ ⟨g'.metric.toRiemannianMetric⟩

end HyperbolicMetric

/-- The metric-level conclusion of Mostow rigidity for one fixed manifold and dimension.

The geometric hypotheses are carried by the typeclass parameters and `hdim`; a future
formalization of Mostow's theorem can provide this predicate from those hypotheses. -/
def IsMostowRigid : Prop :=
  ∀ [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M],
    3 ≤ Module.finrank ℝ E →
      ∀ (g g' : HyperbolicMetric (I := I) (M := M)),
        Nonempty (HyperbolicMetric.Isometry g g')

/-- Extract the isometry conclusion from a fixed-manifold Mostow-rigidity hypothesis. -/
theorem IsMostowRigid.isometry [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M]
    (h : IsMostowRigid (I := I) (M := M)) {hdim : 3 ≤ Module.finrank ℝ E}
    (g g' : HyperbolicMetric (I := I) (M := M)) :
    Nonempty (HyperbolicMetric.Isometry g g') := by
  exact h hdim g g'

/-- The Mostow rigidity theorem, universally over closed connected manifolds.

From the hyperbolicity and dimension hypotheses it gives a smooth metric-preserving
diffeomorphism between every pair of bundled complete constant-curvature `-1` metrics. -/
def MostowRigidity : Prop :=
  ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M],
    IsMostowRigid (I := I) (M := M)

end TauCeti
