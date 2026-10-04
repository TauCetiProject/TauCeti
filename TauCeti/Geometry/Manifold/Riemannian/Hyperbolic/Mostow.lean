/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic

/-!
# Mostow rigidity for hyperbolic metrics

This file records the metric-level statement of Mostow rigidity for closed hyperbolic manifolds.
`HyperbolicMetric.Isometry` specializes the generic `RiemannianIsometry` API to two bundled
metrics, with each metric supplying its own Riemannian bundle instance.
`MostowRigidity` states that every pair of such metrics is related by one once the manifold
is known to be hyperbolic and to have dimension at least three.  The explicit comparison is
needed because `RiemannianIsometry` stores its metric in a typeclass, whereas a Mostow statement
compares the two metric fields carried by `HyperbolicMetric`.

The formulation follows Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Theorem
11.8.5.  The rigidity proposition is stated here; its geometric proof will supply the
metric-independent hyperbolic volume used by the later Weeks-manifold target.
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
  [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M]

namespace HyperbolicMetric

/-- A bundled hyperbolic-metric comparison represented by the generic Riemannian isometry API,
with each metric supplying its own Riemannian bundle instance. -/
abbrev Isometry (g g' : HyperbolicMetric (I := I) (M := M)) :=
  @RiemannianIsometry E _ _ H _ E _ _ H _ I I M M _ _
    ⟨g.metric.toRiemannianMetric⟩ _ _ ⟨g'.metric.toRiemannianMetric⟩

end HyperbolicMetric

/-- The Mostow rigidity theorem, universally over closed connected manifolds.

From the hyperbolicity and dimension hypotheses it gives a smooth metric-preserving
diffeomorphism between every pair of bundled complete constant-curvature `-1` metrics. -/
def MostowRigidity : Prop :=
  ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M],
    IsHyperbolic (I := I) (M := M) →
      3 ≤ Module.finrank ℝ E →
        ∀ (g g' : HyperbolicMetric (I := I) (M := M)),
          Nonempty (HyperbolicMetric.Isometry g g')

/-- The Mostow rigidity theorem supplies an isometry from its geometric hypotheses. -/
theorem MostowRigidity.isometry (h : MostowRigidity.{uE, uH, uM})
    (hM : IsHyperbolic (I := I) (M := M)) (hdim : 3 ≤ Module.finrank ℝ E)
    (g g' : HyperbolicMetric (I := I) (M := M)) :
    Nonempty (HyperbolicMetric.Isometry g g') :=
  h (E := E) (H := H) (M := M) (I := I) hM hdim g g'

end TauCeti
