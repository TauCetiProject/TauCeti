/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic

/-!
# Isometries between hyperbolic metrics

This file specializes the generic `RiemannianIsometry` API to bundled hyperbolic metrics, with
each metric supplying its own Riemannian bundle instance.
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

/-- A bundled hyperbolic-metric comparison represented by the generic Riemannian isometry API. -/
abbrev Isometry (g g' : HyperbolicMetric (I := I) (M := M)) :=
  @RiemannianIsometry E _ _ H _ E _ _ H _ I I M M _ _
    ⟨g.metric.toRiemannianMetric⟩ _ _ ⟨g'.metric.toRiemannianMetric⟩

end HyperbolicMetric

end TauCeti
