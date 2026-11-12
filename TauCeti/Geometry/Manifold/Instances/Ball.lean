/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# The manifold structure on an open ball

An open ball in a pseudometric charted space inherits the open-subset atlas and any manifold
structure. In particular a complex disc, written with its usual subtype rather than as a bundled
open set, is a complex manifold.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {H M : Type*} [TopologicalSpace H] [PseudoMetricSpace M] [ChartedSpace H M]

/-- An open ball has the atlas induced from its ambient charted space. -/
noncomputable instance instChartedSpaceBall (c : M) (r : ℝ) : ChartedSpace H (Metric.ball c r) :=
  inferInstanceAs (ChartedSpace H
    (⟨Metric.ball c r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens M))

/-- The induced atlas makes an open ball in a manifold a manifold with the same model. -/
instance instIsManifoldBall {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n M]
    (c : M) (r : ℝ) : IsManifold I n (Metric.ball c r) :=
  inferInstanceAs (IsManifold I n
    (⟨Metric.ball c r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens M))

end TauCeti
