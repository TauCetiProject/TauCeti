/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# The manifold structure on an open ball

An open ball in a normed vector space inherits the open-subset atlas. In particular a complex
disc, written with its usual subtype rather than as a bundled open set, is a complex manifold.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- An open ball has the atlas induced from its ambient normed space. -/
noncomputable instance instChartedSpaceBall (c : E) (r : ℝ) : ChartedSpace E (Metric.ball c r) :=
  inferInstanceAs (ChartedSpace E
    (⟨Metric.ball c r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens E))

/-- The induced atlas makes an open ball a manifold over the ambient scalar field. -/
instance instIsManifoldBall {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    (c : E) (r : ℝ) (n : ℕ∞ω) : IsManifold 𝓘(𝕜, E) n (Metric.ball c r) :=
  inferInstanceAs (IsManifold 𝓘(𝕜, E) n
    (⟨Metric.ball c r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens E))

/-- Open balls in a locally compact normed group are locally compact. -/
instance instLocallyCompactSpaceBall [LocallyCompactSpace E] (c : E) (r : ℝ) :
    LocallyCompactSpace (Metric.ball c r) := Metric.isOpen_ball.locallyCompactSpace

end TauCeti
