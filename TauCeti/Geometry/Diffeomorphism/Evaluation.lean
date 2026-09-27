/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation

/-!
# Continuous evaluation of diffeomorphisms

On a compact manifold with locally compact model, the weak Whitney topology makes
the tautological action of its `C^n` diffeomorphism group continuous in both the diffeomorphism
and the point. This is the evaluation property used when the group acts on a geometric object or
when a family of diffeomorphisms is studied through its point orbits.
-/

public section

open Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] {n : ℕ∞ω} [IsManifold I n M]

/-- Diffeomorphism evaluation is continuous for the weak Whitney topology. -/
theorem continuousEval_weakWhitney : ContinuousEval (M ≃ₘ^n⟮I, I⟯ M) M M :=
  ContinuousEval.of_continuous_forget continuous_toContMDiffMap

scoped[TauCeti.DiffeomorphWeakWhitney] attribute [instance]
  Diffeomorph.continuousEval_weakWhitney

/-- Evaluation is jointly continuous in a diffeomorphism and a point for the weak Whitney
topology on the diffeomorphism group. -/
theorem continuous_eval :
    Continuous (fun p : (M ≃ₘ^n⟮I, I⟯ M) × M ↦ p.1 p.2) :=
  ContinuousEval.continuous_eval

/-- The natural action of `Diff(M)` on `M` is continuous jointly in the diffeomorphism and
the point. -/
instance applyContinuousSMul : ContinuousSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨ContinuousEval.continuous_eval⟩

end Diffeomorph
