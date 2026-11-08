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

On a compact source manifold with locally compact model, the weak Whitney topology makes
evaluation of `C^n` diffeomorphisms continuous in both the diffeomorphism and the point.
For self-diffeomorphisms this gives continuity of the tautological action.
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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]

/-- Diffeomorphism evaluation is continuous for the weak Whitney topology. -/
theorem continuousEval_weakWhitney : ContinuousEval (M ≃ₘ^n⟮I, J⟯ N) M N :=
  ContinuousEval.of_continuous_forget continuous_toContMDiffMap

scoped[TauCeti.DiffeomorphWeakWhitney] attribute [instance]
  Diffeomorph.continuousEval_weakWhitney

/-- The natural action of `Diff(M)` on `M` is continuous jointly in the diffeomorphism and
the point. -/
theorem applyContinuousSMul : ContinuousSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨ContinuousEval.continuous_eval⟩

scoped[TauCeti.DiffeomorphWeakWhitney] attribute [instance]
  Diffeomorph.applyContinuousSMul

end Diffeomorph
