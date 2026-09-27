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

On a compact boundaryless manifold with locally compact model, the weak Whitney topology makes
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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] {n : ℕ∞ω} [IsManifold I n M]

/-- Evaluation is jointly continuous in a diffeomorphism and a point for the weak Whitney
topology on the diffeomorphism group. -/
theorem continuous_eval :
    Continuous (fun p : (M ≃ₘ^n⟮I, I⟯ M) × M ↦ p.1 p.2) := by
  have h : Continuous (fun p : (M ≃ₘ^n⟮I, I⟯ M) × M ↦
      ((p.1.toContMDiffMap : C^n⟮I, M; I, M⟯), p.2)) :=
    (continuous_toContMDiffMap.comp continuous_fst).prodMk continuous_snd
  exact ContMDiffMap.continuous_eval_manifoldWeakWhitney_joint.comp h

/-- The natural action of `Diff(M)` on `M` is continuous jointly in the diffeomorphism and
the point. -/
instance applyContinuousSMul : ContinuousSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨continuous_eval⟩

end Diffeomorph
