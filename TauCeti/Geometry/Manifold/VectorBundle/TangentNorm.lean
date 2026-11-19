/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Topology.VectorBundle.FiberNorm

/-!
# Compatible continuous tangent norms

A family of norms `ν x` on the tangent spaces of a `C¹` manifold `M` modelled on a real normed
space `E` is a family of *compatible continuous tangent norms*
(`TauCeti.IsContinuousTangentNorm I M ν`) when it is a continuous fibre norm on the tangent
bundle (`TauCeti.IsContinuousFiberNorm`): each `ν x` is comparable with the norm of `E` in the
tangent trivialization at `x`, and the norms read in a tangent trivialization vary continuously,
uniformly on the unit ball of `E`. The model space may be an infinite-dimensional Banach space,
and no smoothness of `ν` is required. The API of `TauCeti.IsContinuousFiberNorm` (independence of
the trivialization, local and compact comparison with the model norm, continuity of the
evaluation on the tangent bundle) applies.

## Main results

* `TauCeti.isContinuousTangentNorm_modelSpace`: the norm of `E`, on `E` viewed as a manifold
  modelled on itself.
* `TauCeti.isContinuousTangentNorm_norm`: the norms of a continuous Riemannian metric.

This is the norm datum of `TauCetiRoadmap/SobolevMapsBetweenManifolds/README.md`, §5.1.
-/

@[expose] public section

open Bundle
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A family of *compatible continuous tangent norms* on a `C¹` manifold: norms on the tangent
spaces forming a continuous fibre norm on the tangent bundle. -/
abbrev IsContinuousTangentNorm (ν : ∀ x : M, Seminorm ℝ (TangentSpace I x)) : Prop :=
  IsContinuousFiberNorm E (TangentSpace I : M → Type _) ν

variable (E) in
/-- On a real normed space viewed as a manifold modelled on itself, the norm of the space is a
compatible continuous tangent norm. -/
theorem isContinuousTangentNorm_modelSpace :
    IsContinuousTangentNorm 𝓘(ℝ, E) E fun _ ↦ normSeminorm ℝ E where
  exists_bounds _ := ⟨1, one_pos, 1, fun v ↦ by
    rw [TangentBundle.symmL_model_space]
    change 1 * ‖v‖ ≤ ‖v‖ ∧ ‖v‖ ≤ 1 * ‖v‖
    simp⟩
  eventually_abs_sub_le _ _ hε := Filter.Eventually.of_forall fun _ v ↦ by
    rw [TangentBundle.symmL_model_space, TangentBundle.symmL_model_space]
    change |‖v‖ - ‖v‖| ≤ _
    rw [sub_self, abs_zero]
    positivity

/-- The norms of a continuous Riemannian metric on a `C¹` manifold are compatible continuous
tangent norms. -/
theorem isContinuousTangentNorm_norm [RiemannianBundle fun x : M ↦ TangentSpace I x]
    [IsContinuousRiemannianBundle E fun x : M ↦ TangentSpace I x] :
    IsContinuousTangentNorm I M fun x ↦ normSeminorm ℝ (TangentSpace I x) :=
  isContinuousFiberNorm_norm E fun x : M ↦ TangentSpace I x

end TauCeti
