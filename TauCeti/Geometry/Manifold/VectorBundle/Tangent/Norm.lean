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
    -- The seminorm and the identity `1` act on the tangent space `TangentSpace 𝓘(ℝ, E) x`, a type
    -- synonym for `E` through which `coe_normSeminorm` and the simp lemmas for `1` do not apply;
    -- by definition the goal is the following one about `E`.
    change 1 * ‖v‖ ≤ ‖v‖ ∧ ‖v‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact ⟨le_rfl, le_rfl⟩⟩
  eventually_abs_sub_le b₀ ε hε := Filter.Eventually.of_forall fun b v ↦ by
    rw [TangentBundle.symmL_model_space, TangentBundle.symmL_model_space]
    -- As above, on the tangent spaces at `b` and `b₀`, both type synonyms for `E`, the goal is by
    -- definition the following one about `E`.
    change |‖v‖ - ‖v‖| ≤ ε * ‖v‖
    rw [sub_self, abs_zero]
    positivity

/-- The norms of a continuous Riemannian metric on a `C¹` manifold are compatible continuous
tangent norms. -/
theorem isContinuousTangentNorm_norm [RiemannianBundle fun x : M ↦ TangentSpace I x]
    [IsContinuousRiemannianBundle E fun x : M ↦ TangentSpace I x] :
    IsContinuousTangentNorm I M fun x ↦ normSeminorm ℝ (TangentSpace I x) :=
  isContinuousFiberNorm_norm E fun x : M ↦ TangentSpace I x

end TauCeti
