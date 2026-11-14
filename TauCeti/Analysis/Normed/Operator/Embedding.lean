/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Reverse norm bounds for linear topological embeddings

Over a nontrivially normed field `𝕜`, a linear map `f : E →ₗ[𝕜] F` between seminormed spaces that
is a topological embedding (`Topology.IsEmbedding f`) has a continuous linear inverse on its range,
so it satisfies a reverse norm bound `‖x‖ ≤ C * ‖f x‖` for some `C > 0` and is antilipschitz. No
completeness or Hausdorffness assumption is needed.

In particular, this applies to any strict injective linear map (`Topology.IsStrictMap f` and
`Function.Injective f`), such as an injective linear map out of a finite module over a complete
Noetherian Tate ring (`LinearMap.isStrictMap_of_module_finite`).

## Main results

* `LinearMap.exists_pos_norm_le_mul_norm_of_isEmbedding`: if `f : E →ₗ[𝕜] F` is a topological
  embedding, then `∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖f x‖`.
* `LinearMap.antilipschitzWith_of_isEmbedding`: the corresponding `AntilipschitzWith` bound.
* `LinearMap.exists_pos_norm_le_mul_norm_of_isStrictMap`: the same bound for a strict injective
  linear map.
-/

public section

open Topology

namespace LinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A linear topological embedding over a nontrivially normed field is bounded below.** If
`f : E →ₗ[𝕜] F` is a topological embedding, then `‖x‖ ≤ C * ‖f x‖` for a single constant `C > 0`.
Neither space need be complete or Hausdorff. -/
theorem exists_pos_norm_le_mul_norm_of_isEmbedding (f : E →ₗ[𝕜] F) (hf : IsEmbedding f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * ‖f x‖ := by
  let e : E ≃ₗ[𝕜] LinearMap.range f := LinearEquiv.ofInjective f hf.injective
  have hsymm : Continuous e.symm.toLinearMap := by
    rw [hf.isInducing.continuous_iff]
    refine continuous_subtype_val.congr fun y ↦ ?_
    simp [Function.comp_apply, e]
  obtain ⟨C, hC, hbound⟩ := SemilinearMapClass.bound_of_continuous e.symm.toLinearMap hsymm
  refine ⟨C, hC, fun x ↦ ?_⟩
  have hx := hbound (e x)
  rwa [LinearEquiv.coe_toLinearMap, e.symm_apply_apply] at hx

/-- A linear topological embedding over a nontrivially normed field is antilipschitz. -/
theorem antilipschitzWith_of_isEmbedding (f : E →ₗ[𝕜] F) (hf : IsEmbedding f) :
    ∃ K : NNReal, 0 < K ∧ AntilipschitzWith K f := by
  obtain ⟨C, hC, hbound⟩ := f.exists_pos_norm_le_mul_norm_of_isEmbedding hf
  refine ⟨Real.toNNReal C, Real.toNNReal_pos.mpr hC, AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal C hC.le]
  exact hbound (x - y)

/-- **A strict injective linear map over a nontrivially normed field is bounded below.** -/
theorem exists_pos_norm_le_mul_norm_of_isStrictMap (f : E →ₗ[𝕜] F) (hf : IsStrictMap f)
    (hinj : Function.Injective f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * ‖f x‖ :=
  f.exists_pos_norm_le_mul_norm_of_isEmbedding
    (isEmbedding_iff_isStrictMap_injective.mpr ⟨hf, hinj⟩)

end LinearMap
