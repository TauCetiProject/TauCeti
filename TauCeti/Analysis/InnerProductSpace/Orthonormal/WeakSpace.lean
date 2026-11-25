/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Orthonormal families converge weakly to zero

Let `v` be an orthonormal family in an inner product space `E`. By Bessel's inequality the
coefficients `⟪v i, x⟫` are square summable, so they tend to `0` along the cofinite filter
(`Orthonormal.tendsto_inner_cofinite`). Every continuous linear functional extends to the
completion of `E`, where it is `⟪y, ·⟫` for some `y` (Riesz), so `v` tends to `0` in the weak
topology (`Orthonormal.tendsto_toWeakSpace_cofinite`); for a sequence this is `eₙ ⇀ 0`
(`Orthonormal.tendsto_toWeakSpace_atTop`). Since `‖eₙ‖ = 1`, the convergence is not in norm: the
unit sphere of an infinite-dimensional inner product space is not weakly sequentially closed,
and the norm is not weakly continuous.

## Main results

* `Orthonormal.tendsto_inner_cofinite`: `⟪v i, x⟫ → 0` along the cofinite filter.
* `Orthonormal.tendsto_toWeakSpace_cofinite`, `Orthonormal.tendsto_toWeakSpace_atTop`: an
  orthonormal family tends weakly to `0`.
-/

public section

open Filter
open scoped InnerProductSpace Topology

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {v : ι → E}

/-- **The coefficients of a vector along an orthonormal family tend to zero.** By Bessel's
inequality `⟪v i, x⟫ → 0` along the cofinite filter. -/
theorem tendsto_inner_cofinite (hv : Orthonormal 𝕜 v) (x : E) :
    Tendsto (fun i ↦ ⟪v i, x⟫_𝕜) cofinite (𝓝 0) := by
  have h := (hv.inner_products_summable x).tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h2 : Tendsto (fun r : ℝ ↦ √r) (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto 0
  exact (h2.comp h).congr fun i ↦ by simp [Real.sqrt_sq (norm_nonneg _)]

/-- **An orthonormal family tends weakly to zero.** An orthonormal family in an inner product space
(not necessarily complete) satisfies `v i ⇀ 0` along the cofinite filter. -/
theorem tendsto_toWeakSpace_cofinite (hv : Orthonormal 𝕜 v) :
    Tendsto (fun i ↦ toWeakSpace 𝕜 E (v i)) cofinite (𝓝 (toWeakSpace 𝕜 E 0)) := by
  open UniformSpace in
  refine TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.2 fun f ↦ ?_
  let ι : E →L[𝕜] Completion E := Completion.toComplL
  let F : StrongDual 𝕜 (Completion E) := f.extend ι
  have hF (x : E) : F x = f x :=
    f.extend_eq (e := ι) Completion.denseRange_coe (Completion.isUniformInducing_coe E) x
  have hw := hv.comp_linearIsometry (Completion.toComplₗᵢ (𝕜 := 𝕜))
  have h := (hw.tendsto_inner_cofinite ((InnerProductSpace.toDual 𝕜 (Completion E)).symm F)).star
  rw [star_zero] at h
  rw [map_zero]
  refine h.congr fun i ↦ ?_
  rw [← hF, ← InnerProductSpace.toDual_symm_apply]
  exact inner_conj_symm _ _

/-- **An orthonormal sequence tends weakly to zero.** An orthonormal sequence `eₙ` in an inner
product space satisfies `eₙ ⇀ 0`. -/
theorem tendsto_toWeakSpace_atTop {e : ℕ → E} (he : Orthonormal 𝕜 e) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 E (e n)) atTop (𝓝 (toWeakSpace 𝕜 E 0)) :=
  Nat.cofinite_eq_atTop ▸ he.tendsto_toWeakSpace_cofinite

end Orthonormal
