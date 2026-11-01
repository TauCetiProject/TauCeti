/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Normed.Group.Completion

/-!
# Operator norms of bounded maps extended to completions

A bounded semilinear map `f : E →SL[σ₁₂] F` between seminormed spaces extends to the bounded
map `f.completion` between the completions, and, when `F` is complete and Hausdorff, to the
bounded map `f.fromCompletion` from the completion of `E` to `F`. Since `E` has dense image in
its completion and the canonical map preserves norms, neither extension changes the operator norm.

These are the continuous semilinear analogues of Mathlib's `NormedAddGroupHom.norm_completion`.
They make extension to completions an isometric operation, as needed for the norm-preserving
universal properties of completed normed constructions. Likewise, a linear isometric equivalence
extends to the linear isometric equivalence `e.completion` between the completions, the analogue
for equivalences of Mathlib's `LinearIsometry.completion`.

Extension to completions also preserves metric quotient maps. If `f` lifts every vector of norm
less than `r` to a vector of norm less than `r`, so does `f.completion`. Combined with
`ContinuousLinearMap.norm_completion`, an operator of norm at most one that maps each open ball
about `0` onto the open ball of the same radius extends to an operator with the same property.
The lifts in the completion are sums of absolutely convergent series of lifts of the terms of
the series provided by `UniformSpace.Completion.exists_hasSum_coe_of_norm_lt`.

## Main results

* `ContinuousLinearMap.norm_completion`: `‖f.completion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_fromCompletion`: `‖f.fromCompletion‖ = ‖f‖`.
* `ContinuousLinearMap.ball_subset_image_completion_ball` and
  `ContinuousLinearMap.image_completion_ball`: the extension of a metric quotient map to the
  completions is a metric quotient map.
* `LinearIsometryEquiv.completion`: the extension of a linear isometric equivalence to the
  completions.
* `LinearIsometryEquiv.toLinearIsometry_completion`: as a linear isometry, it is
  `LinearIsometry.completion`.
* `LinearIsometryEquiv.completion_symm`, `LinearIsometryEquiv.completion_refl`,
  `LinearIsometryEquiv.completion_trans`: extension to completions is compatible with inverses,
  identities and composites.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Extending a bounded semilinear map to the completions of its domain and codomain preserves
its operator norm. -/
@[simp]
theorem norm_completion (f : E →SL[σ₁₂] F) : ‖f.completion‖ = ‖f‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun x ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [completion_apply_coe, Completion.norm_coe] using f.le_opNorm x
  · simpa only [completion_apply_coe, Completion.norm_coe] using f.completion.le_opNorm x

/-- Extending a bounded semilinear map into a complete Hausdorff space to the completion of its
domain preserves its operator norm. -/
@[simp]
theorem norm_fromCompletion [T0Space F] [CompleteSpace F] (f : E →SL[σ₁₂] F) :
    ‖f.fromCompletion‖ = ‖f‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun x ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [fromCompletion_apply_coe, Completion.norm_coe] using f.le_opNorm x
  · simpa only [fromCompletion_apply_coe, Completion.norm_coe] using f.fromCompletion.le_opNorm x

omit [RingHomIsometric σ₁₂] in
/-- If `f` lifts every vector of norm less than `r` to a vector of norm less than `r`, then so
does its extension `f.completion` to the completions. -/
theorem ball_subset_image_completion_ball {f : E →SL[σ₁₂] F}
    (hf : ∀ r, Metric.ball (0 : F) r ⊆ f '' Metric.ball 0 r) (r : ℝ) :
    Metric.ball (0 : Completion F) r ⊆ f.completion '' Metric.ball 0 r := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  -- Write `w` as an absolutely convergent series of points of `F`, with total norm below `r`.
  obtain ⟨v, hv, hvs, hvr⟩ := Completion.exists_hasSum_coe_of_norm_lt w hw
  set δ := r - ∑' n, ‖v n‖ with hδ_def
  have hδ : 0 < δ := sub_pos.2 hvr
  -- Lift the terms, losing at most `δ / 2 / 2 ^ n` in norm on the `n`-th term.
  have hlift (n : ℕ) : ∃ x : E, f x = v n ∧ ‖x‖ < ‖v n‖ + δ / 2 / 2 ^ n := by
    obtain ⟨x, hx, hfx⟩ := hf _ (mem_ball_zero_iff.2 (lt_add_of_pos_right ‖v n‖
      (by positivity : 0 < δ / 2 / 2 ^ n)))
    exact ⟨x, hfx, mem_ball_zero_iff.1 hx⟩
  choose x hfx hx using hlift
  have hg : HasSum (fun n ↦ ‖v n‖ + δ / 2 / 2 ^ n) (∑' n, ‖v n‖ + δ) :=
    hvs.hasSum.add (hasSum_geometric_two' δ)
  have hxs : Summable fun n ↦ ‖(x n : Completion E)‖ := by
    simpa only [Completion.norm_coe] using
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ (hx n).le) hg.summable
  refine ⟨∑' n, (x n : Completion E), mem_ball_zero_iff.2 ?_, ?_⟩
  · calc ‖∑' n, (x n : Completion E)‖ ≤ ∑' n, ‖(x n : Completion E)‖ :=
          norm_tsum_le_tsum_norm hxs
      _ < ∑' n, ‖v n‖ + δ := hasSum_lt (fun n ↦ by simpa using (hx n).le)
          (i := 0) (by simpa using hx 0) hxs.hasSum hg
      _ = r := by rw [hδ_def]; ring
  · have h := (hxs.of_norm.hasSum.map f.completion f.completion.continuous)
    simp only [Function.comp_def, completion_apply_coe, hfx] at h
    exact h.unique hv

/-- The extension to the completions of a **metric quotient map** is a metric quotient map: if
`‖f‖ ≤ 1` and `f` lifts every vector of norm less than `r` to a vector of norm less than `r`,
then `f.completion` maps each open ball about `0` onto the open ball of the same radius. -/
theorem image_completion_ball {f : E →SL[σ₁₂] F} (hf₁ : ‖f‖ ≤ 1)
    (hf : ∀ r, Metric.ball (0 : F) r ⊆ f '' Metric.ball 0 r) (r : ℝ) :
    f.completion '' Metric.ball 0 r = Metric.ball 0 r := by
  refine subset_antisymm ?_ (ball_subset_image_completion_ball hf r)
  have h : ‖f.completion‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_one, coe_nnnorm, norm_completion]
    exact hf₁
  simpa using ((f.completion.lipschitzWith.weaken h).mapsTo_ball one_ne_zero 0 r).image_subset

end ContinuousLinearMap

namespace LinearIsometryEquiv

variable {𝕜 𝕜₂ E F : Type*} [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Extend a linear isometric equivalence `e : E ≃ₛₗᵢ[σ₁₂] F` to a linear isometric equivalence
between the completions of `E` and `F`. -/
noncomputable def completion (e : E ≃ₛₗᵢ[σ₁₂] F) : Completion E ≃ₛₗᵢ[σ₁₂] Completion F :=
  e.toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap
    Completion.toComplₗᵢ.toLinearMap Completion.denseRange_coe Completion.denseRange_coe
    fun x ↦ by simp

/-- On `E`, the extension of `e` to the completions is `e`. -/
@[simp]
theorem completion_apply_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (x : E) : e.completion x = e x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- On `F`, the inverse of the extension of `e` to the completions is `e.symm`. -/
theorem completion_symm_apply_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (y : F) :
    e.completion.symm y = e.symm y :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ y

/-- The extension of `e` to the completions is `UniformSpace.Completion.map e`. -/
@[simp low]
theorem coe_completion (e : E ≃ₛₗᵢ[σ₁₂] F) : ⇑e.completion = Completion.map e :=
  Completion.ext e.completion.continuous Completion.continuous_map fun x ↦ by
    rw [completion_apply_coe, Completion.map_coe e.isometry.uniformContinuous]

/-- The inverse of the extension of `e` to the completions is the extension of `e.symm`. -/
@[simp]
theorem completion_symm (e : E ≃ₛₗᵢ[σ₁₂] F) : e.completion.symm = e.symm.completion := by
  ext y
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq e.completion.symm.continuous e.symm.completion.continuous
  | ih y => rw [completion_symm_apply_coe, completion_apply_coe]

variable (𝕜 E) in
/-- The extension of the identity to the completion is the identity. -/
@[simp]
theorem completion_refl :
    (LinearIsometryEquiv.refl 𝕜 E).completion = LinearIsometryEquiv.refl 𝕜 (Completion E) := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (LinearIsometryEquiv.refl 𝕜 E).completion.continuous continuous_id
  | ih x => simp

/-- Extending a composite of linear isometric equivalences to the completions is the composite
of their extensions. -/
@[simp]
theorem completion_trans {𝕜₃ G : Type*} [NormedField 𝕜₃] [SeminormedAddCommGroup G]
    [NormedSpace 𝕜₃ G] {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₃₂ : 𝕜₃ →+* 𝕜₂} {σ₁₃ : 𝕜 →+* 𝕜₃}
    {σ₃₁ : 𝕜₃ →+* 𝕜} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] (e : E ≃ₛₗᵢ[σ₁₂] F) (e' : F ≃ₛₗᵢ[σ₂₃] G) :
    (e.trans e').completion = e.completion.trans e'.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (e.trans e').completion.continuous
      (e.completion.trans e'.completion).continuous
  | ih x => simp

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- As a linear isometry, the extension of `e` to the completions is the extension
`LinearIsometry.completion` of `e` viewed as a linear isometry. -/
@[simp]
theorem toLinearIsometry_completion (e : E ≃ₛₗᵢ[σ₁₂] F) :
    e.completion.toLinearIsometry = e.toLinearIsometry.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq e.completion.continuous e.toLinearIsometry.completion.continuous
  | ih x => simp [LinearIsometry.completion_apply_coe]

end NormedAddCommGroup

end LinearIsometryEquiv
