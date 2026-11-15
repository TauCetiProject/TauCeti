/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Exact operator norms on inner product tensor products

Mathlib's `TensorProduct.norm_mapL_le`, `ContinuousLinearMap.norm_rTensor_le` and
`ContinuousLinearMap.norm_lTensor_le` bound the operator norms of `f ⊗ g`, `f ⊗ 1` and `1 ⊗ g`
from above. Evaluating on pure tensors `x ⊗ₜ y`, where the inner-product tensor norm is
multiplicative (`‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`), gives the matching lower bounds, so
`‖mapL f g‖ = ‖f‖ * ‖g‖` unconditionally and `‖f.rTensor G‖ = ‖f‖`, `‖g.lTensor G‖ = ‖g‖` whenever
the passive factor `G` is nontrivial (while both amplifications vanish when `G` is subsingleton).

## Main results

* `TensorProduct.norm_mapL`: `‖mapL f g‖ = ‖f‖ * ‖g‖`.
* `ContinuousLinearMap.norm_rTensor` and `ContinuousLinearMap.norm_lTensor`: when `G` is
  nontrivial, `‖f.rTensor G‖ = ‖f‖` and `‖g.lTensor G‖ = ‖g‖`.
* `ContinuousLinearMap.rTensorₗᵢ` and `ContinuousLinearMap.lTensorₗᵢ`: when `G` is nontrivial,
  `f ↦ f.rTensor G` and `g ↦ g.lTensor G` bundled as linear isometries.
* `ContinuousLinearMap.rTensor_eq_zero` and `ContinuousLinearMap.lTensor_eq_zero`: when `G` is
  subsingleton, `f.rTensor G = 0` and `g.lTensor G = 0`.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The operator norm of `f ⊗ g` on the inner-product tensor product is the product of the
operator norms of `f` and `g`. -/
@[simp]
theorem norm_mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) : ‖mapL f g‖ = ‖f‖ * ‖g‖ := by
  refine le_antisymm (norm_mapL_le f g) ?_
  have hpoint (x : E) (y : G) : ‖f x‖ * ‖g y‖ ≤ ‖mapL f g‖ * ‖x‖ * ‖y‖ := by
    calc ‖f x‖ * ‖g y‖ = ‖mapL f g (x ⊗ₜ[𝕜] y)‖ := by rw [mapL_tmul, norm_tmul]
      _ ≤ ‖mapL f g‖ * ‖x ⊗ₜ[𝕜] y‖ := (mapL f g).le_opNorm _
      _ = ‖mapL f g‖ * ‖x‖ * ‖y‖ := by rw [norm_tmul, mul_assoc]
  have hy (y : G) : ‖f‖ * ‖g y‖ ≤ ‖mapL f g‖ * ‖y‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (g y)) with hgy | hgy
    · rw [← hgy, mul_zero]
      positivity
    · rw [← le_div_iff₀ hgy]
      refine f.opNorm_le_bound (by positivity) fun x ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hgy]
      linarith [hpoint x y]
  rcases eq_or_lt_of_le (norm_nonneg f) with hf | hf
  · rw [← hf, zero_mul]
    exact norm_nonneg _
  · rw [mul_comm, ← le_div_iff₀ hf]
    refine g.opNorm_le_bound (by positivity) fun y ↦ ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hf]
    linarith [hy y]

end TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Tensoring on the right with the identity of a nontrivial inner product space preserves the
operator norm. -/
@[simp]
theorem norm_rTensor [Nontrivial G] (f : E →L[𝕜] F) : ‖f.rTensor G‖ = ‖f‖ := by
  rw [rTensor_eq_mapL, TensorProduct.norm_mapL, norm_id, mul_one]

/-- Tensoring on the left with the identity of a nontrivial inner product space preserves the
operator norm. -/
@[simp]
theorem norm_lTensor [Nontrivial G] (f : E →L[𝕜] F) : ‖f.lTensor G‖ = ‖f‖ := by
  rw [lTensor_eq_mapL, TensorProduct.norm_mapL, norm_id, one_mul]

variable (𝕜 E F G) in
/-- Tensoring on the right with the identity of a nontrivial inner product space, bundled as a
linear isometry. -/
noncomputable def rTensorₗᵢ [Nontrivial G] : (E →L[𝕜] F) →ₗᵢ[𝕜] ((E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] G)) where
  toLinearMap :=
    { toFun := fun f ↦ f.rTensor G
      map_add' := rTensor_add G
      map_smul' := rTensor_smul G }
  norm_map' := norm_rTensor

@[simp]
theorem rTensorₗᵢ_apply [Nontrivial G] (f : E →L[𝕜] F) : rTensorₗᵢ 𝕜 E F G f = f.rTensor G :=
  (rfl)

variable (𝕜 E F G) in
/-- Tensoring on the left with the identity of a nontrivial inner product space, bundled as a
linear isometry. -/
noncomputable def lTensorₗᵢ [Nontrivial G] : (E →L[𝕜] F) →ₗᵢ[𝕜] ((G ⊗[𝕜] E) →L[𝕜] (G ⊗[𝕜] F)) where
  toLinearMap :=
    { toFun := fun f ↦ f.lTensor G
      map_add' := lTensor_add G
      map_smul' := lTensor_smul G }
  norm_map' := norm_lTensor

@[simp]
theorem lTensorₗᵢ_apply [Nontrivial G] (f : E →L[𝕜] F) : lTensorₗᵢ 𝕜 E F G f = f.lTensor G :=
  (rfl)

/-- Tensoring on the right with the identity of a nontrivial inner product space is injective. -/
theorem rTensor_injective (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Nontrivial G] : Function.Injective (fun f : E →L[𝕜] F ↦ f.rTensor G) :=
  (rTensorₗᵢ 𝕜 E F G).injective

/-- Tensoring on the left with the identity of a nontrivial inner product space is injective. -/
theorem lTensor_injective (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Nontrivial G] : Function.Injective (fun f : E →L[𝕜] F ↦ f.lTensor G) :=
  (lTensorₗᵢ 𝕜 E F G).injective

/-- Tensoring on the right with a subsingleton space produces the zero operator. -/
@[simp]
theorem rTensor_eq_zero [Subsingleton G] (f : E →L[𝕜] F) : f.rTensor G = 0 :=
  Subsingleton.elim _ _

/-- Tensoring on the left with a subsingleton space produces the zero operator. -/
@[simp]
theorem lTensor_eq_zero [Subsingleton G] (f : E →L[𝕜] F) : f.lTensor G = 0 :=
  Subsingleton.elim _ _

end ContinuousLinearMap
