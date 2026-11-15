/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Exact operator norms and dense range on inner product tensor products

Mathlib establishes only the upper bounds `TensorProduct.norm_mapL_le`,
`ContinuousLinearMap.norm_rTensor_le`, and `ContinuousLinearMap.norm_lTensor_le` on the algebraic
inner-product tensor product `E ⊗[𝕜] F`. Because the inner-product norm is a cross-norm
(`‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`), tensoring bounded operators preserves exact operator norms, making
amplification onto a nontrivial factor isometric and transferring directly to completed Hilbert
tensor products via `ContinuousLinearMap.norm_completion`. Together with preservation of
nontriviality and dense range, this underpins the completed amplifications, partial-completion
equivalences, and associator in `TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion`.

* `TensorProduct.instNontrivial`: `E ⊗[𝕜] F` is nontrivial when `E` and `F` are nontrivial.
* `TensorProduct.norm_mapL` and `TensorProduct.denseRange_mapL`: `‖mapL f g‖ = ‖f‖ * ‖g‖` and
  preservation of dense range.
* `ContinuousLinearMap.norm_rTensor`, `norm_lTensor`, `rTensorₗᵢ`, `lTensorₗᵢ`,
  `denseRange_rTensor`, `denseRange_lTensor`: exact norms, linear isometries on nontrivial passive
  factors (`rTensor_eq_zero`, `lTensor_eq_zero` on subsingletons), and dense-range preservation.
-/

public section

open scoped TensorProduct

namespace TensorProduct
variable {𝕜 E F G H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

instance instNontrivial [Nontrivial E] [Nontrivial F] : Nontrivial (E ⊗[𝕜] F) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E); obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine ⟨x ⊗ₜ[𝕜] y, 0, fun h ↦ ?_⟩
  have h0 : ‖x ⊗ₜ[𝕜] y‖ = 0 := by simp [h]
  rw [norm_tmul, mul_eq_zero, norm_eq_zero, norm_eq_zero] at h0
  exact h0.elim hx hy
/-- The operator norm of `f ⊗ g` on the inner-product tensor product is the product of the
operator norms of `f` and `g`. -/
@[simp] theorem norm_mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) : ‖mapL f g‖ = ‖f‖ * ‖g‖ := by
  refine le_antisymm (norm_mapL_le f g) ?_
  have hy (y : G) : ‖f‖ * ‖g y‖ ≤ ‖mapL f g‖ * ‖y‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (g y)) with hgy | hgy
    · rw [← hgy, mul_zero]; positivity
    · rw [← le_div_iff₀ hgy]
      refine f.opNorm_le_bound (by positivity) fun x ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hgy]
      have h := (mapL f g).le_opNorm (x ⊗ₜ[𝕜] y)
      rw [mapL_tmul, norm_tmul, norm_tmul] at h; linarith
  rcases eq_or_lt_of_le (norm_nonneg f) with hf | hf
  · simp [← hf]
  · rw [mul_comm, ← le_div_iff₀ hf]
    refine g.opNorm_le_bound (by positivity) fun y ↦ ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hf]; linarith [hy y]
/-- The tensor product of two bounded linear maps with dense range has dense range. -/
theorem denseRange_mapL {f : E →L[𝕜] F} {g : G →L[𝕜] H} (hf : DenseRange f) (hg : DenseRange g) :
    DenseRange (mapL f g) := by
  let R : Submodule 𝕜 (F ⊗[𝕜] H) := LinearMap.range (mapL f g).toLinearMap
  have hmem (z : F ⊗[𝕜] H) : z ∈ R.topologicalClosure := by
    induction z using TensorProduct.inductionOn with
    | tmul y w =>
      refine hf.induction_on y (R.isClosed_topologicalClosure.preimage ((mkL 𝕜 F H).flip w).2)
        fun x ↦ hg.induction_on w (R.isClosed_topologicalClosure.preimage (mkL 𝕜 F H (f x)).2)
          fun z ↦ R.le_topologicalClosure ⟨x ⊗ₜ[𝕜] z, rfl⟩
    | add _ _ hz₁ hz₂ => exact add_mem hz₁ hz₂
  intro z; have hz : z ∈ (R.topologicalClosure : Set (F ⊗[𝕜] H)) := hmem z
  rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range, ContinuousLinearMap.coe_coe] at hz
end TensorProduct

namespace ContinuousLinearMap
variable {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Tensoring on the right with the identity of a nontrivial inner product space preserves norm. -/
@[simp] theorem norm_rTensor [Nontrivial G] (f : E →L[𝕜] F) : ‖f.rTensor G‖ = ‖f‖ := by
  rw [rTensor_eq_mapL, TensorProduct.norm_mapL, norm_id, mul_one]
/-- Tensoring on the left with the identity of a nontrivial inner product space preserves norm. -/
@[simp] theorem norm_lTensor [Nontrivial G] (f : E →L[𝕜] F) : ‖f.lTensor G‖ = ‖f‖ := by
  rw [lTensor_eq_mapL, TensorProduct.norm_mapL, norm_id, one_mul]
variable (𝕜 E F G) in
/-- Tensoring on the right with the identity of a nontrivial space, as a linear isometry. -/
noncomputable def rTensorₗᵢ [Nontrivial G] : (E →L[𝕜] F) →ₗᵢ[𝕜] ((E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] G)) where
  toLinearMap := ⟨⟨fun f ↦ f.rTensor G, rTensor_add G⟩, rTensor_smul G⟩
  norm_map' := norm_rTensor
@[simp] theorem rTensorₗᵢ_apply [Nontrivial G] (f : E →L[𝕜] F) :
    rTensorₗᵢ 𝕜 E F G f = f.rTensor G := (rfl)
variable (𝕜 E F G) in
/-- Tensoring on the left with the identity of a nontrivial space, as a linear isometry. -/
noncomputable def lTensorₗᵢ [Nontrivial G] : (E →L[𝕜] F) →ₗᵢ[𝕜] ((G ⊗[𝕜] E) →L[𝕜] (G ⊗[𝕜] F)) where
  toLinearMap := ⟨⟨fun f ↦ f.lTensor G, lTensor_add G⟩, lTensor_smul G⟩
  norm_map' := norm_lTensor
@[simp] theorem lTensorₗᵢ_apply [Nontrivial G] (f : E →L[𝕜] F) :
    lTensorₗᵢ 𝕜 E F G f = f.lTensor G := (rfl)
/-- Tensoring on the right with the identity of a nontrivial inner product space is injective. -/
theorem rTensor_injective (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Nontrivial G] : Function.Injective (fun f : E →L[𝕜] F ↦ f.rTensor G) :=
  (rTensorₗᵢ 𝕜 E F G).injective
/-- Tensoring on the left with the identity of a nontrivial inner product space is injective. -/
theorem lTensor_injective (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Nontrivial G] : Function.Injective (fun f : E →L[𝕜] F ↦ f.lTensor G) :=
  (lTensorₗᵢ 𝕜 E F G).injective
/-- Tensoring on the right with a subsingleton space produces the zero operator. -/
@[simp] theorem rTensor_eq_zero [Subsingleton G] (f : E →L[𝕜] F) : f.rTensor G = 0 :=
  Subsingleton.elim _ _
/-- Tensoring on the left with a subsingleton space produces the zero operator. -/
@[simp] theorem lTensor_eq_zero [Subsingleton G] (f : E →L[𝕜] F) : f.lTensor G = 0 :=
  Subsingleton.elim _ _
/-- Tensoring a map with dense range on the right with the identity preserves dense range. -/
theorem denseRange_rTensor (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {f : E →L[𝕜] F} (hf : DenseRange f) : DenseRange (f.rTensor G) := by
  rw [rTensor_eq_mapL]; exact TensorProduct.denseRange_mapL hf denseRange_id
/-- Tensoring a map with dense range on the left with the identity preserves dense range. -/
theorem denseRange_lTensor (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {f : E →L[𝕜] F} (hf : DenseRange f) : DenseRange (f.lTensor G) := by
  rw [lTensor_eq_mapL]; exact TensorProduct.denseRange_mapL denseRange_id hf
end ContinuousLinearMap
