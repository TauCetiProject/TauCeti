/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Compactness of `2 × 2` block operators on `Lᵖ` products

A continuous linear map `T : WithLp p (E₁ × E₂) →L[𝕜] WithLp q (F₁ × F₂)` decomposes along the
coordinate projections `WithLp.fstL`, `WithLp.sndL` and inclusions `WithLp.inlL`, `WithLp.inrL` as
the sum of its four coordinate blocks. Consequently `T` is a compact operator if and only if all
four coordinate blocks are compact (`ContinuousLinearMap.isCompactOperator_withLp_prod_iff`), and
in particular a diagonal block sum `f.withLpProdMap p g` is compact if and only if `f` and `g` are
compact (`ContinuousLinearMap.isCompactOperator_withLpProdMap_iff`).
-/

public section

open scoped ENNReal

namespace ContinuousLinearMap

section GeneralBlock

variable {p q : ℝ≥0∞} [Fact (1 ≤ q)] {𝕜 E₁ E₂ F₁ F₂ : Type*} [Semiring 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [Module 𝕜 F₁]
  [SeminormedAddCommGroup F₂] [Module 𝕜 F₂]

/-- Decomposition of an operator between `WithLp` binary products into its four coordinate
blocks. -/
theorem eq_sum_withLp_prod_blocks (T : WithLp p (E₁ × E₂) →L[𝕜] WithLp q (F₁ × F₂)) :
    T =
      (WithLp.inlL q 𝕜 F₁ F₂ ∘L (WithLp.fstL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inlL p 𝕜 E₁ E₂) ∘L
          WithLp.fstL p 𝕜 E₁ E₂) +
        (WithLp.inlL q 𝕜 F₁ F₂ ∘L (WithLp.fstL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inrL p 𝕜 E₁ E₂) ∘L
          WithLp.sndL p 𝕜 E₁ E₂) +
        (WithLp.inrL q 𝕜 F₁ F₂ ∘L (WithLp.sndL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inlL p 𝕜 E₁ E₂) ∘L
          WithLp.fstL p 𝕜 E₁ E₂) +
        (WithLp.inrL q 𝕜 F₁ F₂ ∘L (WithLp.sndL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inrL p 𝕜 E₁ E₂) ∘L
          WithLp.sndL p 𝕜 E₁ E₂) := by
  ext ⟨a, b⟩
  have hx : WithLp.toLp p (a, 0) + WithLp.toLp p (0, b) = WithLp.toLp p (a, b) := by
    simp [← WithLp.toLp_add]
  have hTx := congrArg T hx
  rw [map_add] at hTx
  apply (WithLp.prodContinuousLinearEquiv q 𝕜 F₁ F₂).injective
  ext <;> simp [← hTx]

/-- A continuous linear map `T : WithLp p (E₁ × E₂) →L[𝕜] WithLp q (F₁ × F₂)` is compact if and
only if all four of its `2 × 2` coordinate blocks are compact operators. -/
theorem isCompactOperator_withLp_prod_iff
    {T : WithLp p (E₁ × E₂) →L[𝕜] WithLp q (F₁ × F₂)} :
    IsCompactOperator T ↔
      IsCompactOperator ⇑(WithLp.fstL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inlL p 𝕜 E₁ E₂) ∧
        IsCompactOperator ⇑(WithLp.fstL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inrL p 𝕜 E₁ E₂) ∧
        IsCompactOperator ⇑(WithLp.sndL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inlL p 𝕜 E₁ E₂) ∧
        IsCompactOperator ⇑(WithLp.sndL q 𝕜 F₁ F₂ ∘L T ∘L WithLp.inrL p 𝕜 E₁ E₂) := by
  refine ⟨fun h ↦
    ⟨(h.comp_clm (WithLp.inlL p 𝕜 E₁ E₂)).clm_comp (WithLp.fstL q 𝕜 F₁ F₂),
     (h.comp_clm (WithLp.inrL p 𝕜 E₁ E₂)).clm_comp (WithLp.fstL q 𝕜 F₁ F₂),
     (h.comp_clm (WithLp.inlL p 𝕜 E₁ E₂)).clm_comp (WithLp.sndL q 𝕜 F₁ F₂),
     (h.comp_clm (WithLp.inrL p 𝕜 E₁ E₂)).clm_comp (WithLp.sndL q 𝕜 F₁ F₂)⟩, ?_⟩
  rintro ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩
  have hsum := eq_sum_withLp_prod_blocks T
  rw [hsum, FunLike.coe_add, FunLike.coe_add, FunLike.coe_add]
  exact (((((h₁₁.comp_clm (WithLp.fstL p 𝕜 E₁ E₂)).clm_comp (WithLp.inlL q 𝕜 F₁ F₂)).add
    ((h₁₂.comp_clm (WithLp.sndL p 𝕜 E₁ E₂)).clm_comp (WithLp.inlL q 𝕜 F₁ F₂))).add
    ((h₂₁.comp_clm (WithLp.fstL p 𝕜 E₁ E₂)).clm_comp (WithLp.inrL q 𝕜 F₁ F₂))).add
    ((h₂₂.comp_clm (WithLp.sndL p 𝕜 E₁ E₂)).clm_comp (WithLp.inrL q 𝕜 F₁ F₂)))

end GeneralBlock

section BlockSum

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E₁ E₂ F₁ F₂ : Type*} [Semiring 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [Module 𝕜 F₁]
  [SeminormedAddCommGroup F₂] [Module 𝕜 F₂]

/-- An `L^p` block sum is a compact operator if and only if both blocks are compact operators. -/
@[simp]
theorem isCompactOperator_withLpProdMap_iff {f : E₁ →L[𝕜] F₁} {g : E₂ →L[𝕜] F₂} :
    IsCompactOperator ⇑(f.withLpProdMap p g) ↔ IsCompactOperator f ∧ IsCompactOperator g := by
  have h₁₁ : WithLp.fstL p 𝕜 F₁ F₂ ∘L f.withLpProdMap p g ∘L WithLp.inlL p 𝕜 E₁ E₂ = f := by
    ext x; simp
  have h₁₂ : WithLp.fstL p 𝕜 F₁ F₂ ∘L f.withLpProdMap p g ∘L WithLp.inrL p 𝕜 E₁ E₂ = 0 := by
    ext x; simp
  have h₂₁ : WithLp.sndL p 𝕜 F₁ F₂ ∘L f.withLpProdMap p g ∘L WithLp.inlL p 𝕜 E₁ E₂ = 0 := by
    ext x; simp
  have h₂₂ : WithLp.sndL p 𝕜 F₁ F₂ ∘L f.withLpProdMap p g ∘L WithLp.inrL p 𝕜 E₁ E₂ = g := by
    ext x; simp
  rw [isCompactOperator_withLp_prod_iff, h₁₁, h₁₂, h₂₁, h₂₂]
  simp [isCompactOperator_zero]

end BlockSum

end ContinuousLinearMap
