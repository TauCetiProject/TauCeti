/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import TauCeti.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# The continuous functional calculus of orthogonal block sums

For operators `T₁` on a Hilbert space `H₁` and `T₂` on `H₂`, the block sum
`T₁.withLpProdMap 2 T₂` acts by `T₁` on the first summand of the Hilbert direct sum
`WithLp 2 (H₁ × H₂)` and by `T₂` on the second. By `TauCeti.Analysis.InnerProductSpace.ProdL2`,
`(T₁, T₂) ↦ T₁ ⊕ T₂` is a star algebra homomorphism (`ContinuousLinearMap.withLpProdMapStarAlgHom`)
and `T₁ ⊕ T₂` is self-adjoint exactly when `T₁` and `T₂` are.

The continuous functional calculus acts block by block: `cfc f (T₁ ⊕ T₂) = cfc f T₁ ⊕ cfc f T₂`
for self-adjoint `T₁` and `T₂` and `f` continuous on their spectra. The spectrum of `T₁ ⊕ T₂` is
the union of the two spectra (`ContinuousLinearMap.spectrum_withLpProdMap`), so
`g ↦ cfc g T₁ ⊕ cfc g T₂` is a continuous star algebra homomorphism on the continuous functions on
the spectrum of `T₁ ⊕ T₂`. It sends the identity to `T₁ ⊕ T₂`, so by uniqueness of the functional
calculus it is the functional calculus of `T₁ ⊕ T₂`. In particular the spectral projections of a
block sum are the block sums of the spectral projections.

## Main declarations

* `ContinuousLinearMap.cfc_withLpProdMap`: `cfc f (T₁ ⊕ T₂) = cfc f T₁ ⊕ cfc f T₂`.
-/

public section

open Set WithLp

variable {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

namespace ContinuousLinearMap

variable (T₁ : H₁ →L[𝕜] H₁) (T₂ : H₂ →L[𝕜] H₂)

variable [Algebra ℝ (H₁ →L[𝕜] H₁)] [Algebra ℝ (H₂ →L[𝕜] H₂)]
  [Algebra ℝ (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))]
  [IsScalarTower ℝ 𝕜 (H₁ →L[𝕜] H₁)] [IsScalarTower ℝ 𝕜 (H₂ →L[𝕜] H₂)]
  [IsScalarTower ℝ 𝕜 (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))]
  [ContinuousFunctionalCalculus ℝ (H₁ →L[𝕜] H₁) IsSelfAdjoint]
  [ContinuousFunctionalCalculus ℝ (H₂ →L[𝕜] H₂) IsSelfAdjoint]
  [ContinuousFunctionalCalculus ℝ (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂)) IsSelfAdjoint]

/-- **The continuous functional calculus of an orthogonal block sum acts block by block.** For
self-adjoint `T₁` and `T₂` and `f` continuous on their spectra,
`cfc f (T₁ ⊕ T₂) = cfc f T₁ ⊕ cfc f T₂`. -/
theorem cfc_withLpProdMap (f : ℝ → ℝ) (h₁ : IsSelfAdjoint T₁) (h₂ : IsSelfAdjoint T₂)
    (hf : ContinuousOn f (spectrum ℝ T₁ ∪ spectrum ℝ T₂)) :
    cfc f (T₁.withLpProdMap 2 T₂) = (cfc f T₁).withLpProdMap 2 (cfc f T₂) := by
  have h : IsSelfAdjoint (T₁.withLpProdMap 2 T₂) :=
    (isSelfAdjoint_withLpProdMap_iff T₁ T₂).2 ⟨h₁, h₂⟩
  have hσ := spectrum_withLpProdMap (R := ℝ) (p := 2) T₁ T₂
  have hσ₁ : spectrum ℝ T₁ ⊆ spectrum ℝ (T₁.withLpProdMap 2 T₂) := hσ ▸ subset_union_left
  have hσ₂ : spectrum ℝ T₂ ⊆ spectrum ℝ (T₁.withLpProdMap 2 T₂) := hσ ▸ subset_union_right
  -- The functional calculus of `T₁ ⊕ T₂` is `g ↦ cfc g T₁ ⊕ cfc g T₂`, by uniqueness.
  let Φ : C(spectrum ℝ (T₁.withLpProdMap 2 T₂), ℝ) →⋆ₐ[ℝ]
      (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂)) :=
    (withLpProdMapStarAlgHom.restrictScalars ℝ).comp
      (((cfcHom h₁).comp (ContinuousMap.compStarAlgHom' ℝ ℝ
        ⟨inclusion hσ₁, continuous_inclusion hσ₁⟩)).prod
      ((cfcHom h₂).comp (ContinuousMap.compStarAlgHom' ℝ ℝ
        ⟨inclusion hσ₂, continuous_inclusion hσ₂⟩)))
  -- `Φ` unfolds, by definition of the composite and the product of star algebra homomorphisms.
  have hΦapp (g : C(spectrum ℝ (T₁.withLpProdMap 2 T₂), ℝ)) :
      Φ g = (cfcHom h₁ (g.comp ⟨inclusion hσ₁, continuous_inclusion hσ₁⟩)).withLpProdMap 2
        (cfcHom h₂ (g.comp ⟨inclusion hσ₂, continuous_inclusion hσ₂⟩)) :=
    withLpProdMapStarAlgHom_apply _
  have hΦc : Continuous Φ := by
    rw [show ⇑Φ = _ from funext hΦapp]
    exact ((cfcHom_continuous h₁).comp (ContinuousMap.continuous_precomp _)).withLpProdMap
      ((cfcHom_continuous h₂).comp (ContinuousMap.continuous_precomp _))
  have hΦ : cfcHom h = Φ := by
    refine cfcHom_eq_of_continuous_of_map_id h Φ hΦc ?_
    rw [hΦapp]
    exact congr_arg₂ (withLpProdMap 2) (cfcHom_id h₁) (cfcHom_id h₂)
  rw [cfc_apply f _ h (hσ ▸ hf), cfc_apply f T₁ h₁ (hf.mono subset_union_left),
    cfc_apply f T₂ h₂ (hf.mono subset_union_right), hΦ, hΦapp]
  -- The restriction of `f` to the spectrum of `T₁ ⊕ T₂`, composed with the inclusion of the
  -- spectrum of `Tᵢ`, is by definition the restriction of `f` to the spectrum of `Tᵢ`.
  rfl

end ContinuousLinearMap
