/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Exact

/-!
# Automatic continuity of the snake connecting map on Banach spaces

In an algebraically exact diagram `(T₁, T₂, T₃)` of continuous linear maps over a
`NontriviallyNormedField` with rows `E₁ --f₁--> E₂ --f₂--> E₃ → 0` and
`0 → F₁ --g₁--> F₂ --g₂--> F₃`, where `E₂, E₃, F₁, F₂` are Banach spaces and `F₃` is a `T₁`
topological module, the Banach open mapping theorem makes `f₂` an open quotient map and `g₁`
(whose range equals the closed kernel of `g₂` because `F₃` is `T₁`) a topological embedding.
Consequently `Function.Exact.snakeδ` is automatically continuous (`TauCeti.continuous_snakeδ`,
bundled as `TauCeti.banachSnakeδL`), with no splitting or Hilbert-space assumptions; in particular,
Hilbert short exact diagrams over `RCLike` fields are covered directly by typeclass inference.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1,
  Theorem 19.1.2.
-/

public section

namespace TauCeti

open ContinuousLinearMap (toLinearMap_comp_eq)

universe u u₁ u₂ u₃ v₁ v₂ v₃

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E₁ : Type u₁} {E₂ : Type u₂} {E₃ : Type u₃} {F₁ : Type v₁} {F₂ : Type v₂} {F₃ : Type v₃}
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃] [T1Space F₃]
  {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
  {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
  (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
  (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
  (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)

include hf hf₂ hg hg₁ h₁₂ h₂₃

/-- Continuous snake connecting map for an algebraically exact diagram where `E₂, E₃, F₁, F₂` are
Banach spaces over a `NontriviallyNormedField` and `F₃` is a `T₁` space (`[T1Space F₃]`), requiring
no continuous linear splittings as data. -/
noncomputable def banachSnakeδL : T₃.ker →L[𝕜] F₁ ⧸ T₁.range :=
  snakeδLOfIsOpenQuotientMap hf (f₂.isOpenQuotientMap_iff_surjective.2 hf₂) hg
    (g₁.isEmbedding_iff_injective_and_isClosed_range.2 ⟨hg₁,
      by simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hg.isClosed_range⟩)
    h₁₂ h₂₃

@[simp, norm_cast] theorem toLinearMap_banachSnakeδL :
    (banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃).toLinearMap =
      hf.snakeδ hg hf₂ hg₁ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃) := by
  simp [banachSnakeδL]

@[simp] theorem coe_banachSnakeδL :
    ⇑(banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃) =
      hf.snakeδ hg hf₂ hg₁ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃) := by
  simp [banachSnakeδL]

/-- In an algebraically exact diagram where `E₂, E₃, F₁, F₂` are Banach spaces over a
`NontriviallyNormedField` and `F₃` is a `T₁` space, the algebraic snake connecting map
`Function.Exact.snakeδ` is automatically continuous. -/
theorem continuous_snakeδ :
    Continuous (hf.snakeδ hg hf₂ hg₁ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)) :=
  coe_banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃ ▸ (banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃).continuous

/-- Diagram-chase formula for `TauCeti.banachSnakeδL`: if `f₂ x₂ = x₃` and `g₁ y₁ = T₂ x₂`, then
`banachSnakeδL` sends `x₃` to the class of `y₁` modulo `range T₁`. -/
theorem banachSnakeδL_eq (x₃ : T₃.ker) (x₂ : E₂) (y₁ : F₁)
    (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = T₂ x₂) :
    banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃ x₃ = Submodule.Quotient.mk y₁ := by
  simpa only [coe_banachSnakeδL] using
    hf.snakeδ_apply hg hf₂ hg₁ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)
      x₃ x₂ hx₂ y₁ hy₁

/-- When continuous linear splittings `(σ, ρ)` also exist, `TauCeti.banachSnakeδL` agrees with
`TauCeti.snakeδL`. -/
theorem banachSnakeδL_eq_snakeδL
    {σ : E₃ →L[𝕜] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[𝕜] F₁} (hρ : Function.LeftInverse ρ g₁) :
    banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃ = snakeδL hf hg h₁₂ h₂₃ hσ hρ :=
  ContinuousLinearMap.coe_injective <| by rw [toLinearMap_banachSnakeδL, toLinearMap_snakeδL]

/-- Exactness of `TauCeti.banachSnakeδL` at `ker T₃`. -/
theorem exact_kerMapL_banachSnakeδL :
    Function.Exact (kerMapL h₂₃) (banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃) := by
  simpa only [coe_kerMapL, coe_banachSnakeδL] using
    hf.restrict_ker_snakeδ hg hf₂ hg₁ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

/-- Exactness of `TauCeti.banachSnakeδL` at `F₁ ⧸ range T₁`. -/
theorem exact_banachSnakeδL_cokerMapL :
    Function.Exact (banachSnakeδL hf hf₂ hg hg₁ h₁₂ h₂₃) (cokerMapL h₁₂) := by
  simpa only [coe_banachSnakeδL, coe_cokerMapL] using
    hf.snakeδ_mapQ_range hg hf₂ hg₁ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

end TauCeti
