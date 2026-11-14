/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Composition of continuous linear maps with linear isometries

Postcomposition by a (semilinear) isometry `i` acts pointwise on continuous linear maps, and
its image consists precisely of the operators whose values lie in the range of `i`
(`LinearIsometry.range_postcomp`). Consequently, if the range of `i` is closed, the
postcomposition operator also has closed range (`LinearIsometry.isClosed_range_postcomp`).
This lets regularity of an operator-valued map be checked after a closed isometric embedding
of the codomain, for instance of alternating maps into multilinear maps.

Dually, precomposition with a linear isometric equivalence `e : E ≃ₗᵢ[𝕜] F` is a linear isometric
equivalence `LinearIsometryEquiv.precomp G e : (F →L[𝕜] G) ≃ₗᵢ[𝕜] (E →L[𝕜] G)` for any seminormed
target `G`. Taking `G = 𝕜` gives contravariant functoriality of the continuous dual on linear
isometric equivalences, used to pass between duals and biduals of submodules and quotients.
-/

public section

open Set

namespace LinearIsometry

variable {𝕜 𝕜₂ 𝕜₃ D E F : Type*}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [SeminormedAddCommGroup D] [NormedSpace 𝕜 D]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₃ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃]

/-- Postcomposition by a linear isometry evaluates by composing the two maps. -/
@[simp] theorem postcomp_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜₂ E]
    (i : E →ₛₗᵢ[σ₂₃] F) (f : D →SL[σ₁₂] E) (x : D) :
    postcomp (σ₁₂ := σ₁₂) (σ₁₃ := σ₁₃) i f x = i (f x) := rfl

variable [NormedAddCommGroup E] [NormedSpace 𝕜₂ E]

/-- The range of postcomposition by a linear isometry consists exactly of the continuous linear
maps all of whose values lie in the range of that isometry. -/
@[simp] theorem range_postcomp (i : E →ₛₗᵢ[σ₂₃] F) :
    range (postcomp (σ₁₂ := σ₁₂) (σ₁₃ := σ₁₃) i) = {g : D →SL[σ₁₃] F | ∀ x, g x ∈ range i} := by
  ext g
  rw [mem_ofPred_eq]
  refine ⟨by rintro ⟨f, rfl⟩ x; exact ⟨f x, rfl⟩, fun hg ↦ ?_⟩
  choose f hf using hg
  let f' : D →ₛₗ[σ₁₂] E :=
    { toFun := f
      map_add' x y := i.injective (by simp [hf])
      map_smul' c x := i.injective <| by
        rw [i.map_smulₛₗ, RingHomCompTriple.comp_apply, hf, hf, g.map_smulₛₗ] }
  refine ⟨f'.mkContinuous ‖g‖ fun x ↦ ?_, by ext x; exact hf x⟩
  rw [← i.norm_map, LinearMap.coe_mk, AddHom.coe_mk, hf]
  exact g.le_opNorm x

/-- Postcomposition by a closed-range linear isometry has closed range on operators. -/
theorem isClosed_range_postcomp (i : E →ₛₗᵢ[σ₂₃] F) (hi : IsClosed (range i)) :
    IsClosed (range (postcomp i : (D →SL[σ₁₂] E) →ₛₗᵢ[σ₂₃] (D →SL[σ₁₃] F))) := by
  convert isClosed_iInter fun x : D ↦
    hi.preimage (continuous_eval_const (F := D →SL[σ₁₃] F) x) using 1
  ext g
  simp only [range_postcomp, mem_ofPred_eq, mem_iInter, mem_preimage]

end LinearIsometry

namespace LinearIsometryEquiv

variable {𝕜 E F H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
  (G : Type*) [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Precomposition with a linear isometric equivalence as a linear isometric equivalence between
spaces of continuous linear maps. -/
def precomp (e : E ≃ₗᵢ[𝕜] F) : (F →L[𝕜] G) ≃ₗᵢ[𝕜] (E →L[𝕜] G) where
  toFun f := f.comp e.toLinearIsometry.toContinuousLinearMap
  invFun g := g.comp e.symm.toLinearIsometry.toContinuousLinearMap
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    apply le_antisymm
    · exact (f.opNorm_comp_le _).trans <|
        mul_le_of_le_one_right (norm_nonneg f) e.toLinearIsometry.norm_toContinuousLinearMap_le
    · have h : f = (f.comp e.toLinearIsometry.toContinuousLinearMap).comp
          e.symm.toLinearIsometry.toContinuousLinearMap := by ext x; simp
      exact (congrArg norm h).le.trans <| ((f.comp _).opNorm_comp_le _).trans <|
        mul_le_of_le_one_right (norm_nonneg _) e.symm.toLinearIsometry.norm_toContinuousLinearMap_le

/-- Precomposing an operator with `e` composes it on the right with `e` as a continuous linear
map. -/
@[simp]
theorem precomp_apply (e : E ≃ₗᵢ[𝕜] F) (f : F →L[𝕜] G) :
    e.precomp G f = f.comp e.toLinearIsometry.toContinuousLinearMap :=
  (rfl)

/-- As a continuous linear map, `e.precomp G` agrees with `ContinuousLinearMap.precomp G`. -/
theorem toContinuousLinearMap_precomp (e : E ≃ₗᵢ[𝕜] F) :
    (e.precomp G).toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.precomp G e.toLinearIsometry.toContinuousLinearMap := by
  ext f x
  simp

/-- The inverse of `LinearIsometryEquiv.precomp` is precomposition with `e.symm`. -/
@[simp]
theorem precomp_symm (e : E ≃ₗᵢ[𝕜] F) : (e.precomp G).symm = e.symm.precomp G :=
  (rfl)

/-- Precomposing with the identity isometric equivalence is the identity on continuous linear
maps. -/
@[simp]
theorem precomp_refl :
    (LinearIsometryEquiv.refl 𝕜 E).precomp G = LinearIsometryEquiv.refl 𝕜 (E →L[𝕜] G) := by
  ext f x
  simp

/-- Precomposing with a composition of linear isometric equivalences reverses the order of
composition. -/
@[simp]
theorem precomp_trans (e₁ : E ≃ₗᵢ[𝕜] F) (e₂ : F ≃ₗᵢ[𝕜] H) :
    (e₁.trans e₂).precomp G = (e₂.precomp G).trans (e₁.precomp G) := by
  ext f x
  simp

end LinearIsometryEquiv
