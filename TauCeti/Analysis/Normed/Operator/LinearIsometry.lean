/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Closed ranges of postcomposition by linear isometries

Postcomposition by a (semilinear) isometry `i` acts pointwise on continuous linear maps, and
its image consists precisely of the operators whose values lie in the range of `i`
(`LinearIsometry.range_postcomp`). Consequently, if the range of `i` is closed, the
postcomposition operator also has closed range (`LinearIsometry.isClosed_range_postcomp`).
This lets regularity of an operator-valued map be checked after a closed isometric embedding
of the codomain, for instance of alternating maps into multilinear maps.
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
