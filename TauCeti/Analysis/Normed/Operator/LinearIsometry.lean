/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Closed ranges of postcomposition by linear isometries

Postcomposition by a linear isometry acts pointwise on continuous linear maps.
If its range is closed, the postcomposition operator also has closed range: its
image consists precisely of operators whose values lie in that range. This lets
smooth alternating pullback be checked through the underlying multilinear maps.
-/

public section

noncomputable section

open Set

namespace LinearIsometry

section Semilinear

variable {𝕜 𝕜₂ 𝕜₃ D E F : Type*}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [SeminormedAddCommGroup D] [NormedSpace 𝕜 D]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜₂ E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₃ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃]

/-- Postcomposition by a linear isometry evaluates by composing the two maps. -/
@[simp] theorem postcomp_apply (i : E →ₛₗᵢ[σ₂₃] F) (f : D →SL[σ₁₂] E) (x : D) :
    postcomp (σ₁₂ := σ₁₂) (σ₁₃ := σ₁₃) i f x = i (f x) := rfl

end Semilinear

variable {𝕜 D E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Postcomposition by a closed-range linear isometry has closed range on operators. -/
theorem isClosed_range_postcomp (i : E →ₗᵢ[𝕜] F) (hi : IsClosed (range i)) :
    IsClosed (range (postcomp i : (D →L[𝕜] E) →ₗᵢ[𝕜] (D →L[𝕜] F))) := by
  have hr : range (postcomp i : (D →L[𝕜] E) →ₗᵢ[𝕜] (D →L[𝕜] F)) =
      {g | ∀ x, g x ∈ i.toLinearMap.range} := by
    ext g
    constructor
    · rintro ⟨f, rfl⟩ x
      exact ⟨f x, postcomp_apply i f x⟩
    · intro hg
      let f := i.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (g.codRestrict i.toLinearMap.range hg)
      refine ⟨f, ?_⟩
      ext x
      simp only [postcomp_apply, f, ContinuousLinearMap.comp_apply]
      exact congrArg Subtype.val (i.equivRange.apply_symm_apply ⟨g x, hg x⟩)
  rw [hr]
  simp only [ofPred_forall]
  exact isClosed_iInter fun x ↦ hi.preimage (continuous_eval_const x)

end LinearIsometry
