/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Iterated derivatives under a linear change of variables

For a continuous linear equivalence `e`, the iterated derivative of `f` at `e y` is the iterated
derivative of `f ∘ e` at `y` precomposed with `e⁻¹` in every slot. Hence its norm is at most
`‖e⁻¹‖ ^ i` times the norm of the `i`-th derivative of `f ∘ e` at `y`. No differentiability
of `f` is needed.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Under a linear change of variables `e`, the `i`-th derivative of `f` at `e y` is bounded by
`‖e⁻¹‖ ^ i` times the `i`-th derivative of `f ∘ e` at `y`. -/
theorem norm_iteratedFDeriv_le_pow_mul_norm_iteratedFDeriv_comp_right (e : G ≃L[𝕜] E)
    (f : E → F) (y : G) (i : ℕ) :
    ‖iteratedFDeriv 𝕜 i f (e y)‖ ≤
      ‖(e.symm : E →L[𝕜] G)‖ ^ i * ‖iteratedFDeriv 𝕜 i (f ∘ e) y‖ := by
  have hf : (f ∘ e) ∘ e.symm = f := by
    funext z
    simp
  have h : iteratedFDeriv 𝕜 i f (e y) =
      (iteratedFDeriv 𝕜 i (f ∘ e) y).compContinuousLinearMap fun _ => (e.symm : E →L[𝕜] G) := by
    simpa only [← iteratedFDerivWithin_univ, Set.preimage_univ, symm_apply_apply, hf] using
      e.symm.iteratedFDerivWithin_comp_right (f ∘ e) uniqueDiffOn_univ (Set.mem_univ _) i
        (x := e y)
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

end ContinuousLinearEquiv
