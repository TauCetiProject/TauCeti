/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Smooth functions supported in a compact set as Schwartz functions

A smooth function supported in a compact set `K` is a Schwartz function. This file shows that the
resulting inclusion of `𝓓_{K}(E, F)` into `𝓢(E, F)` is continuous
(`ContDiffMapSupportedIn.toSchwartzMapCLM`, which does not change the function:
`ContDiffMapSupportedIn.coe_toSchwartzMapCLM`). On functions supported in `K`, the Schwartz
seminorm `sup ‖x‖ ^ k ‖D^j f x‖` is at most `max r 0 ^ k` times the seminorm `sup ‖D^j f‖`, for a
bound `r` on the norms of the points of `K`.
-/

public section

noncomputable section

open TopologicalSpace
open scoped SchwartzMap Distributions

namespace ContDiffMapSupportedIn

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [SMulCommClass ℝ 𝕜 F] {K : Compacts E}

/-- The inclusion of the smooth functions supported in a compact set `K` into Schwartz space, as a
continuous `𝕜`-linear map. -/
@[expose]
def toSchwartzMapCLM : 𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F) :=
  letI L : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓢(E, F) :=
    { toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' _ _ := SchwartzMap.ext fun _ ↦ rfl
      map_smul' _ _ := SchwartzMap.ext fun _ ↦ rfl }
  { toLinearMap := L
    cont := show Continuous L by
      obtain ⟨r, hr⟩ := K.isCompact.isBounded.exists_norm_le
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K) (schwartz_withSeminorms 𝕜 E F) L
        (.of_real fun ⟨k, j⟩ ↦ ⟨{j}, max r 0 ^ k, fun f ↦ ?_⟩)
      rw [Finset.sup_singleton]
      refine SchwartzMap.seminorm_le_bound 𝕜 k j _ (by positivity) fun x ↦ ?_
      -- `L f` is `f`, read as a Schwartz function.
      rw [show (L f : E → F) = f from rfl]
      by_cases hx : x ∈ K
      · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) ((hr x hx).trans (le_max_left r 0)) k)
          (norm_iteratedFDeriv_apply_le_seminorm_top 𝕜) (norm_nonneg _) (by positivity)
      · rw [f.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
        positivity }

/-- A smooth function supported in `K`, read as a Schwartz function, is the same function. -/
@[simp]
theorem coe_toSchwartzMapCLM (f : 𝓓_{K}(E, F)) : ⇑(toSchwartzMapCLM 𝕜 f) = f :=
  rfl

/-- A smooth function supported in `K`, read as a Schwartz function, has the same values. -/
theorem toSchwartzMapCLM_apply (f : 𝓓_{K}(E, F)) (x : E) : toSchwartzMapCLM 𝕜 f x = f x :=
  rfl

/-- A smooth function supported in `K`, read as a Schwartz function, is still supported in `K`. -/
theorem tsupport_toSchwartzMapCLM_subset (f : 𝓓_{K}(E, F)) :
    tsupport (toSchwartzMapCLM 𝕜 f) ⊆ K :=
  f.tsupport_subset

end ContDiffMapSupportedIn
