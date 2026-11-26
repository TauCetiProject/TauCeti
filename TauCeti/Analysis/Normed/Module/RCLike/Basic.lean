/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.RCLike.Basic

/-!
# Elementary norm estimates in normed spaces over `ℝ` or `ℂ`

In a normed space over an `RCLike` field:

* `TauCeti.norm_two_inv_smul_add_le`: half the sum of two vectors of norm at most `B` has norm
  at most `B`, so the closed ball of radius `B` contains the midpoint of any two of its points;
* `TauCeti.norm_sum_smul_le_norm_sum_re_add_norm_sum_im`: splitting the scalar coefficients of a
  finite combination `∑ i ∈ s, a i • v i` into real and imaginary parts bounds its norm by the
  sum of the norms of the two combinations with real coefficients.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Half the sum of two vectors of norm at most `B` has norm at most `B`. -/
theorem norm_two_inv_smul_add_le {a b : E} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖(2 : 𝕜)⁻¹ • (a + b)‖ ≤ B := by
  rw [norm_smul, norm_inv, RCLike.norm_two]
  linarith [norm_add_le a b]

/-- Splitting scalar coefficients into real and imaginary parts: the norm of a combination of the
`v i` with coefficients `a i` is at most the sum of the norms of the combinations with real
coefficients `re (a i)` and `im (a i)`. -/
theorem norm_sum_smul_le_norm_sum_re_add_norm_sum_im {ι : Type*} {v : ι → E} {s : Finset ι}
    {a : ι → 𝕜} :
    ‖∑ i ∈ s, a i • v i‖ ≤
      ‖∑ i ∈ s, (RCLike.re (a i) : 𝕜) • v i‖ + ‖∑ i ∈ s, (RCLike.im (a i) : 𝕜) • v i‖ := by
  -- The imaginary parts contribute `I • ∑ i ∈ s, im (a i) • v i`, and `‖I‖ ≤ 1`.
  have hsplit : ∑ i ∈ s, a i • v i = ∑ i ∈ s, (RCLike.re (a i) : 𝕜) • v i +
      (RCLike.I : 𝕜) • ∑ i ∈ s, (RCLike.im (a i) : 𝕜) • v i := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_smul, mul_comm, ← add_smul, RCLike.re_add_im]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) RCLike.norm_I_le_one

end TauCeti
