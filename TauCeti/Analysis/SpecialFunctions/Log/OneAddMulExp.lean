/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A linear bound on `log ((1 + l * exp σ) / (l + exp σ))`

For `l ≥ 1`, the function `σ ↦ log ((1 + l * exp σ) / (l + exp σ))` vanishes at `σ = 0` and has
derivative `l * exp σ / (1 + l * exp σ) - exp σ / (l + exp σ)`, which is at most
`(l - 1) / (l + 1)` (with equality at `σ = 0`). It is therefore bounded by `(l - 1) / (l + 1) * σ`
for `σ ≥ 0`. Writing `l = exp (Δ / 2)`, the slope is `tanh (Δ / 4)`.

This is the scalar estimate behind Birkhoff's contraction theorem for Hilbert's projective metric
(`Matrix.hilbertProjectiveDist_mulVec_le` in `TauCeti/Data/Matrix/BirkhoffContraction.lean`),
but it contains no matrices.

## Main results

* `TauCeti.log_one_add_mul_exp_div_add_exp_le`:
  `log ((1 + l * exp σ) / (l + exp σ)) ≤ (l - 1) / (l + 1) * σ` for `1 ≤ l` and `0 ≤ σ`.
-/

public section

open Real

namespace TauCeti

/-- For `1 ≤ l` and `0 ≤ σ`, `log ((1 + l * exp σ) / (l + exp σ)) ≤ (l - 1) / (l + 1) * σ`.
Both sides vanish at `σ = 0`, and the derivative of the left side is at most `(l - 1) / (l + 1)`. -/
theorem log_one_add_mul_exp_div_add_exp_le {l σ : ℝ} (hl : 1 ≤ l) (hσ : 0 ≤ σ) :
    log ((1 + l * exp σ) / (l + exp σ)) ≤ (l - 1) / (l + 1) * σ := by
  have hpos₁ : ∀ t, 0 < 1 + l * exp t := fun t ↦ by positivity
  have hpos₂ : ∀ t, 0 < l + exp t := fun t ↦ by positivity
  have hderiv : ∀ t, HasDerivAt
      (fun t ↦ (l - 1) / (l + 1) * t - (log (1 + l * exp t) - log (l + exp t)))
      ((l - 1) / (l + 1) - (l * exp t / (1 + l * exp t) - exp t / (l + exp t))) t := fun t ↦ by
    have := ((hasDerivAt_id t).const_mul ((l - 1) / (l + 1))).sub
      ((((hasDerivAt_exp t).const_mul l).const_add 1).log (hpos₁ t).ne' |>.sub
        (((hasDerivAt_exp t).const_add l).log (hpos₂ t).ne'))
    exact this.congr_deriv (by ring)
  have hmono := monotone_of_hasDerivAt_nonneg hderiv fun t ↦ by
    have hw := (exp_pos t).le
    rw [Pi.zero_apply, sub_nonneg, div_sub_div _ _ (hpos₁ t).ne' (hpos₂ t).ne',
      div_le_div_iff₀ (mul_pos (hpos₁ t) (hpos₂ t)) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hl) (zero_le_one.trans hl))
      (sq_nonneg (exp t - 1))]
  have := hmono hσ
  simp only [mul_zero, exp_zero, mul_one, add_comm (1 : ℝ) l, sub_self] at this
  rw [log_div (hpos₁ σ).ne' (hpos₂ σ).ne']
  linarith

end TauCeti
