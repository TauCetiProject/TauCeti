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
# The scalar estimates behind Birkhoff's contraction theorem

This file collects the scalar inequalities behind Birkhoff's contraction theorem for Hilbert's
projective metric (`Matrix.hilbertProjectiveDist_mulVec_le` in
`TauCeti/Data/Matrix/BirkhoffContraction.lean`). They contain no matrices.

For `l ≥ 1`, the function `σ ↦ log ((1 + l * exp σ) / (l + exp σ))` vanishes at `σ = 0` and has
derivative `l * exp σ / (1 + l * exp σ) - exp σ / (l + exp σ)`, which is at most
`(l - 1) / (l + 1)` (with equality at `σ = 0`). It is therefore bounded by `(l - 1) / (l + 1) * σ`
for `σ ≥ 0`. Writing `l = exp (Δ / 2)`, the slope is `tanh (Δ / 4)`.

Combined with a polynomial inequality, this gives the following for `R ≥ 1`, `l ≥ 1` and
positive `α, β, α', β'`. The logarithmic cross ratio of the pairs `(R * α + β, α + β)` and
`(R * α' + β', α' + β')` is at most `(l - 1) / (l + 1) * log R` whenever the pairs `(α, β)` and
`(α', β')` themselves have cross ratio `α * β' / (β * α')` at most `l ^ 2`. This is Birkhoff's
theorem in two dimensions.

## Main results

* `TauCeti.log_one_add_mul_exp_div_add_exp_le`:
  `log ((1 + l * exp σ) / (l + exp σ)) ≤ (l - 1) / (l + 1) * σ` for `1 ≤ l` and `0 ≤ σ`.
* `TauCeti.birkhoff_cross_ratio_le`: the polynomial cross-ratio bound by
  `((1 + l * s) / (l + s)) ^ 2` for `1 ≤ s` and `1 ≤ l`.
* `TauCeti.log_birkhoff_cross_ratio_le`: the two-dimensional form of Birkhoff's theorem, for
  `1 ≤ R` and `1 ≤ l`.

## References

* G. Birkhoff, *Extensions of Jentzsch's theorem*, Trans. Amer. Math. Soc. 85 (1957), 219--227.
* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer (2006), Chapter 3.
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
    rw [Pi.zero_apply, sub_nonneg, div_sub_div _ _ (hpos₁ t).ne' (hpos₂ t).ne',
      div_le_div_iff₀ (mul_pos (hpos₁ t) (hpos₂ t)) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hl) (zero_le_one.trans hl))
      (sq_nonneg (exp t - 1))]
  have := hmono hσ
  simp only [mul_zero, exp_zero, mul_one, add_comm (1 : ℝ) l, sub_self] at this
  rw [log_div (hpos₁ σ).ne' (hpos₂ σ).ne']
  linarith

/-- The two-dimensional polynomial inequality behind Birkhoff's theorem. Let `1 ≤ s` and
`1 ≤ l`, and let `α, β, α', β'` be positive with `α * β' ≤ l ^ 2 * (β * α')`. Then the cross ratio
of `(s ^ 2 * α + β, α + β)` and `(s ^ 2 * α' + β', α' + β')` is at most
`((1 + l * s) / (l + s)) ^ 2`. -/
theorem birkhoff_cross_ratio_le {α β α' β' s l : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα' : 0 < α')
    (hβ' : 0 < β') (hs : 1 ≤ s) (hl : 1 ≤ l) (h : α * β' ≤ l ^ 2 * (β * α')) :
    (s ^ 2 * α + β) * (α' + β') * (l + s) ^ 2 ≤
      (1 + l * s) ^ 2 * ((α + β) * (s ^ 2 * α' + β')) := by
  have hs2 : 0 ≤ s ^ 2 - 1 := by nlinarith
  have hl2 : 0 ≤ l ^ 2 - 1 := by nlinarith
  -- increasing the ratio `α / β` up to `l ^ 2 * α' / β'` only increases the left side
  have h₁ : (s ^ 2 * α + β) * (l ^ 2 * α' + β') ≤ (s ^ 2 * (l ^ 2 * α') + β') * (α + β) := by
    nlinarith [mul_le_mul_of_nonneg_left h hs2]
  -- at the extreme ratio the difference is `(l ^ 2 - 1) * (s ^ 2 - 1) * (l * s * α' - β') ^ 2`
  have h₂ : (s ^ 2 * (l ^ 2 * α') + β') * (α' + β') * (l + s) ^ 2 ≤
      (1 + l * s) ^ 2 * ((l ^ 2 * α' + β') * (s ^ 2 * α' + β')) := by
    nlinarith [mul_nonneg (mul_nonneg hl2 hs2) (sq_nonneg (l * s * α' - β'))]
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < l ^ 2 * α' + β')
  nlinarith [mul_le_mul_of_nonneg_right h₁ (by positivity : 0 ≤ (α' + β') * (l + s) ^ 2),
    mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ α + β)]

/-- The two-dimensional form of Birkhoff's theorem: for `R ≥ 1`, `l ≥ 1` and positive
`α, β, α', β'` with `α * β' ≤ l ^ 2 * (β * α')`, the logarithmic cross ratio of
`(R * α + β, α + β)` and `(R * α' + β', α' + β')` is at most `(l - 1) / (l + 1) * log R`. -/
theorem log_birkhoff_cross_ratio_le {α β α' β' R l : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα' : 0 < α')
    (hβ' : 0 < β') (hR : 1 ≤ R) (hl : 1 ≤ l) (h : α * β' ≤ l ^ 2 * (β * α')) :
    log ((R * α + β) * (α' + β') / ((α + β) * (R * α' + β'))) ≤
      (l - 1) / (l + 1) * log R := by
  set s := exp (log R / 2)
  have hs : 1 ≤ s := one_le_exp (by linarith [log_nonneg hR])
  have hsR : s ^ 2 = R := by
    rw [sq, ← exp_add, add_halves, exp_log (by linarith)]
  have hden : 0 < (α + β) * (R * α' + β') := by
    have : 0 < R := by linarith
    positivity
  have hnum : 0 < (R * α + β) * (α' + β') := by
    have : 0 < R := by linarith
    positivity
  have _hls : 0 < l + s := by linarith
  have hle : (R * α + β) * (α' + β') / ((α + β) * (R * α' + β')) ≤
      ((1 + l * s) / (l + s)) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hden (by positivity), ← hsR]
    nlinarith [birkhoff_cross_ratio_le hα hβ hα' hβ' hs hl h]
  calc log ((R * α + β) * (α' + β') / ((α + β) * (R * α' + β')))
      ≤ log (((1 + l * s) / (l + s)) ^ 2) := log_le_log (div_pos hnum hden) hle
    _ = 2 * log ((1 + l * s) / (l + s)) := by rw [log_pow]; norm_num
    _ ≤ 2 * ((l - 1) / (l + 1) * (log R / 2)) := by
        gcongr
        exact log_one_add_mul_exp_div_add_exp_le hl (by linarith [log_nonneg hR])
    _ = (l - 1) / (l + 1) * log R := by ring

end TauCeti
