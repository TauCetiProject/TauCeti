/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
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
* `TauCeti.log_sub_sub_le_of_bounds`: a one-sided estimate for the signed difference of two
  logarithmic ratios, used for the half-step contraction of the Schrödinger system.

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

/-- **A one-sided scalar estimate for the half-step contraction of the Schrödinger system.** For
positive reals `A₁, A₂, B₁, B₂` and `0 ≤ M` with `exp m * A₂ ≤ A₁ ≤ exp (m + ω) * A₂`,
`exp (-2M) * B₂ ≤ A₂` and `exp (-2M) * (A₁ - exp m * A₂) ≤ B₁ - exp m * B₂`, the signed difference
`(log A₁ - log A₂) - (log B₁ - log B₂)` is at most `(1 - exp (-4M)) * ω`. Only this one-sided bound
is claimed. -/
theorem log_sub_sub_le_of_bounds {A₁ A₂ B₁ B₂ M m ω : ℝ} (hM0 : 0 ≤ M) (hA₁ : 0 < A₁)
    (hA₂ : 0 < A₂) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hA₁lo : exp m * A₂ ≤ A₁)
    (hA₁hi : A₁ ≤ exp (m + ω) * A₂) (hB₂A₂ : exp (-(2 * M)) * B₂ ≤ A₂)
    (hBA : exp (-(2 * M)) * (A₁ - exp m * A₂) ≤ B₁ - exp m * B₂) :
    (log A₁ - log A₂) - (log B₁ - log B₂) ≤ (1 - exp (-(4 * M))) * ω := by
  -- With `s = exp (-4M)`: `s * A₁ * B₂ + (1 - s) * exp m * A₂ * B₂ ≤ B₁ * A₂`.
  have hss : exp (-(2 * M)) * exp (-(2 * M)) = exp (-(4 * M)) := by
    rw [← exp_add]
    ring_nf
  set s := exp (-(4 * M))
  have hkey : s * A₁ * B₂ + (1 - s) * exp m * A₂ * B₂ ≤ B₁ * A₂ := by
    have h₁ : 0 ≤ A₁ - exp m * A₂ := sub_nonneg.2 hA₁lo
    have h₂ := mul_le_mul hBA hB₂A₂ (by positivity)
      ((mul_nonneg (exp_pos _).le h₁).trans hBA)
    have h₃ : exp (-(2 * M)) * (A₁ - exp m * A₂) * (exp (-(2 * M)) * B₂) =
        s * (A₁ - exp m * A₂) * B₂ := by
      rw [← hss]
      ring
    rw [h₃] at h₂
    linarith
  -- With `E = exp ((1 - s) * ω)`, convexity of `exp` and `A₁ ≤ exp (m + ω) * A₂` give
  -- `A₁ ≤ E * (s * A₁ + (1 - s) * exp m * A₂)`, which with `hkey` yields `A₁ * B₂ ≤ E * (A₂ * B₁)`.
  have hs0 : 0 < s := exp_pos _
  have hs1 : s ≤ 1 := exp_le_one_iff.2 (by linarith)
  have hconv : exp (s * ω) ≤ s * exp ω + (1 - s) := by
    simpa using convexOn_exp.2 (Set.mem_univ ω) (Set.mem_univ 0) hs0.le (sub_nonneg.2 hs1) (by ring)
  set E := exp ((1 - s) * ω)
  have hE : E * exp (s * ω) = exp ω := by
    rw [← exp_add]
    ring_nf
  have hEpos : 0 < E := exp_pos _
  have h₁ : A₁ * exp ω ≤
      E * (s * A₁ * exp ω + (1 - s) * exp m * exp ω * A₂) := by
    have h₁a : A₁ * exp ω = E * A₁ * exp (s * ω) := by
      rw [← hE]
      ring
    have h₁b := mul_le_mul_of_nonneg_left hconv (mul_nonneg hEpos.le hA₁.le)
    have h₁c := mul_le_mul_of_nonneg_left ((exp_add m ω) ▸ hA₁hi)
      (mul_nonneg hEpos.le (sub_nonneg.2 hs1))
    linarith
  have h₂ : A₁ ≤ E * (s * A₁ + (1 - s) * exp m * A₂) := by
    have hω0 := exp_pos ω
    nlinarith [h₁]
  have hmain : A₁ * B₂ ≤ E * (A₂ * B₁) := by nlinarith [hkey, h₂, hB₂, hEpos]
  have := log_le_log (by positivity) hmain
  rw [log_mul hA₁.ne' hB₂.ne', log_mul (exp_pos _).ne' (by positivity),
    log_exp, log_mul hA₂.ne' hB₁.ne'] at this
  linarith

end TauCeti
