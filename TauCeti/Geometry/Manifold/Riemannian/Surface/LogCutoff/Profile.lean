/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The logarithmic cutoff profile

For `0 < 4ε ≤ δ`, put `Λ = log (δ / ε)` and `λ(r) = log (r / ε) / Λ`, and let `τ` be
`Real.smoothTransition`. The logarithmic cutoff profile is
`ψ(r) = λ(r) τ(log₂ (r / ε)) + (1 - λ(r)) (1 - τ(log₂ (δ / r)))` for `r > 0`, and `0` for
`r ≤ 0`. It is smooth and nondecreasing, vanishes on `(-∞, ε]`, equals `1` on `[δ, ∞)` and
equals the logarithmic interpolation `λ` on `[2ε, δ / 2]`. Its derivative is nonnegative
everywhere and satisfies
`ψ'(r) ≤ c₀ / (r Λ)` for `r > 0` (and `0 ≤ 0` at `r = 0` under Lean's totalized division
`x / 0 = 0`), with `c₀ = 1 + sup τ'`. This bound makes its Dirichlet
energy on a surface of order `1 / Λ`.

## Main definitions

* `TauCeti.logCutoffProfile ε δ`: the profile `ψ`.
* `TauCeti.logCutoffConst`: the constant `c₀ = 1 + sup τ'`.

## Main results

* `TauCeti.contDiff_logCutoffProfile`: `ψ` is smooth.
* `TauCeti.monotone_logCutoffProfile`: `ψ` is nondecreasing.
* `TauCeti.deriv_logCutoffProfile_le`: `ψ'(r) ≤ c₀ / (r Λ)` for `r > 0` (and `0 ≤ 0` at `r = 0`
  via Lean's `x / 0 = 0`).
* `TauCeti.deriv_logCutoffProfile_of_mem_Icc`: `ψ'(r) = 1 / (r Λ)` on `[2ε, δ / 2]`.

Adapted from Giada Franz’s formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory),
`ForTauCeti/Geometry/Manifold/Riemannian/Surface/LogCutoff/Profile.lean`.

## References

* O. Chodosh, *Introduction to minimal surfaces*, proof of Lemma 5.8, for the planar
  logarithmic interpolation.
-/

public noncomputable section

open Real Set Filter
open scoped Topology ContDiff

namespace TauCeti

/-- The logarithmic cutoff profile `ψ_ε`: for `0 < 4ε ≤ δ` it vanishes on `(-∞, ε]`, equals
`log (r / ε) / log (δ / ε)` on `[2ε, δ / 2]` and equals `1` on `[δ, ∞)`, with smooth
transitions built from `Real.smoothTransition` in between. -/
def logCutoffProfile (ε δ r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else
    Real.log (r / ε) / Real.log (δ / ε) * smoothTransition (Real.logb 2 (r / ε)) +
      (1 - Real.log (r / ε) / Real.log (δ / ε)) *
        (1 - smoothTransition (Real.logb 2 (δ / r)))

/-- The defining formula for the logarithmic cutoff profile. -/
theorem logCutoffProfile_def (ε δ r : ℝ) :
    logCutoffProfile ε δ r = if r ≤ 0 then 0 else
      Real.log (r / ε) / Real.log (δ / ε) * smoothTransition (Real.logb 2 (r / ε)) +
        (1 - Real.log (r / ε) / Real.log (δ / ε)) *
          (1 - smoothTransition (Real.logb 2 (δ / r))) := (rfl)

/-- The constant `c₀ = 1 + sup τ'` of the derivative bound of the logarithmic cutoff profile,
where `τ` is `Real.smoothTransition`. -/
def logCutoffConst : ℝ :=
  1 + ⨆ t, deriv smoothTransition t

/-- The defining formula for the constant in the logarithmic cutoff derivative bound. -/
theorem logCutoffConst_def : logCutoffConst = 1 + ⨆ t, deriv smoothTransition t := (rfl)

/-- The constant of the derivative bound is at least one. -/
theorem one_le_logCutoffConst : 1 ≤ logCutoffConst := by
  rw [logCutoffConst_def]
  linarith [smoothTransition.iSup_deriv_nonneg]

/-- The constant of the derivative bound is positive. -/
theorem logCutoffConst_pos : 0 < logCutoffConst :=
  zero_lt_one.trans_le one_le_logCutoffConst

/-- The absolute value of the derivative of `Real.smoothTransition` is at most `c₀`. -/
theorem abs_deriv_smoothTransition_le_logCutoffConst (t : ℝ) :
    |deriv smoothTransition t| ≤ logCutoffConst := by
  rw [abs_of_nonneg (smoothTransition.deriv_nonneg t), logCutoffConst_def]
  linarith [smoothTransition.deriv_le_iSup t]

variable {ε δ r : ℝ}

section LogVariable

/-- The profile in the logarithmic variable `u = log r`. -/
private def logProfile (ε δ u : ℝ) : ℝ :=
  (u - log ε) / log (δ / ε) * smoothTransition ((u - log ε) / log 2) +
    (1 - (u - log ε) / log (δ / ε)) * (1 - smoothTransition ((log δ - u) / log 2))

/-- The derivative of the profile in the logarithmic variable. -/
private def logProfileDeriv (ε δ u : ℝ) : ℝ :=
  (smoothTransition ((u - log ε) / log 2) + smoothTransition ((log δ - u) / log 2) - 1 +
      (u - log ε) / log 2 * deriv smoothTransition ((u - log ε) / log 2) +
      (log δ - u) / log 2 * deriv smoothTransition ((log δ - u) / log 2)) / log (δ / ε)

private theorem one_le_logb_two {a b : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b) :
    1 ≤ Real.logb 2 (b / a) := by
  rw [← Real.logb_self_eq_one one_lt_two]
  exact Real.logb_le_logb_of_le one_lt_two two_pos ((le_div_iff₀ ha).2 hab)

private theorem one_le_sub_log_div_log_two {a b : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b) :
    1 ≤ (log b - log a) / log 2 := by
  have hb : 0 < b := by linarith
  simpa only [Real.logb, Real.log_div hb.ne' ha.ne'] using one_le_logb_two ha hab

private theorem logb_two_div_nonpos_of_abs_le {x y : ℝ} (hxy : |x| ≤ |y|) :
    Real.logb 2 (x / y) ≤ 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [← Real.logb_abs, abs_div]
  exact Real.logb_nonpos one_lt_two (by positivity) ((div_le_one (abs_pos.2 hy)).2 hxy)

private theorem abs_le_of_log_div_eq_zero (hε : 0 < ε) (hΛ : log (δ / ε) = 0) : |δ| ≤ ε := by
  rw [← div_le_one hε, ← abs_of_pos hε, ← abs_div]
  rcases Real.log_eq_zero.1 hΛ with h | h | h <;> simp [h]

private theorem log_div_pos (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) : 0 < log (δ / ε) :=
  Real.log_pos ((one_lt_div hε).2 (by linarith))

private theorem contDiff_logProfile : ContDiff ℝ ∞ (logProfile ε δ) := by
  have hτ : ContDiff ℝ ∞ smoothTransition := smoothTransition.contDiff
  have ha : ContDiff ℝ ∞ fun u : ℝ ↦ (u - log ε) / log 2 :=
    (contDiff_id.sub contDiff_const).div_const _
  have hb : ContDiff ℝ ∞ fun u : ℝ ↦ (log δ - u) / log 2 :=
    (contDiff_const.sub contDiff_id).div_const _
  have hl : ContDiff ℝ ∞ fun u : ℝ ↦ (u - log ε) / log (δ / ε) :=
    (contDiff_id.sub contDiff_const).div_const _
  exact (hl.mul (hτ.comp ha)).add ((contDiff_const.sub hl).mul (contDiff_const.sub (hτ.comp hb)))

private theorem hasDerivAt_logProfile (hΛ : log (δ / ε) ≠ 0) (u : ℝ) :
    HasDerivAt (logProfile ε δ) (logProfileDeriv ε δ u) u := by
  have hδ : δ ≠ 0 := fun h ↦ hΛ (by simp [h])
  have hε : ε ≠ 0 := fun h ↦ hΛ (by simp [h])
  unfold logProfile
  have ha : HasDerivAt (fun u : ℝ ↦ (u - log ε) / log 2) (1 / log 2) u :=
    ((hasDerivAt_id u).sub_const _).div_const _
  have hb : HasDerivAt (fun u : ℝ ↦ (log δ - u) / log 2) (-1 / log 2) u :=
    ((hasDerivAt_id u).const_sub _).div_const _
  have hl : HasDerivAt (fun u : ℝ ↦ (u - log ε) / log (δ / ε)) (1 / log (δ / ε)) u :=
    ((hasDerivAt_id u).sub_const _).div_const _
  have hd := (hl.fun_mul ha.smoothTransition).fun_add
    ((hl.const_sub 1).fun_mul (hb.smoothTransition.const_sub 1))
  refine hd.congr_deriv ?_
  unfold logProfileDeriv
  rw [Real.log_div hδ hε] at hΛ ⊢
  field_simp
  ring

private theorem logProfileDeriv_nonneg (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (u : ℝ) :
    0 ≤ logProfileDeriv ε δ u := by
  have hδ : 0 < δ := by linarith
  have h2 : 0 < log 2 := Real.log_pos one_lt_two
  have hlog : log 2 ≤ log (δ / ε) := Real.log_le_log two_pos ((le_div_iff₀ hε).2 hεδ)
  unfold logProfileDeriv
  apply div_nonneg _ (log_div_pos hε hεδ).le
  have hge : 1 ≤ (u - log ε) / log 2 + (log δ - u) / log 2 := by
    rw [← add_div, le_div_iff₀ h2]
    rw [Real.log_div hδ.ne' hε.ne'] at hlog
    linarith
  have hm := smoothTransition.monotone
    (by linarith : 1 - (u - log ε) / log 2 ≤ (log δ - u) / log 2)
  rw [smoothTransition.one_sub] at hm
  linarith [smoothTransition.mul_deriv_nonneg ((u - log ε) / log 2),
    smoothTransition.mul_deriv_nonneg ((log δ - u) / log 2)]

private theorem logProfileDeriv_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ) (u : ℝ) :
    logProfileDeriv ε δ u ≤ logCutoffConst / log (δ / ε) := by
  have hδ : 0 < δ := by linarith
  have h2 : 0 < log 2 := Real.log_pos one_lt_two
  have hlog : 2 * log 2 ≤ log (δ / ε) := by
    have hpow : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by norm_num
    rw [← Real.log_rpow two_pos, hpow]
    exact Real.log_le_log (by norm_num) ((le_div_iff₀ hε).2 h4)
  unfold logProfileDeriv
  rw [logCutoffConst_def]
  apply div_le_div_of_nonneg_right _ (log_div_pos hε (by linarith)).le
  have hge : 2 ≤ (u - log ε) / log 2 + (log δ - u) / log 2 := by
    rw [← add_div, le_div_iff₀ h2]
    rw [Real.log_div hδ.ne' hε.ne'] at hlog
    linarith
  rcases le_or_gt 1 ((u - log ε) / log 2) with h | h
  · rw [smoothTransition.one_of_one_le h, smoothTransition.deriv_of_one_le h]
    linarith [smoothTransition.le_one ((log δ - u) / log 2),
      smoothTransition.mul_deriv_le_deriv ((log δ - u) / log 2),
      smoothTransition.deriv_le_iSup ((log δ - u) / log 2)]
  · have h' : 1 ≤ (log δ - u) / log 2 := by linarith
    rw [smoothTransition.one_of_one_le h', smoothTransition.deriv_of_one_le h']
    linarith [smoothTransition.le_one ((u - log ε) / log 2),
      smoothTransition.mul_deriv_le_deriv ((u - log ε) / log 2),
      smoothTransition.deriv_le_iSup ((u - log ε) / log 2)]

private theorem logCutoffProfile_eq_logProfile (hδ : δ ≠ 0) (hr : 0 < r) :
    logCutoffProfile ε δ r = logProfile ε δ (log r) := by
  unfold logCutoffProfile logProfile
  rcases eq_or_ne ε 0 with rfl | hε
  · simp [hr.not_ge, Real.logb, Real.log_div hδ hr.ne']
  · rw [ite_eq_right hr.not_ge, Real.logb, Real.logb, Real.log_div hr.ne' hε,
      Real.log_div hδ hr.ne']

private theorem logCutoffProfile_eventuallyEq (hδ : δ ≠ 0) (hr : 0 < r) :
    logCutoffProfile ε δ =ᶠ[𝓝 r] logProfile ε δ ∘ log := by
  filter_upwards [lt_mem_nhds hr] with s hs
  exact logCutoffProfile_eq_logProfile hδ hs

private theorem logCutoffProfile_eq_one_sub_of_log_eq_zero (hΛ : log (δ / ε) = 0) (hr : 0 < r) :
    logCutoffProfile ε δ r = 1 - smoothTransition (Real.logb 2 (δ / r)) := by
  simp [logCutoffProfile_def, hr.not_ge, hΛ]

private theorem deriv_logCutoffProfile_eq (hΛ : log (δ / ε) ≠ 0) (hr : 0 < r) :
    deriv (logCutoffProfile ε δ) r = logProfileDeriv ε δ (log r) / r := by
  have hδ : δ ≠ 0 := fun h ↦ hΛ (by simp [h])
  have hd := (hasDerivAt_logProfile hΛ (log r)).comp r (Real.hasDerivAt_log hr.ne')
  rw [← div_eq_mul_inv] at hd
  exact (hd.congr_of_eventuallyEq (logCutoffProfile_eventuallyEq hδ hr)).deriv

end LogVariable

/-! ### Pointwise formulas and values -/

/-- The logarithmic cutoff profile vanishes at every nonpositive radius. -/
@[simp]
theorem logCutoffProfile_of_nonpos (hr : r ≤ 0) : logCutoffProfile ε δ r = 0 := by
  rw [logCutoffProfile_def, ite_eq_left hr]

/-- For `0 < r ≤ δ / 2`, the profile is `λ(r) τ(log₂ (r / ε))` (both sides are `0` when
`log (δ / ε) = 0` under Lean's totalized division `x / 0 = 0`). -/
theorem logCutoffProfile_of_le_half (hr0 : 0 < r) (hr : r ≤ δ / 2) :
    logCutoffProfile ε δ r =
      Real.log (r / ε) / Real.log (δ / ε) * smoothTransition (Real.logb 2 (r / ε)) := by
  rw [logCutoffProfile_def, ite_eq_right hr0.not_ge,
    smoothTransition.one_of_one_le (one_le_logb_two hr0 (by linarith))]
  ring

/-- For `2ε ≤ r` and `ε > 0`, the profile is `1 - (1 - λ(r)) τ(log₂ (δ / r))`, with `λ(r) = 0`
when `log (δ / ε) = 0` under Lean's totalized division `x / 0 = 0`. -/
theorem logCutoffProfile_of_two_mul_le (hε : 0 < ε) (hr : 2 * ε ≤ r) :
    logCutoffProfile ε δ r =
      1 - (1 - Real.log (r / ε) / Real.log (δ / ε)) *
        smoothTransition (Real.logb 2 (δ / r)) := by
  have hr0 : 0 < r := by linarith
  rw [logCutoffProfile_def, ite_eq_right hr0.not_ge,
    smoothTransition.one_of_one_le (one_le_logb_two hε hr)]
  ring

/-- For `2ε ≤ δ`, the logarithmic cutoff profile vanishes on `(-∞, ε]`. -/
@[simp]
theorem logCutoffProfile_eq_zero_of_le (hεδ : 2 * ε ≤ δ) (hr : r ≤ ε) :
    logCutoffProfile ε δ r = 0 := by
  rcases le_or_gt r 0 with hr0 | hr0
  · exact logCutoffProfile_of_nonpos hr0
  have hε : 0 < ε := hr0.trans_le hr
  rw [logCutoffProfile_of_le_half hr0 (by linarith),
    smoothTransition.zero_of_nonpos (Real.logb_nonpos one_lt_two (by positivity)
      ((div_le_one hε).2 hr)), mul_zero]

/-- For `0 < 2ε ≤ δ`, the logarithmic cutoff profile equals `1` on `[δ, ∞)`. -/
@[simp]
theorem logCutoffProfile_eq_one_of_ge (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (hr : δ ≤ r) :
    logCutoffProfile ε δ r = 1 := by
  have hδ : 0 < δ := by linarith
  have hr0 : 0 < r := hδ.trans_le hr
  rw [logCutoffProfile_of_two_mul_le hε (by linarith),
    smoothTransition.zero_of_nonpos (Real.logb_nonpos one_lt_two (by positivity)
      ((div_le_one hr0).2 hr)), mul_zero, sub_zero]

/-- On `[2ε, δ / 2]` the logarithmic cutoff profile is the logarithmic interpolation. -/
theorem logCutoffProfile_of_mem_Icc (hε : 0 < ε) (hr : r ∈ Icc (2 * ε) (δ / 2)) :
    logCutoffProfile ε δ r = Real.log (r / ε) / Real.log (δ / ε) := by
  rw [logCutoffProfile_of_le_half (by linarith [hr.1]) hr.2,
    smoothTransition.one_of_one_le (one_le_logb_two hε hr.1), mul_one]

/-! ### Smoothness, monotonicity, and bounds -/

private theorem logCutoffProfile_eventuallyEq_zero (hδ : δ ≠ 0) (hr : r ≤ 0) :
    logCutoffProfile ε δ =ᶠ[𝓝 r] fun _ ↦ 0 := by
  have hm : 0 < if ε = 0 then |δ| / 2 else min |ε| (|δ| / 2) := by
    split_ifs with hε
    · positivity
    · exact lt_min (abs_pos.2 hε) (by positivity)
  filter_upwards [gt_mem_nhds (hr.trans_lt hm)] with s hs
  rcases le_or_gt s 0 with hs0 | hs0
  · exact logCutoffProfile_of_nonpos hs0
  have hsδ : s ≤ |δ| / 2 := by
    split_ifs at hs with hε
    · exact hs.le
    · exact hs.le.trans (min_le_right _ _)
  have hb : 1 ≤ Real.logb 2 (δ / s) := by
    rw [← Real.logb_abs, abs_div, abs_of_pos hs0]
    exact one_le_logb_two hs0 (by linarith)
  rw [logCutoffProfile_def, ite_eq_right hs0.not_ge, smoothTransition.one_of_one_le hb,
    sub_self, mul_zero, add_zero]
  rcases eq_or_ne ε 0 with rfl | hε
  · simp
  · simp only [hε, ↓reduceIte] at hs
    have ha : Real.logb 2 (s / ε) ≤ 0 :=
      logb_two_div_nonpos_of_abs_le (by rw [abs_of_pos hs0]; exact hs.le.trans (min_le_left _ _))
    rw [smoothTransition.zero_of_nonpos ha, mul_zero]

private theorem logCutoffProfile_eventuallyEq_one
    (hΛ : log (δ / ε) = 0) (hr : |δ| < r) :
    logCutoffProfile ε δ =ᶠ[𝓝 r] fun _ ↦ 1 := by
  filter_upwards [lt_mem_nhds hr] with s hs
  have hs0 : 0 < s := (abs_nonneg δ).trans_lt hs
  rw [logCutoffProfile_eq_one_sub_of_log_eq_zero hΛ hs0,
    smoothTransition.zero_of_nonpos
      (logb_two_div_nonpos_of_abs_le (by rw [abs_of_pos hs0]; exact hs.le)), sub_zero]

private theorem deriv_logCutoffProfile_of_nonpos (hr : r ≤ 0) :
    deriv (logCutoffProfile ε δ) r = 0 := by
  rcases lt_or_eq_of_le hr with hr0 | rfl
  · rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
    filter_upwards [gt_mem_nhds hr0] with s hs
    exact logCutoffProfile_of_nonpos hs.le
  · rcases eq_or_ne δ 0 with rfl | hδ
    · refine deriv_zero_of_not_differentiableAt fun hd ↦ ?_
      have h1 : Tendsto (logCutoffProfile ε 0) (𝓝[>] 0) (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp [logCutoffProfile_def, hs.not_ge]
      have h0 : Tendsto (logCutoffProfile ε 0) (𝓝[>] 0) (𝓝 0) := by
        simpa [logCutoffProfile_of_nonpos le_rfl] using
          hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact one_ne_zero (tendsto_nhds_unique h1 h0)
    · rw [(logCutoffProfile_eventuallyEq_zero hδ le_rfl).deriv_eq, deriv_const]

/-- For `δ ≠ 0`, the logarithmic cutoff profile is smooth. -/
theorem contDiff_logCutoffProfile (hδ : δ ≠ 0) : ContDiff ℝ ∞ (logCutoffProfile ε δ) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  rcases lt_or_ge 0 r with hr | hr
  · exact (contDiff_logProfile.contDiffAt.comp r
      (Real.contDiffAt_log.2 hr.ne')).congr_of_eventuallyEq (logCutoffProfile_eventuallyEq hδ hr)
  · exact contDiffAt_const.congr_of_eventuallyEq (logCutoffProfile_eventuallyEq_zero hδ hr)

/-- The derivative of the logarithmic cutoff profile is nonnegative. -/
theorem deriv_logCutoffProfile_nonneg (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (r : ℝ) :
    0 ≤ deriv (logCutoffProfile ε δ) r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [deriv_logCutoffProfile_of_nonpos hr]
  · rw [deriv_logCutoffProfile_eq (log_div_pos hε hεδ).ne' hr]
    exact div_nonneg (logProfileDeriv_nonneg hε hεδ _) hr.le

/-- The logarithmic cutoff profile is nondecreasing. -/
theorem monotone_logCutoffProfile (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) :
    Monotone (logCutoffProfile ε δ) :=
  monotone_of_deriv_nonneg
    ((contDiff_logCutoffProfile (by linarith : δ ≠ 0)).differentiable (by simp))
    (deriv_logCutoffProfile_nonneg hε hεδ)

/-- The logarithmic cutoff profile is nonnegative. -/
theorem logCutoffProfile_nonneg (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (r : ℝ) :
    0 ≤ logCutoffProfile ε δ r := by
  rcases le_total r ε with hr | hr
  · rw [logCutoffProfile_eq_zero_of_le hεδ hr]
  · exact (logCutoffProfile_eq_zero_of_le hεδ le_rfl).symm.trans_le
      (monotone_logCutoffProfile hε hεδ hr)

/-- For `2ε ≤ δ` and `r ≤ ε`, Lean's `deriv (logCutoffProfile ε δ) r` is `0`; at the degenerate
triple `ε = δ = r = 0` the profile has a jump discontinuity from `0` to `1` and this is `deriv`'s
default value. -/
@[simp]
theorem deriv_logCutoffProfile_eq_zero_of_le (hεδ : 2 * ε ≤ δ) (hr : r ≤ ε) :
    deriv (logCutoffProfile ε δ) r = 0 := by
  rcases lt_or_ge 0 ε with hε | hε
  · apply IsLocalMin.deriv_eq_zero
    filter_upwards with s
    rw [logCutoffProfile_eq_zero_of_le hεδ hr]
    exact logCutoffProfile_nonneg hε hεδ s
  · exact deriv_logCutoffProfile_of_nonpos (hr.trans hε)

/-- The logarithmic cutoff profile is at most `1`. -/
theorem logCutoffProfile_le_one (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (r : ℝ) :
    logCutoffProfile ε δ r ≤ 1 := by
  rcases le_total δ r with hr | hr
  · rw [logCutoffProfile_eq_one_of_ge hε hεδ hr]
  · exact (monotone_logCutoffProfile hε hεδ hr).trans
      (logCutoffProfile_eq_one_of_ge hε hεδ le_rfl).le

/-- The derivative of the logarithmic cutoff profile vanishes on `[δ, ∞)`. -/
@[simp]
theorem deriv_logCutoffProfile_eq_zero_of_ge (hε : 0 < ε) (hεδ : 2 * ε ≤ δ)
    (hr : δ ≤ r) : deriv (logCutoffProfile ε δ) r = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with s
  rw [logCutoffProfile_eq_one_of_ge hε hεδ hr]
  exact logCutoffProfile_le_one hε hεδ s

/-! ### Derivative formulas and estimates -/

/-- The derivative bound `ψ'(r) ≤ c₀ / (r log (δ / ε))` for `0 < 4ε ≤ δ` and `r > 0`. At `r = 0`,
the derivative is `0` and the right-hand side is `0` by Lean's totalized division `x / 0 = 0`.
See `deriv_logCutoffProfile_nonneg` for the lower bound. -/
theorem deriv_logCutoffProfile_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ) (hr : 0 ≤ r) :
    deriv (logCutoffProfile ε δ) r ≤ logCutoffConst / (r * Real.log (δ / ε)) := by
  rcases hr.eq_or_lt with rfl | hr0
  · simp [deriv_logCutoffProfile_eq_zero_of_le (by linarith : 2 * ε ≤ δ) hε.le]
  · rw [deriv_logCutoffProfile_eq (log_div_pos hε (by linarith)).ne' hr0, mul_comm r, ← div_div]
    exact div_le_div_of_nonneg_right (logProfileDeriv_le hε h4 _) hr0.le

private theorem deriv_logCutoffProfile_of_log_eq_zero_of_le_half
    (hΛ : log (δ / ε) = 0) (hr : r ≤ δ / 2) :
    deriv (logCutoffProfile ε δ) r = 0 := by
  rcases lt_or_ge 0 r with hr0 | hr0
  · have hδ : 0 < δ := by linarith
    have hb : 1 ≤ (log δ - log r) / log 2 := one_le_sub_log_div_log_two hr0 (by linarith)
    have hev : logCutoffProfile ε δ =ᶠ[𝓝 r]
        fun s ↦ 1 - smoothTransition ((log δ - log s) / log 2) := by
      filter_upwards [lt_mem_nhds hr0] with s hs
      rw [logCutoffProfile_eq_one_sub_of_log_eq_zero hΛ hs, Real.logb, Real.log_div hδ.ne' hs.ne']
    have harg : HasDerivAt (fun s ↦ (log δ - log s) / log 2) (-(r⁻¹) / log 2) r :=
      ((Real.hasDerivAt_log hr0.ne').const_sub _).div_const _
    have hd := (harg.smoothTransition.const_sub 1).congr_of_eventuallyEq hev
    rw [hd.deriv, smoothTransition.deriv_of_one_le hb, zero_mul, neg_zero]
  · exact deriv_logCutoffProfile_of_nonpos hr0

/-- For `0 < r ≤ δ / 2`, the derivative is `(τ(a) + a τ'(a)) / (r log (δ / ε))` with
`a = log₂ (r / ε)` when `log (δ / ε) ≠ 0`. When `log (δ / ε) = 0` (`ε = 0` or `|ε| = δ`), the
derivative at `r` is `0`, matching the right-hand side under Lean's totalized division
`x / 0 = 0`. -/
theorem deriv_logCutoffProfile_of_le_half (hr0 : 0 < r) (hr : r ≤ δ / 2) :
    deriv (logCutoffProfile ε δ) r =
      (smoothTransition (Real.logb 2 (r / ε)) +
        Real.logb 2 (r / ε) * deriv smoothTransition (Real.logb 2 (r / ε))) /
        (r * Real.log (δ / ε)) := by
  by_cases hΛ : Real.log (δ / ε) = 0
  · rw [hΛ, mul_zero, div_zero, deriv_logCutoffProfile_of_log_eq_zero_of_le_half hΛ hr]
  · have hε : ε ≠ 0 := fun h ↦ hΛ (by simp [h])
    have hb : 1 ≤ (log δ - log r) / log 2 := one_le_sub_log_div_log_two hr0 (by linarith)
    rw [deriv_logCutoffProfile_eq hΛ hr0]
    unfold logProfileDeriv
    rw [smoothTransition.one_of_one_le hb, smoothTransition.deriv_of_one_le hb, Real.logb,
      Real.log_div hr0.ne' hε]
    field_simp
    ring

/-- For `0 < ε` and `2ε ≤ r`, `deriv (logCutoffProfile ε δ) r` equals
`(τ(b) + b τ'(b)) / (r log (δ / ε))` with `b = log₂ (δ / r)` when `log (δ / ε) ≠ 0`. When
`log (δ / ε) = 0` (`δ = 0` or `|δ| = ε`), both sides are `0` under Lean's totalized division
`x / 0 = 0`. -/
theorem deriv_logCutoffProfile_of_two_mul_le (hε : 0 < ε) (hr : 2 * ε ≤ r) :
    deriv (logCutoffProfile ε δ) r =
      (smoothTransition (Real.logb 2 (δ / r)) +
        Real.logb 2 (δ / r) * deriv smoothTransition (Real.logb 2 (δ / r))) /
        (r * Real.log (δ / ε)) := by
  by_cases hΛ : Real.log (δ / ε) = 0
  · have hδ_le : |δ| ≤ ε := abs_le_of_log_div_eq_zero hε hΛ
    rw [hΛ, mul_zero, div_zero,
      (logCutoffProfile_eventuallyEq_one hΛ (by linarith)).deriv_eq, deriv_const]
  · have hr0 : 0 < r := by linarith
    have hδ : δ ≠ 0 := fun h ↦ hΛ (by simp [h])
    have ha : 1 ≤ (log r - log ε) / log 2 := one_le_sub_log_div_log_two hε hr
    rw [deriv_logCutoffProfile_eq hΛ hr0]
    unfold logProfileDeriv
    rw [smoothTransition.one_of_one_le ha, smoothTransition.deriv_of_one_le ha, Real.logb,
      Real.log_div hδ hr0.ne']
    field_simp
    ring

/-- On `[2ε, δ / 2]` the derivative of the logarithmic cutoff profile is
`1 / (r log (δ / ε))`. -/
theorem deriv_logCutoffProfile_of_mem_Icc (hε : 0 < ε) (hr : r ∈ Icc (2 * ε) (δ / 2)) :
    deriv (logCutoffProfile ε δ) r = 1 / (r * Real.log (δ / ε)) := by
  have ha := one_le_logb_two hε hr.1
  rw [deriv_logCutoffProfile_of_le_half (by linarith [hr.1]) hr.2,
    smoothTransition.one_of_one_le ha, smoothTransition.deriv_of_one_le ha, mul_zero, add_zero]

/-- For `0 < 2ε ≤ δ` and `0 < r ≤ δ`, the defect `1 - ψ(r)` is at most
`log (2δ / r) / log (δ / ε)`. -/
theorem one_sub_logCutoffProfile_le (hε : 0 < ε) (hεδ : 2 * ε ≤ δ)
    (hr : 0 < r) (hrδ : r ≤ δ) :
    1 - logCutoffProfile ε δ r ≤ Real.log (2 * δ / r) / Real.log (δ / ε) := by
  have hδ : 0 < δ := by linarith
  have hΛ : 0 < Real.log (δ / ε) := log_div_pos hε hεδ
  by_cases hr2 : 2 * ε ≤ r
  · rw [logCutoffProfile_of_two_mul_le hε hr2, sub_sub_cancel]
    have hsub :
        1 - Real.log (r / ε) / Real.log (δ / ε) = Real.log (δ / r) / Real.log (δ / ε) := by
      rw [one_sub_div hΛ.ne', Real.log_div hδ.ne' hε.ne', Real.log_div hr.ne' hε.ne',
        Real.log_div hδ.ne' hr.ne']
      ring
    have hnn : 0 ≤ Real.log (δ / r) / Real.log (δ / ε) :=
      div_nonneg (Real.log_nonneg ((one_le_div hr).2 hrδ)) hΛ.le
    rw [hsub]
    calc Real.log (δ / r) / Real.log (δ / ε) * smoothTransition (Real.logb 2 (δ / r))
        ≤ Real.log (δ / r) / Real.log (δ / ε) :=
          mul_le_of_le_one_right hnn (smoothTransition.le_one _)
      _ ≤ Real.log (2 * δ / r) / Real.log (δ / ε) :=
          div_le_div_of_nonneg_right
            (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) hr.le))
            hΛ.le
  · have hle : 1 ≤ Real.log (2 * δ / r) / Real.log (δ / ε) := by
      rw [one_le_div hΛ]
      exact Real.log_le_log (by positivity)
        ((div_le_div_iff₀ hε hr).2 (by nlinarith))
    linarith [logCutoffProfile_nonneg hε hεδ r]

end TauCeti
