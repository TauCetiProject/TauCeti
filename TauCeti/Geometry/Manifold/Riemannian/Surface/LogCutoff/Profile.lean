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
`ψ'(r) ≤ c₀ / (r Λ)` for `r > 0`, with `c₀ = 1 + sup τ'`. This bound makes its Dirichlet
energy on a surface of order `1 / Λ`.

## Main definitions

* `TauCeti.logCutoffProfile ε δ`: the profile `ψ`.
* `TauCeti.logCutoffConst`: the constant `c₀ = 1 + sup τ'`.

## Main results

* `TauCeti.contDiff_logCutoffProfile`: `ψ` is smooth.
* `TauCeti.monotone_logCutoffProfile`: `ψ` is nondecreasing.
* `TauCeti.deriv_logCutoffProfile_le`: `ψ'(r) ≤ c₀ / (r Λ)` for `r > 0`.
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
  rw [abs_of_nonneg (smoothTransition.deriv_nonneg t)]
  rw [logCutoffConst_def]
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

private theorem one_le_sub_log_div_log_two (hε : 0 < ε) (hr : 2 * ε ≤ r) :
    1 ≤ (log r - log ε) / log 2 := by
  have hr0 : 0 < r := by linarith
  rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_div hr0.ne' hε.ne']
  simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hε).2 hr)

variable (hε : 0 < ε) (hεδ : 2 * ε ≤ δ)
include hε hεδ

private theorem pos_of_two_mul_le : 0 < δ := by linarith

private theorem log_div_eq : log (δ / ε) = log δ - log ε :=
  Real.log_div (pos_of_two_mul_le hε hεδ).ne' hε.ne'

private theorem log_two_le : log 2 ≤ log (δ / ε) :=
  Real.log_le_log two_pos ((le_div_iff₀ hε).2 hεδ)

private theorem log_div_pos : 0 < log (δ / ε) :=
  (Real.log_pos one_lt_two).trans_le (log_two_le hε hεδ)

omit hε hεδ in
private theorem logProfile_eq_of_one_le_left {u : ℝ} (hu : 1 ≤ (u - log ε) / log 2) :
    logProfile ε δ u =
      1 - (1 - (u - log ε) / log (δ / ε)) * smoothTransition ((log δ - u) / log 2) := by
  unfold logProfile
  rw [smoothTransition.one_of_one_le hu]
  ring

omit hε hεδ in
private theorem contDiff_logProfile : ContDiff ℝ ∞ (logProfile ε δ) := by
  have hτ : ContDiff ℝ ∞ smoothTransition := smoothTransition.contDiff
  have ha : ContDiff ℝ ∞ fun u : ℝ ↦ (u - log ε) / log 2 :=
    (contDiff_id.sub contDiff_const).div_const _
  have hb : ContDiff ℝ ∞ fun u : ℝ ↦ (log δ - u) / log 2 :=
    (contDiff_const.sub contDiff_id).div_const _
  have hl : ContDiff ℝ ∞ fun u : ℝ ↦ (u - log ε) / log (δ / ε) :=
    (contDiff_id.sub contDiff_const).div_const _
  exact (hl.mul (hτ.comp ha)).add ((contDiff_const.sub hl).mul (contDiff_const.sub (hτ.comp hb)))

omit hεδ in
private theorem hasDerivAt_logProfile (hδ : 0 < δ) (hne : δ ≠ ε) (u : ℝ) :
    HasDerivAt (logProfile ε δ) (logProfileDeriv ε δ u) u := by
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
  have hΛ : log (δ / ε) ≠ 0 := by
    rw [Real.log_div hδ.ne' hε.ne', sub_ne_zero]
    exact fun h ↦ hne (Real.log_injOn_pos hδ hε h)
  unfold logProfileDeriv
  rw [Real.log_div hδ.ne' hε.ne'] at hΛ ⊢
  field_simp
  ring

private theorem logProfileDeriv_nonneg (u : ℝ) : 0 ≤ logProfileDeriv ε δ u := by
  unfold logProfileDeriv
  apply div_nonneg _ (log_div_pos hε hεδ).le
  have hsum : 0 ≤ smoothTransition ((u - log ε) / log 2) +
      smoothTransition ((log δ - u) / log 2) - 1 := by
    have h2 := Real.log_pos one_lt_two
    have hge : 1 ≤ (u - log ε) / log 2 + (log δ - u) / log 2 := by
      rw [← add_div, le_div_iff₀ h2]
      have := log_two_le hε hεδ
      rw [log_div_eq hε hεδ] at this
      linarith
    have hm := smoothTransition.monotone (by linarith :
      1 - (u - log ε) / log 2 ≤ (log δ - u) / log 2)
    rw [smoothTransition.one_sub] at hm
    linarith
  linarith [smoothTransition.mul_deriv_nonneg ((u - log ε) / log 2),
    smoothTransition.mul_deriv_nonneg ((log δ - u) / log 2)]

omit hεδ in
private theorem logProfileDeriv_le (h4 : 4 * ε ≤ δ) (u : ℝ) :
    logProfileDeriv ε δ u ≤ logCutoffConst / log (δ / ε) := by
  unfold logProfileDeriv
  rw [logCutoffConst_def]
  have hεδ : 2 * ε ≤ δ := by linarith
  apply div_le_div_of_nonneg_right _ (log_div_pos hε hεδ).le
  have h2 := Real.log_pos one_lt_two
  have hge : 2 ≤ (u - log ε) / log 2 + (log δ - u) / log 2 := by
    rw [← add_div, le_div_iff₀ h2]
    have hpow : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by norm_num
    have hlog : 2 * log 2 ≤ log (δ / ε) := by
      rw [← Real.log_rpow two_pos, hpow]
      exact Real.log_le_log (by norm_num) ((le_div_iff₀ hε).2 h4)
    rw [log_div_eq hε hεδ] at hlog
    linarith
  have hor : 1 ≤ (u - log ε) / log 2 ∨ 1 ≤ (log δ - u) / log 2 := by
    by_contra! h
    linarith [h.1, h.2]
  rcases hor with h | h
  · rw [smoothTransition.one_of_one_le h, smoothTransition.deriv_of_one_le h]
    linarith [smoothTransition.le_one ((log δ - u) / log 2),
      smoothTransition.mul_deriv_le_deriv ((log δ - u) / log 2),
      smoothTransition.deriv_le_iSup ((log δ - u) / log 2)]
  · rw [smoothTransition.one_of_one_le h, smoothTransition.deriv_of_one_le h]
    linarith [smoothTransition.le_one ((u - log ε) / log 2),
      smoothTransition.mul_deriv_le_deriv ((u - log ε) / log 2),
      smoothTransition.deriv_le_iSup ((u - log ε) / log 2)]

omit hεδ in
private theorem logCutoffProfile_eq_logProfile (hδ : 0 < δ) (hr : 0 < r) :
    logCutoffProfile ε δ r = logProfile ε δ (log r) := by
  unfold logCutoffProfile logProfile
  rw [ite_eq_right hr.not_ge, Real.logb, Real.logb, Real.log_div hr.ne' hε.ne',
    Real.log_div hδ.ne' hr.ne']

omit hεδ in
private theorem logCutoffProfile_eventuallyEq (hδ : 0 < δ) (hr : 0 < r) :
    logCutoffProfile ε δ =ᶠ[𝓝 r] logProfile ε δ ∘ log := by
  filter_upwards [lt_mem_nhds hr] with s hs
  exact logCutoffProfile_eq_logProfile hε hδ hs

omit hεδ in
/-- The derivative of the logarithmic cutoff profile at a positive radius. -/
private theorem hasDerivAt_logCutoffProfile (hδ : 0 < δ) (hne : δ ≠ ε) (hr : 0 < r) :
    HasDerivAt (logCutoffProfile ε δ) (logProfileDeriv ε δ (log r) / r) r := by
  have hd := (hasDerivAt_logProfile hε hδ hne (log r)).comp r (Real.hasDerivAt_log hr.ne')
  rw [div_eq_mul_inv]
  exact hd.congr_of_eventuallyEq (logCutoffProfile_eventuallyEq hε hδ hr)

omit hεδ in
private theorem deriv_logCutoffProfile_eq (hδ : 0 < δ) (hne : δ ≠ ε) (hr : 0 < r) :
    deriv (logCutoffProfile ε δ) r = logProfileDeriv ε δ (log r) / r :=
  (hasDerivAt_logCutoffProfile hε hδ hne hr).deriv

end LogVariable

variable (hε : 0 < ε) (hεδ : 2 * ε ≤ δ)
include hε hεδ

omit hε hεδ in
/-- The logarithmic cutoff profile vanishes at every nonpositive radius. -/
@[simp]
theorem logCutoffProfile_of_nonpos (hr : r ≤ 0) : logCutoffProfile ε δ r = 0 := by
  rw [logCutoffProfile_def, ite_eq_left hr]

omit hε hεδ in
/-- For `0 < r ≤ δ / 2`, the profile is `λ(r) τ(log₂ (r / ε))`. -/
theorem logCutoffProfile_of_le_half (hr0 : 0 < r) (hr : r ≤ δ / 2) :
    logCutoffProfile ε δ r =
      Real.log (r / ε) / Real.log (δ / ε) * smoothTransition (Real.logb 2 (r / ε)) := by
  have hδ : 0 < δ := by linarith
  have hb := one_le_sub_log_div_log_two hr0 (by linarith : 2 * r ≤ δ)
  rw [← Real.log_div hδ.ne' hr0.ne'] at hb
  rw [logCutoffProfile_def, ite_eq_right hr0.not_ge]
  simp only [Real.logb]
  rw [smoothTransition.one_of_one_le hb]
  ring

omit hεδ in
/-- For `2ε ≤ r` and `ε > 0`, the profile is `1 - (1 - λ(r)) τ(log₂ (δ / r))`. -/
theorem logCutoffProfile_of_two_mul_le (hr : 2 * ε ≤ r) :
    logCutoffProfile ε δ r =
      1 - (1 - Real.log (r / ε) / Real.log (δ / ε)) * smoothTransition (Real.logb 2 (δ / r)) := by
  have hr0 : 0 < r := by linarith
  have ha := one_le_sub_log_div_log_two hε hr
  rw [← Real.log_div hr0.ne' hε.ne'] at ha
  rw [logCutoffProfile_def, ite_eq_right hr0.not_ge, Real.logb,
    smoothTransition.one_of_one_le ha]
  ring

/-- For `0 < 2ε ≤ δ`, the logarithmic cutoff profile vanishes on `(-∞, ε]`. -/
@[simp]
theorem logCutoffProfile_eq_zero_of_le (hr : r ≤ ε) : logCutoffProfile ε δ r = 0 := by
  rcases le_or_gt r 0 with hr0 | hr0
  · exact logCutoffProfile_of_nonpos hr0
  have hlog : log r ≤ log ε := Real.log_le_log hr0 hr
  rw [logCutoffProfile_of_le_half hr0 (by linarith), Real.logb,
    Real.log_div hr0.ne' hε.ne',
    smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (Real.log_pos one_lt_two).le), mul_zero]

/-- For `0 < 2ε ≤ δ`, the logarithmic cutoff profile equals `1` on `[δ, ∞)`. -/
@[simp]
theorem logCutoffProfile_eq_one_of_ge (hr : δ ≤ r) : logCutoffProfile ε δ r = 1 := by
  have hδ := pos_of_two_mul_le hε hεδ
  have hr0 := hδ.trans_le hr
  have hlog : log δ ≤ log r := Real.log_le_log hδ hr
  rw [logCutoffProfile_of_two_mul_le hε (by linarith), Real.logb,
    Real.log_div hδ.ne' hr0.ne',
    smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (Real.log_pos one_lt_two).le), mul_zero, sub_zero]

omit hεδ in
/-- On `[2ε, δ / 2]` the logarithmic cutoff profile is the logarithmic interpolation. -/
theorem logCutoffProfile_of_mem_Icc (hr : r ∈ Icc (2 * ε) (δ / 2)) :
    logCutoffProfile ε δ r = Real.log (r / ε) / Real.log (δ / ε) := by
  have hr0 : 0 < r := by linarith [hr.1]
  have ha := one_le_sub_log_div_log_two hε hr.1
  rw [← Real.log_div hr0.ne' hε.ne'] at ha
  rw [logCutoffProfile_of_le_half hr0 hr.2, Real.logb,
    smoothTransition.one_of_one_le ha, mul_one]

omit hεδ in
/-- The logarithmic cutoff profile is smooth. -/
theorem contDiff_logCutoffProfile (hδ : 0 < δ) : ContDiff ℝ ∞ (logCutoffProfile ε δ) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  rcases lt_or_ge 0 r with hr | hr
  · have hlog : ContDiffAt ℝ ∞ log r := Real.contDiffAt_log.2 hr.ne'
    exact (contDiff_logProfile.contDiffAt.comp r hlog).congr_of_eventuallyEq
      (logCutoffProfile_eventuallyEq hε hδ hr)
  · apply contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq
    have hm : 0 < min ε (δ / 2) := lt_min hε (by positivity)
    filter_upwards [gt_mem_nhds (hr.trans_lt hm)] with s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · exact logCutoffProfile_of_nonpos hs0
    · rw [logCutoffProfile_of_le_half hs0 (hs.le.trans (min_le_right _ _)), Real.logb,
        Real.log_div hs0.ne' hε.ne',
        smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.2 (Real.log_le_log hs0 (hs.le.trans (min_le_left _ _))))
          (Real.log_pos one_lt_two).le), mul_zero]

/-- The derivative of the logarithmic cutoff profile is nonnegative. -/
theorem deriv_logCutoffProfile_nonneg (r : ℝ) : 0 ≤ deriv (logCutoffProfile ε δ) r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
    filter_upwards [gt_mem_nhds (hr.trans_lt hε)] with s hs
    exact logCutoffProfile_eq_zero_of_le hε hεδ hs.le
  · rw [deriv_logCutoffProfile_eq hε (pos_of_two_mul_le hε hεδ) (by linarith) hr]
    exact div_nonneg (logProfileDeriv_nonneg hε hεδ _) hr.le

/-- The logarithmic cutoff profile is nondecreasing. -/
theorem monotone_logCutoffProfile : Monotone (logCutoffProfile ε δ) :=
  monotone_of_deriv_nonneg
    ((contDiff_logCutoffProfile hε (pos_of_two_mul_le hε hεδ)).differentiable (by simp))
    (deriv_logCutoffProfile_nonneg hε hεδ)

/-- The logarithmic cutoff profile is nonnegative. -/
theorem logCutoffProfile_nonneg (r : ℝ) : 0 ≤ logCutoffProfile ε δ r := by
  rcases le_total r ε with hr | hr
  · rw [logCutoffProfile_eq_zero_of_le hε hεδ hr]
  · exact (logCutoffProfile_eq_zero_of_le hε hεδ le_rfl).symm.trans_le
      (monotone_logCutoffProfile hε hεδ hr)

/-- The derivative of the logarithmic cutoff profile vanishes on `(-∞, ε]`. -/
@[simp]
theorem deriv_logCutoffProfile_eq_zero_of_le (hr : r ≤ ε) :
    deriv (logCutoffProfile ε δ) r = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards with s
  rw [logCutoffProfile_eq_zero_of_le hε hεδ hr]
  exact logCutoffProfile_nonneg hε hεδ s

/-- The logarithmic cutoff profile is at most `1`. -/
theorem logCutoffProfile_le_one (r : ℝ) : logCutoffProfile ε δ r ≤ 1 := by
  rcases le_total δ r with hr | hr
  · rw [logCutoffProfile_eq_one_of_ge hε hεδ hr]
  · exact (monotone_logCutoffProfile hε hεδ hr).trans
      (logCutoffProfile_eq_one_of_ge hε hεδ le_rfl).le

/-- The derivative of the logarithmic cutoff profile vanishes on `[δ, ∞)`. -/
@[simp]
theorem deriv_logCutoffProfile_eq_zero_of_ge (hr : δ ≤ r) :
    deriv (logCutoffProfile ε δ) r = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with s
  rw [logCutoffProfile_eq_one_of_ge hε hεδ hr]
  exact logCutoffProfile_le_one hε hεδ s

omit hεδ in
/-- The derivative bound `ψ'(r) ≤ c₀ / (r log (δ / ε))` for `0 < 4ε ≤ δ` and `r > 0`.
See `deriv_logCutoffProfile_nonneg` for the lower bound. -/
theorem deriv_logCutoffProfile_le (h4 : 4 * ε ≤ δ) (hr : 0 < r) :
    deriv (logCutoffProfile ε δ) r ≤ logCutoffConst / (r * Real.log (δ / ε)) := by
  rw [deriv_logCutoffProfile_eq hε (by linarith) (by linarith) hr, mul_comm r, ← div_div]
  exact div_le_div_of_nonneg_right (logProfileDeriv_le hε h4 _) hr.le

omit hεδ in
/-- For distinct `ε, δ > 0` and `0 < r ≤ δ / 2`, the derivative is
`(τ(a) + a τ'(a)) / (r log (δ / ε))` with `a = log₂ (r / ε)`. -/
theorem deriv_logCutoffProfile_of_le_half (hne : δ ≠ ε) (hr0 : 0 < r) (hr : r ≤ δ / 2) :
    deriv (logCutoffProfile ε δ) r =
      (smoothTransition (Real.logb 2 (r / ε)) +
        Real.logb 2 (r / ε) * deriv smoothTransition (Real.logb 2 (r / ε))) /
        (r * Real.log (δ / ε)) := by
  have hδ : 0 < δ := by linarith
  have hb := one_le_sub_log_div_log_two hr0 (by linarith : 2 * r ≤ δ)
  rw [deriv_logCutoffProfile_eq hε hδ hne hr0]
  unfold logProfileDeriv
  rw [smoothTransition.one_of_one_le hb, smoothTransition.deriv_of_one_le hb, Real.logb,
    Real.log_div hr0.ne' hε.ne']
  field_simp
  ring

omit hεδ in
/-- For distinct `ε, δ > 0` and `2ε ≤ r`, the derivative is
`(τ(b) + b τ'(b)) / (r log (δ / ε))` with `b = log₂ (δ / r)`. -/
theorem deriv_logCutoffProfile_of_two_mul_le (hδ : 0 < δ) (hne : δ ≠ ε) (hr : 2 * ε ≤ r) :
    deriv (logCutoffProfile ε δ) r =
      (smoothTransition (Real.logb 2 (δ / r)) +
        Real.logb 2 (δ / r) * deriv smoothTransition (Real.logb 2 (δ / r))) /
        (r * Real.log (δ / ε)) := by
  have hr0 : 0 < r := by linarith
  have ha := one_le_sub_log_div_log_two hε hr
  rw [deriv_logCutoffProfile_eq hε hδ hne hr0]
  unfold logProfileDeriv
  rw [smoothTransition.one_of_one_le ha, smoothTransition.deriv_of_one_le ha, Real.logb,
    Real.log_div hδ.ne' hr0.ne']
  field_simp
  ring

omit hεδ in
/-- On `[2ε, δ / 2]` the derivative of the logarithmic cutoff profile is `1 / (r log (δ / ε))`. -/
theorem deriv_logCutoffProfile_of_mem_Icc (hr : r ∈ Icc (2 * ε) (δ / 2)) :
    deriv (logCutoffProfile ε δ) r = 1 / (r * Real.log (δ / ε)) := by
  have hr0 : 0 < r := by linarith [hr.1]
  have ha := one_le_sub_log_div_log_two hε hr.1
  rw [← Real.log_div hr0.ne' hε.ne'] at ha
  rw [deriv_logCutoffProfile_of_le_half hε (by linarith [hr.1, hr.2]) hr0 hr.2, Real.logb,
    smoothTransition.one_of_one_le ha, smoothTransition.deriv_of_one_le ha]
  simp

/-- For `0 < 2ε ≤ δ` and `0 < r ≤ δ`, the defect `1 - ψ(r)` is at most
`log (2δ / r) / log (δ / ε)`. -/
theorem one_sub_logCutoffProfile_le (hr : 0 < r) (hrδ : r ≤ δ) :
    1 - logCutoffProfile ε δ r ≤ Real.log (2 * δ / r) / Real.log (δ / ε) := by
  have hδ := pos_of_two_mul_le hε hεδ
  have hΛ := log_div_pos hε hεδ
  have h2 := Real.log_pos one_lt_two
  have hlog2 : Real.log (2 * δ / r) = log 2 + log δ - log r := by
    rw [Real.log_div (by positivity) hr.ne', Real.log_mul two_ne_zero hδ.ne']
  have hΛe := log_div_eq hε hεδ
  have hlr : log r ≤ log δ := Real.log_le_log hr hrδ
  rw [hlog2, le_div_iff₀ hΛ]
  by_cases ha : 1 ≤ (log r - log ε) / log 2
  · rw [logCutoffProfile_eq_logProfile hε hδ hr, logProfile_eq_of_one_le_left ha]
    have hτ := smoothTransition.le_one ((log δ - log r) / log 2)
    have h1 : 0 ≤ 1 - (log r - log ε) / log (δ / ε) := by
      rw [sub_nonneg, div_le_one hΛ, hΛe]
      linarith
    have hkey : (1 - (log r - log ε) / log (δ / ε)) * log (δ / ε) = log δ - log r := by
      field_simp
      rw [hΛe]
      ring
    nlinarith [mul_le_mul_of_nonneg_left hτ h1]
  · rw [not_le, div_lt_one h2] at ha
    have hp := logCutoffProfile_nonneg hε hεδ r
    rw [hΛe] at hΛ ⊢
    nlinarith [mul_nonneg hp hΛ.le]

end TauCeti
