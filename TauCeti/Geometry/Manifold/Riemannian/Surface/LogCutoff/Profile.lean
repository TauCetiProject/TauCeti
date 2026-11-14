/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The logarithmic cutoff profile

For `0 < 4ε ≤ δ`, put `Λ = log (δ / ε)` and `λ(r) = log (r / ε) / Λ`, and let `τ` be
`Real.smoothTransition`. The logarithmic cutoff profile is
`ψ(r) = λ(r) τ(log₂ (r / ε)) + (1 - λ(r)) (1 - τ(log₂ (δ / r)))` for `r > 0`, and `0` for
`r ≤ 0`. It is smooth and nondecreasing, vanishes on `(-∞, ε]`, equals `1` on `[δ, ∞)` and
equals the logarithmic interpolation `λ` on `[2ε, δ / 2]`. Its derivative satisfies
`0 ≤ ψ'(r) ≤ c₀ / (r Λ)` with `c₀ = 1 + sup τ'`, the bound that makes its Dirichlet energy on a
surface of order `1 / Λ`.

## Main definitions

* `TauCeti.logCutoffProfile ε δ`: the profile `ψ`.
* `TauCeti.logCutoffConst`: the constant `c₀ = 1 + sup τ'`.

## Main results

* `TauCeti.contDiff_logCutoffProfile`: `ψ` is smooth.
* `TauCeti.monotone_logCutoffProfile`: `ψ` is nondecreasing.
* `TauCeti.deriv_logCutoffProfile_le`: `ψ'(r) ≤ c₀ / (r Λ)` for `r > 0`.
* `TauCeti.deriv_logCutoffProfile_of_mem_Icc`: `ψ'(r) = 1 / (r Λ)` on `[2ε, δ / 2]`.

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
@[expose] def logCutoffProfile (ε δ r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else
    Real.log (r / ε) / Real.log (δ / ε) * smoothTransition (Real.logb 2 (r / ε)) +
      (1 - Real.log (r / ε) / Real.log (δ / ε)) *
        (1 - smoothTransition (Real.logb 2 (δ / r)))

/-- The constant `c₀ = 1 + sup τ'` of the derivative bound of the logarithmic cutoff profile,
where `τ` is `Real.smoothTransition`. -/
def logCutoffConst : ℝ :=
  1 + ⨆ t, deriv smoothTransition t

section SmoothTransition

/-- The derivative of `Real.smoothTransition` vanishes outside `(0, 1)`. -/
theorem deriv_smoothTransition_eq_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    deriv smoothTransition t = 0 := by
  rcases ht with ht | ht
  · apply IsLocalMin.deriv_eq_zero
    filter_upwards with s
    rw [smoothTransition.zero_of_nonpos ht]
    exact smoothTransition.nonneg s
  · apply IsLocalMax.deriv_eq_zero
    filter_upwards with s
    rw [smoothTransition.one_of_one_le ht]
    exact smoothTransition.le_one s

private theorem deriv_smoothTransition_nonneg (t : ℝ) : 0 ≤ deriv smoothTransition t :=
  smoothTransition.monotone.deriv_nonneg

private theorem bddAbove_range_deriv_smoothTransition :
    BddAbove (range (deriv smoothTransition)) := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max B 0, ?_⟩
  rintro _ ⟨t, rfl⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hB (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  · rw [deriv_smoothTransition_eq_zero]
    · exact le_max_right _ _
    · simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact Or.inl ht.le
      · exact Or.inr ht.le

private theorem deriv_smoothTransition_le (t : ℝ) :
    deriv smoothTransition t ≤ ⨆ s, deriv smoothTransition s :=
  le_ciSup bddAbove_range_deriv_smoothTransition t

private theorem iSup_deriv_smoothTransition_nonneg : 0 ≤ ⨆ s, deriv smoothTransition s :=
  (deriv_smoothTransition_nonneg 0).trans (deriv_smoothTransition_le 0)

/-- The constant of the derivative bound is at least one. -/
theorem one_le_logCutoffConst : 1 ≤ logCutoffConst := by
  unfold logCutoffConst
  linarith [iSup_deriv_smoothTransition_nonneg]

/-- The constant of the derivative bound is positive. -/
theorem logCutoffConst_pos : 0 < logCutoffConst :=
  zero_lt_one.trans_le one_le_logCutoffConst

/-- The derivative of `Real.smoothTransition` lies in `[0, c₀]`. -/
theorem abs_deriv_smoothTransition_le (t : ℝ) : |deriv smoothTransition t| ≤ logCutoffConst := by
  rw [abs_of_nonneg (deriv_smoothTransition_nonneg t)]
  unfold logCutoffConst
  linarith [deriv_smoothTransition_le t]

private theorem mul_deriv_smoothTransition_nonneg (t : ℝ) :
    0 ≤ t * deriv smoothTransition t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [deriv_smoothTransition_eq_zero (Or.inl ht), mul_zero]
  · exact mul_nonneg ht.le (deriv_smoothTransition_nonneg t)

private theorem mul_deriv_smoothTransition_le (t : ℝ) :
    t * deriv smoothTransition t ≤ ⨆ s, deriv smoothTransition s := by
  rcases le_or_gt t 0 with ht | _ht
  · rw [deriv_smoothTransition_eq_zero (Or.inl ht), mul_zero]
    exact iSup_deriv_smoothTransition_nonneg
  rcases le_or_gt 1 t with ht1 | ht1
  · rw [deriv_smoothTransition_eq_zero (Or.inr ht1), mul_zero]
    exact iSup_deriv_smoothTransition_nonneg
  calc t * deriv smoothTransition t ≤ 1 * deriv smoothTransition t :=
        mul_le_mul_of_nonneg_right ht1.le (deriv_smoothTransition_nonneg t)
    _ = deriv smoothTransition t := one_mul _
    _ ≤ _ := deriv_smoothTransition_le t

end SmoothTransition

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

variable (hε : 0 < ε) (hεδ : 4 * ε ≤ δ)
include hε hεδ

private theorem pos_of_four_mul_le : 0 < δ := by linarith

private theorem log_div_eq : log (δ / ε) = log δ - log ε :=
  Real.log_div (pos_of_four_mul_le hε hεδ).ne' hε.ne'

private theorem two_mul_log_two_le : 2 * log 2 ≤ log (δ / ε) := by
  rw [← Real.log_rpow two_pos, show ((2 : ℝ) ^ (2 : ℝ)) = 4 by norm_num]
  exact Real.log_le_log (by norm_num) ((le_div_iff₀ hε).2 (by linarith))

private theorem log_div_pos : 0 < log (δ / ε) :=
  (mul_pos two_pos (Real.log_pos one_lt_two)).trans_le (two_mul_log_two_le hε hεδ)

private theorem one_le_or_one_le (u : ℝ) :
    1 ≤ (u - log ε) / log 2 ∨ 1 ≤ (log δ - u) / log 2 := by
  have h2 := Real.log_pos one_lt_two
  have hsum : (u - log ε) / log 2 + (log δ - u) / log 2 = log (δ / ε) / log 2 := by
    rw [log_div_eq hε hεδ]
    ring
  have hge : 2 ≤ log (δ / ε) / log 2 := (le_div_iff₀ h2).2 (two_mul_log_two_le hε hεδ)
  by_contra! h
  linarith [h.1, h.2]

omit hε hεδ in
private theorem logProfile_eq_of_one_le_left {u : ℝ} (hu : 1 ≤ (u - log ε) / log 2) :
    logProfile ε δ u =
      1 - (1 - (u - log ε) / log (δ / ε)) * smoothTransition ((log δ - u) / log 2) := by
  unfold logProfile
  rw [smoothTransition.one_of_one_le hu]
  ring

omit hε hεδ in
private theorem logProfile_eq_of_one_le_right {u : ℝ} (hu : 1 ≤ (log δ - u) / log 2) :
    logProfile ε δ u = (u - log ε) / log (δ / ε) * smoothTransition ((u - log ε) / log 2) := by
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

private theorem hasDerivAt_logProfile (u : ℝ) :
    HasDerivAt (logProfile ε δ) (logProfileDeriv ε δ u) u := by
  have hτ (t : ℝ) : HasDerivAt smoothTransition (deriv smoothTransition t) t :=
    ((smoothTransition.contDiff (n := 1)).differentiable (by norm_num) t).hasDerivAt
  have ha : HasDerivAt (fun u : ℝ ↦ (u - log ε) / log 2) (1 / log 2) u :=
    ((hasDerivAt_id u).sub_const _).div_const _
  have hb : HasDerivAt (fun u : ℝ ↦ (log δ - u) / log 2) (-1 / log 2) u :=
    ((hasDerivAt_id u).const_sub _).div_const _
  have hl : HasDerivAt (fun u : ℝ ↦ (u - log ε) / log (δ / ε)) (1 / log (δ / ε)) u :=
    ((hasDerivAt_id u).sub_const _).div_const _
  have hd := (hl.mul ((hτ _).comp u ha)).add
    ((hl.const_sub 1).mul (((hτ _).comp u hb).const_sub 1))
  have hd' : HasDerivAt (logProfile ε δ) _ u := hd
  convert hd' using 1
  have hΛ := (log_div_pos hε hεδ).ne'
  have h2 := (Real.log_pos one_lt_two).ne'
  unfold logProfileDeriv
  simp only [Function.comp_apply]
  rw [log_div_eq hε hεδ] at hΛ ⊢
  field_simp
  ring

private theorem logProfileDeriv_nonneg (u : ℝ) : 0 ≤ logProfileDeriv ε δ u := by
  unfold logProfileDeriv
  apply div_nonneg _ (log_div_pos hε hεδ).le
  have hsum : 0 ≤ smoothTransition ((u - log ε) / log 2) +
      smoothTransition ((log δ - u) / log 2) - 1 := by
    rcases one_le_or_one_le hε hεδ u with h | h
    · rw [smoothTransition.one_of_one_le h]
      linarith [smoothTransition.nonneg ((log δ - u) / log 2)]
    · rw [smoothTransition.one_of_one_le h]
      linarith [smoothTransition.nonneg ((u - log ε) / log 2)]
  linarith [mul_deriv_smoothTransition_nonneg ((u - log ε) / log 2),
    mul_deriv_smoothTransition_nonneg ((log δ - u) / log 2)]

private theorem logProfileDeriv_le (u : ℝ) :
    logProfileDeriv ε δ u ≤ logCutoffConst / log (δ / ε) := by
  unfold logProfileDeriv logCutoffConst
  apply div_le_div_of_nonneg_right _ (log_div_pos hε hεδ).le
  rcases one_le_or_one_le hε hεδ u with h | h
  · rw [smoothTransition.one_of_one_le h, deriv_smoothTransition_eq_zero (Or.inr h)]
    linarith [smoothTransition.le_one ((log δ - u) / log 2),
      mul_deriv_smoothTransition_le ((log δ - u) / log 2)]
  · rw [smoothTransition.one_of_one_le h, deriv_smoothTransition_eq_zero (Or.inr h)]
    linarith [smoothTransition.le_one ((u - log ε) / log 2),
      mul_deriv_smoothTransition_le ((u - log ε) / log 2)]

private theorem logCutoffProfile_eq_logProfile (hr : 0 < r) :
    logCutoffProfile ε δ r = logProfile ε δ (log r) := by
  have hδ := pos_of_four_mul_le hε hεδ
  unfold logCutoffProfile logProfile
  rw [ite_eq_right hr.not_ge, Real.logb, Real.logb, Real.log_div hr.ne' hε.ne',
    Real.log_div hδ.ne' hr.ne']

private theorem logCutoffProfile_eventuallyEq (hr : 0 < r) :
    logCutoffProfile ε δ =ᶠ[𝓝 r] logProfile ε δ ∘ log := by
  filter_upwards [lt_mem_nhds hr] with s hs
  exact logCutoffProfile_eq_logProfile hε hεδ hs

private theorem logCutoffProfile_eq_zero_of_le_aux (hr : r ≤ ε) : logCutoffProfile ε δ r = 0 := by
  rcases le_or_gt r 0 with hr0 | hr0
  · unfold logCutoffProfile
    rw [ite_eq_left hr0]
  have h2 := Real.log_pos one_lt_two
  have hlog : log r ≤ log ε := Real.log_le_log hr0 hr
  have hb : 1 ≤ (log δ - log r) / log 2 := by
    rw [le_div_iff₀ h2]
    have := two_mul_log_two_le hε hεδ
    rw [log_div_eq hε hεδ] at this
    linarith
  rw [logCutoffProfile_eq_logProfile hε hεδ hr0, logProfile_eq_of_one_le_right hb,
    smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le),
    mul_zero]

/-- The derivative of the logarithmic cutoff profile at a positive radius. -/
private theorem hasDerivAt_logCutoffProfile (hr : 0 < r) :
    HasDerivAt (logCutoffProfile ε δ) (logProfileDeriv ε δ (log r) / r) r := by
  have hd := (hasDerivAt_logProfile hε hεδ (log r)).comp r (Real.hasDerivAt_log hr.ne')
  rw [div_eq_mul_inv]
  exact hd.congr_of_eventuallyEq (logCutoffProfile_eventuallyEq hε hεδ hr)

private theorem deriv_logCutoffProfile_eq (hr : 0 < r) :
    deriv (logCutoffProfile ε δ) r = logProfileDeriv ε δ (log r) / r :=
  (hasDerivAt_logCutoffProfile hε hεδ hr).deriv

end LogVariable

variable (hε : 0 < ε) (hεδ : 4 * ε ≤ δ)
include hε hεδ

/-- The logarithmic cutoff profile vanishes on `(-∞, ε]`. -/
theorem logCutoffProfile_eq_zero_of_le (hr : r ≤ ε) : logCutoffProfile ε δ r = 0 :=
  logCutoffProfile_eq_zero_of_le_aux hε hεδ hr

/-- The logarithmic cutoff profile equals `1` on `[δ, ∞)`. -/
theorem logCutoffProfile_eq_one_of_le (hr : δ ≤ r) : logCutoffProfile ε δ r = 1 := by
  have hδ := pos_of_four_mul_le hε hεδ
  have hr0 := hδ.trans_le hr
  have h2 := Real.log_pos one_lt_two
  have hlog : log δ ≤ log r := Real.log_le_log hδ hr
  have ha : 1 ≤ (log r - log ε) / log 2 := by
    rw [le_div_iff₀ h2]
    have := two_mul_log_two_le hε hεδ
    rw [log_div_eq hε hεδ] at this
    linarith
  rw [logCutoffProfile_eq_logProfile hε hεδ hr0, logProfile_eq_of_one_le_left ha,
    smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le),
    mul_zero, sub_zero]

/-- On `[2ε, δ / 2]` the logarithmic cutoff profile is the logarithmic interpolation. -/
theorem logCutoffProfile_of_mem_Icc (hr : r ∈ Icc (2 * ε) (δ / 2)) :
    logCutoffProfile ε δ r = Real.log (r / ε) / Real.log (δ / ε) := by
  have hr0 : 0 < r := by linarith [hr.1]
  have h2 := Real.log_pos one_lt_two
  have hδ := pos_of_four_mul_le hε hεδ
  have ha : 1 ≤ (log r - log ε) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hr0.ne' hε.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hε).2 (by linarith [hr.1]))
  have hb : 1 ≤ (log δ - log r) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hδ.ne' hr0.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hr0).2 (by linarith [hr.2]))
  rw [logCutoffProfile_eq_logProfile hε hεδ hr0, logProfile_eq_of_one_le_right hb,
    smoothTransition.one_of_one_le ha, mul_one, Real.log_div hr0.ne' hε.ne']

/-- On `[ε, 2ε]` the logarithmic cutoff profile is `λ(r) τ(log₂ (r / ε))`. -/
theorem logCutoffProfile_of_mem_Icc_left (hr : r ∈ Icc ε (2 * ε)) :
    logCutoffProfile ε δ r =
      Real.log (r / ε) / Real.log (δ / ε) * smoothTransition (Real.logb 2 (r / ε)) := by
  have hr0 : 0 < r := hε.trans_le hr.1
  have h2 := Real.log_pos one_lt_two
  have hδ := pos_of_four_mul_le hε hεδ
  have hb : 1 ≤ (log δ - log r) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hδ.ne' hr0.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hr0).2 (by linarith [hr.2]))
  rw [logCutoffProfile_eq_logProfile hε hεδ hr0, logProfile_eq_of_one_le_right hb,
    Real.logb, Real.log_div hr0.ne' hε.ne']

/-- On `[δ / 2, δ]` the logarithmic cutoff profile is `1 - (1 - λ(r)) τ(log₂ (δ / r))`. -/
theorem logCutoffProfile_of_mem_Icc_right (hr : r ∈ Icc (δ / 2) δ) :
    logCutoffProfile ε δ r =
      1 - (1 - Real.log (r / ε) / Real.log (δ / ε)) * smoothTransition (Real.logb 2 (δ / r)) := by
  have hδ := pos_of_four_mul_le hε hεδ
  have hr0 : 0 < r := by linarith [hr.1]
  have h2 := Real.log_pos one_lt_two
  have ha : 1 ≤ (log r - log ε) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hr0.ne' hε.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hε).2 (by linarith [hr.1]))
  rw [logCutoffProfile_eq_logProfile hε hεδ hr0, logProfile_eq_of_one_le_left ha,
    Real.logb, Real.log_div hr0.ne' hε.ne', Real.log_div hδ.ne' hr0.ne']

/-- The logarithmic cutoff profile is smooth. -/
theorem contDiff_logCutoffProfile : ContDiff ℝ ∞ (logCutoffProfile ε δ) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  rcases lt_or_ge 0 r with hr | hr
  · have hlog : ContDiffAt ℝ ∞ log r := Real.contDiffAt_log.2 hr.ne'
    exact (contDiff_logProfile.contDiffAt.comp r hlog).congr_of_eventuallyEq
      (logCutoffProfile_eventuallyEq hε hεδ hr)
  · apply contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds (hr.trans_lt hε)] with s hs
    exact logCutoffProfile_eq_zero_of_le hε hεδ hs.le

/-- The derivative of the logarithmic cutoff profile vanishes on `(-∞, ε]`. -/
theorem deriv_logCutoffProfile_eq_zero_of_le (hr : r ≤ ε) :
    deriv (logCutoffProfile ε δ) r = 0 := by
  rcases hr.lt_or_eq with hr | rfl
  · rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
    filter_upwards [gt_mem_nhds hr] with s hs
    exact logCutoffProfile_eq_zero_of_le hε hεδ hs.le
  · apply IsLocalMin.deriv_eq_zero
    have hmono := monotone_of_deriv_nonneg
      ((contDiff_logCutoffProfile hε hεδ).differentiable (by simp)) fun s ↦ ?_
    · filter_upwards with s
      rw [logCutoffProfile_eq_zero_of_le hε hεδ le_rfl]
      rcases le_total s r with hs | hs
      · rw [logCutoffProfile_eq_zero_of_le hε hεδ hs]
      · exact (logCutoffProfile_eq_zero_of_le hε hεδ le_rfl).symm.trans_le (hmono hs)
    · rcases le_or_gt s 0 with hs | hs
      · rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
        filter_upwards [gt_mem_nhds (hs.trans_lt hε)] with t ht
        exact logCutoffProfile_eq_zero_of_le hε hεδ ht.le
      · rw [deriv_logCutoffProfile_eq hε hεδ hs]
        exact div_nonneg (logProfileDeriv_nonneg hε hεδ _) hs.le

/-- The derivative of the logarithmic cutoff profile is nonnegative. -/
theorem deriv_logCutoffProfile_nonneg (r : ℝ) : 0 ≤ deriv (logCutoffProfile ε δ) r := by
  rcases le_or_gt r ε with hr | hr
  · rw [deriv_logCutoffProfile_eq_zero_of_le hε hεδ hr]
  · rw [deriv_logCutoffProfile_eq hε hεδ (hε.trans hr)]
    exact div_nonneg (logProfileDeriv_nonneg hε hεδ _) (hε.trans hr).le

/-- The logarithmic cutoff profile is nondecreasing. -/
theorem monotone_logCutoffProfile : Monotone (logCutoffProfile ε δ) :=
  monotone_of_deriv_nonneg ((contDiff_logCutoffProfile hε hεδ).differentiable (by simp))
    (deriv_logCutoffProfile_nonneg hε hεδ)

/-- The logarithmic cutoff profile is nonnegative. -/
theorem logCutoffProfile_nonneg (r : ℝ) : 0 ≤ logCutoffProfile ε δ r := by
  rcases le_total r ε with hr | hr
  · rw [logCutoffProfile_eq_zero_of_le hε hεδ hr]
  · exact (logCutoffProfile_eq_zero_of_le hε hεδ le_rfl).symm.trans_le
      (monotone_logCutoffProfile hε hεδ hr)

/-- The logarithmic cutoff profile is at most `1`. -/
theorem logCutoffProfile_le_one (r : ℝ) : logCutoffProfile ε δ r ≤ 1 := by
  rcases le_total δ r with hr | hr
  · rw [logCutoffProfile_eq_one_of_le hε hεδ hr]
  · exact (monotone_logCutoffProfile hε hεδ hr).trans
      (logCutoffProfile_eq_one_of_le hε hεδ le_rfl).le

/-- The derivative of the logarithmic cutoff profile vanishes on `[δ, ∞)`. -/
theorem deriv_logCutoffProfile_eq_zero_of_ge (hr : δ ≤ r) :
    deriv (logCutoffProfile ε δ) r = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with s
  rw [logCutoffProfile_eq_one_of_le hε hεδ hr]
  exact logCutoffProfile_le_one hε hεδ s

/-- The derivative bound `0 ≤ ψ'(r) ≤ c₀ / (r log (δ / ε))` for `r > 0`. -/
theorem deriv_logCutoffProfile_le (hr : 0 < r) :
    deriv (logCutoffProfile ε δ) r ≤ logCutoffConst / (r * Real.log (δ / ε)) := by
  rw [deriv_logCutoffProfile_eq hε hεδ hr, mul_comm r, ← div_div]
  exact div_le_div_of_nonneg_right (logProfileDeriv_le hε hεδ _) hr.le

/-- On `[2ε, δ / 2]` the derivative of the logarithmic cutoff profile is `1 / (r log (δ / ε))`. -/
theorem deriv_logCutoffProfile_of_mem_Icc (hr : r ∈ Icc (2 * ε) (δ / 2)) :
    deriv (logCutoffProfile ε δ) r = 1 / (r * Real.log (δ / ε)) := by
  have hr0 : 0 < r := by linarith [hr.1]
  have h2 := Real.log_pos one_lt_two
  have hδ := pos_of_four_mul_le hε hεδ
  have ha : 1 ≤ (log r - log ε) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hr0.ne' hε.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hε).2 (by linarith [hr.1]))
  have hb : 1 ≤ (log δ - log r) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hδ.ne' hr0.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hr0).2 (by linarith [hr.2]))
  rw [deriv_logCutoffProfile_eq hε hεδ hr0]
  unfold logProfileDeriv
  rw [smoothTransition.one_of_one_le ha, smoothTransition.one_of_one_le hb,
    deriv_smoothTransition_eq_zero (Or.inr ha), deriv_smoothTransition_eq_zero (Or.inr hb)]
  field_simp
  ring

/-- On `[ε, 2ε]` the derivative of the logarithmic cutoff profile is
`(τ(a) + a τ'(a)) / (r log (δ / ε))` with `a = log₂ (r / ε)`. -/
theorem deriv_logCutoffProfile_of_mem_Icc_left (hr : r ∈ Icc ε (2 * ε)) :
    deriv (logCutoffProfile ε δ) r =
      (smoothTransition (Real.logb 2 (r / ε)) +
        Real.logb 2 (r / ε) * deriv smoothTransition (Real.logb 2 (r / ε))) /
        (r * Real.log (δ / ε)) := by
  have hr0 : 0 < r := hε.trans_le hr.1
  have h2 := Real.log_pos one_lt_two
  have hδ := pos_of_four_mul_le hε hεδ
  have hb : 1 ≤ (log δ - log r) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hδ.ne' hr0.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hr0).2 (by linarith [hr.2]))
  rw [deriv_logCutoffProfile_eq hε hεδ hr0]
  unfold logProfileDeriv
  rw [smoothTransition.one_of_one_le hb, deriv_smoothTransition_eq_zero (Or.inr hb), Real.logb,
    Real.log_div hr0.ne' hε.ne']
  field_simp
  ring

/-- On `[δ / 2, δ]` the derivative of the logarithmic cutoff profile is
`(τ(b) + b τ'(b)) / (r log (δ / ε))` with `b = log₂ (δ / r)`. -/
theorem deriv_logCutoffProfile_of_mem_Icc_right (hr : r ∈ Icc (δ / 2) δ) :
    deriv (logCutoffProfile ε δ) r =
      (smoothTransition (Real.logb 2 (δ / r)) +
        Real.logb 2 (δ / r) * deriv smoothTransition (Real.logb 2 (δ / r))) /
        (r * Real.log (δ / ε)) := by
  have hδ := pos_of_four_mul_le hε hεδ
  have hr0 : 0 < r := by linarith [hr.1]
  have h2 := Real.log_pos one_lt_two
  have ha : 1 ≤ (log r - log ε) / log 2 := by
    rw [le_div_iff₀ h2, ← Real.log_div hr0.ne' hε.ne']
    simpa only [one_mul] using Real.log_le_log two_pos ((le_div_iff₀ hε).2 (by linarith [hr.1]))
  rw [deriv_logCutoffProfile_eq hε hεδ hr0]
  unfold logProfileDeriv
  rw [smoothTransition.one_of_one_le ha, deriv_smoothTransition_eq_zero (Or.inr ha), Real.logb,
    Real.log_div hδ.ne' hr0.ne']
  field_simp
  ring

/-- Below `δ`, the defect `1 - ψ(r)` is at most `log (2δ / r) / log (δ / ε)`. -/
theorem one_sub_logCutoffProfile_le (hr : 0 < r) (hrδ : r ≤ δ) :
    1 - logCutoffProfile ε δ r ≤ Real.log (2 * δ / r) / Real.log (δ / ε) := by
  have hδ := pos_of_four_mul_le hε hεδ
  have hΛ := log_div_pos hε hεδ
  have h2 := Real.log_pos one_lt_two
  have hlog2 : Real.log (2 * δ / r) = log 2 + log δ - log r := by
    rw [Real.log_div (by positivity) hr.ne', Real.log_mul two_ne_zero hδ.ne']
  have hΛe := log_div_eq hε hεδ
  have hlr : log r ≤ log δ := Real.log_le_log hr hrδ
  rw [logCutoffProfile_eq_logProfile hε hεδ hr, hlog2, le_div_iff₀ hΛ]
  by_cases ha : 1 ≤ (log r - log ε) / log 2
  · rw [logProfile_eq_of_one_le_left ha]
    have hτ := smoothTransition.le_one ((log δ - log r) / log 2)
    have h1 : 0 ≤ 1 - (log r - log ε) / log (δ / ε) := by
      rw [sub_nonneg, div_le_one hΛ, hΛe]
      linarith
    have hkey : (1 - (log r - log ε) / log (δ / ε)) * log (δ / ε) = log δ - log r := by
      field_simp
      rw [hΛe]
      ring
    nlinarith [mul_le_mul_of_nonneg_left hτ h1]
  · replace ha := not_le.mp ha
    have hb := (one_le_or_one_le hε hεδ (log r)).resolve_left ha.not_ge
    rw [logProfile_eq_of_one_le_right hb]
    have hlt : log r < log ε + log 2 := by
      rw [div_lt_one h2] at ha
      linarith
    have hprod : 0 ≤ (log r - log ε) / log (δ / ε) *
        smoothTransition ((log r - log ε) / log 2) := by
      rcases le_or_gt (log r - log ε) 0 with hn | hn
      · rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hn h2.le),
          mul_zero]
      · exact mul_nonneg (div_nonneg hn.le hΛ.le) (smoothTransition.nonneg _)
    rw [hΛe] at hΛ hprod ⊢
    nlinarith [mul_nonneg hprod hΛ.le]

end TauCeti
