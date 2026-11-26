/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HigherPole.DelangeWeight
public import TauCeti.NumberTheory.LSeries.HigherPole.SquaredSinc

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Monotone unsmoothing for Delange's Tauberian theorem

This file proves the Tauberian unsmoothing step of Delange's theorem for higher-order poles
(Delange 1954, §3.4, pp. 227–228): if `α` is nondecreasing on `[0, ∞)` and, along arbitrarily
large bandwidths `λ`, the weighted integrands `t ↦ w_k(t) exp (-a t) α(t) K_λ(t - T)` are
eventually integrable on `[0, ∞)` as `T → ∞` and their integrals
`∫₀^∞ w_k(t) exp (-a t) α(t) K_λ(t - T) dt` tend to `C`, then `α(t) / (exp (a t) t ^ k) → C` as
`t → ∞`.

No sign assumption on `α` or `a` is required: both nonnegative monotone and nonnegative antitone
profiles satisfy two-sided local slow-oscillation bounds on `[0, ∞)`, and an arbitrary
nondecreasing `α` either stays negative (making `-α` nonnegative and antitone) or eventually
becomes nonnegative (agreeing with `max α 0` up to a compactly supported perturbation whose
`K_λ`-convolution vanishes at infinity).

The file also proves that a single bandwidth `λ > 0` does not suffice: for every `a > 0`, `C > 0`,
`λ > 0`, and `k : ℕ`, there exists a nonnegative nondecreasing `α` on `[0, ∞)` for which the
weighted integrand `t ↦ w_k(t) exp (-a t) α(t) K_λ(t - T)` is integrable on `[0, ∞)` at every `T`
and its integral tends to `C` as `T → ∞`, while `α(t) / (exp (a t) t ^ k)` fails to converge to `C`.

## Main results

* `TauCeti.HigherPoleTauberian.monotoneUnsmoothing`: monotone removal of `squaredSinc` smoothing.
* `TauCeti.HigherPoleTauberian.exists_not_tendsto_of_single_bandwidth`: counterexample showing that
  a single bandwidth `λ > 0` does not suffice.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242, especially §3.4.
-/

public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-! ### Abstract nonnegative unsmoothing -/

/-- Eventually `J T < C + ε` under a lower window comparison and frequent eventually integrable
`squaredSinc` convolutions converging to `C`. -/
private theorem eventually_lt_add_of_squaredSinc_convolution {J : ℝ → ℝ} {C ε : ℝ} (hε : 0 < ε)
    (hJ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ J t)
    (hlow : ∀ c ∈ Ioo (0 : ℝ) 1, ∃ h > 0, ∃ s : ℝ, ∀ᶠ T in atTop,
      ∀ t ∈ Icc (T + s - h) (T + s + h), c * J T ≤ J t)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦ J t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ), J t * squaredSinc ell (t - T)) atTop (𝓝 C)) :
    ∀ᶠ T in atTop, J T < C + ε := by
  have hC0 : 0 ≤ C := by
    obtain ⟨ell, ⟨_, hlim⟩, hell⟩ := (hsmooth.and_eventually (eventually_gt_atTop (0 : ℝ))).exists
    exact ge_of_tendsto' hlim fun T ↦ setIntegral_nonneg measurableSet_Ici fun t ht ↦
      mul_nonneg (hJ0 t ht) (squaredSinc_nonneg hell.le _)
  let c : ℝ := (C + ε / 3) / (C + 2 * ε / 3)
  let m : ℝ := (C + 2 * ε / 3) / (C + ε)
  have hc_pos : 0 < c := by positivity
  have hc_lt : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hm_pos : 0 < m := by positivity
  have hm_lt : m < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hcm : c * m * (C + ε) = C + ε / 3 := by
    simp only [c, m]
    field_simp [(by linarith : C + 2 * ε / 3 ≠ 0), (by linarith : C + ε ≠ 0)]
  obtain ⟨h, hh, s, hwin⟩ := hlow c ⟨hc_pos, hc_lt⟩
  have hm_ev : ∀ᶠ ell in atTop, 0 < ell ∧ m ≤ ∫ v in (-h)..h, squaredSinc ell v :=
    (eventually_gt_atTop (0 : ℝ)).and
      ((tendsto_intervalIntegral_squaredSinc hh).eventually (Ici_mem_nhds hm_lt))
  obtain ⟨ell, ⟨hint_ev, hlim⟩, hell, hm_le⟩ := (hsmooth.and_eventually hm_ev).exists
  have hshift : Tendsto (fun T : ℝ ↦ T + s) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  filter_upwards [hwin, hshift.eventually hint_ev,
    (hlim.comp hshift).eventually (Iio_mem_nhds (by linarith : C < C + ε / 3)),
    eventually_ge_atTop (max 0 (h - s))] with T hT hint hconv hT0
  have hJT : 0 ≤ J T := hJ0 T (le_trans (le_max_left _ _) hT0)
  have hTs : 0 ≤ T + s - h := by linarith [le_trans (le_max_right 0 (h - s)) hT0]
  have hle := mul_intervalIntegral_squaredSinc_le_setIntegral_Ici hell.le hh.le hTs hJ0 hint hT
  have h1 : (c * J T) * m ≤ (c * J T) * ∫ v in (-h)..h, squaredSinc ell v :=
    mul_le_mul_of_nonneg_left hm_le (mul_nonneg hc_pos.le hJT)
  have h2 : c * m * J T < c * m * (C + ε) := by
    have hlin : c * J T * m < C + ε / 3 := lt_of_le_of_lt (h1.trans hle) hconv
    linarith [hcm]
  exact lt_of_mul_lt_mul_left h2 (mul_nonneg hc_pos.le hm_pos.le)

/-- Under a lower window comparison and local boundedness, a nonnegative function with frequent
eventually integrable `squaredSinc` convolutions converging to `C` along arbitrarily large
bandwidths is globally bounded on `[0, ∞)`. -/
private theorem exists_bddAbove_of_squaredSinc_convolution {J : ℝ → ℝ} {C : ℝ}
    (hJ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ J t)
    (hJloc : ∀ T₀ : ℝ, ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T₀, J t ≤ B)
    (hlow : ∀ c ∈ Ioo (0 : ℝ) 1, ∃ h > 0, ∃ s : ℝ, ∀ᶠ T in atTop,
      ∀ t ∈ Icc (T + s - h) (T + s + h), c * J T ≤ J t)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦ J t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ), J t * squaredSinc ell (t - T)) atTop (𝓝 C)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Ici (0 : ℝ), J t ≤ M := by
  have hev := eventually_lt_add_of_squaredSinc_convolution zero_lt_one hJ0 hlow hsmooth
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  obtain ⟨B, hB⟩ := hJloc T₀
  refine ⟨max 0 (max B (C + 1)), le_max_left _ _, fun t ht ↦ ?_⟩
  rcases le_or_gt t T₀ with hle | hgt
  · exact le_trans (hB t ⟨ht, hle⟩) (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact le_trans (hT₀ t hgt.le).le (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Eventually `C - ε < J T` under an upper window comparison, a global upper bound, and frequent
eventually integrable `squaredSinc` convolutions converging to `C`. -/
private theorem eventually_sub_lt_of_squaredSinc_convolution {J : ℝ → ℝ} {C M ε : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M)
    (hJ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ J t) (hJM : ∀ t ∈ Ici (0 : ℝ), J t ≤ M)
    (hhigh : ∀ c > (1 : ℝ), ∃ h > 0, ∃ s : ℝ, ∀ᶠ T in atTop,
      ∀ t ∈ Icc (T + s - h) (T + s + h), J t ≤ c * J T)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦ J t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ), J t * squaredSinc ell (t - T)) atTop (𝓝 C)) :
    ∀ᶠ T in atTop, C - ε < J T := by
  by_cases hC : C < ε
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    linarith [hJ0 T hT]
  push Not at hC
  let c : ℝ := (C - ε / 2) / (C - 3 * ε / 4)
  have hden : 0 < C - 3 * ε / 4 := by linarith
  have hc_gt : 1 < c := (one_lt_div hden).mpr (by linarith)
  have hc_mul : c * (C - ε) < C - ε / 2 := by
    calc c * (C - ε) < c * (C - 3 * ε / 4) := by gcongr; linarith
      _ = C - ε / 2 := div_mul_cancel₀ _ hden.ne'
  obtain ⟨h, hh, s, hwin⟩ := hhigh c hc_gt
  have htail_lim :
      Tendsto (fun ell : ℝ ↦ M * ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_integral_squaredSinc_tail hh).const_mul M
  have htail_ev : ∀ᶠ ell in atTop,
      0 < ell ∧ M * ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v < ε / 4 :=
    (eventually_gt_atTop (0 : ℝ)).and
      (htail_lim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4)))
  obtain ⟨ell, ⟨hint_ev, hlim⟩, hell, htail⟩ := (hsmooth.and_eventually htail_ev).exists
  have hshift : Tendsto (fun T : ℝ ↦ T + s) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  filter_upwards [hwin, hshift.eventually hint_ev,
    (hlim.comp hshift).eventually (Ioi_mem_nhds (by linarith : C - ε / 4 < C)),
    eventually_ge_atTop (0 : ℝ)] with T hT hint hconv hT0
  dsimp only [Function.comp_apply] at hconv
  have hJT : 0 ≤ J T := hJ0 T hT0
  have hle := setIntegral_Ici_mul_squaredSinc_le hell.le (mul_nonneg (by linarith) hJT) hM
    hJM hint hT
  have hcJT : c * (C - ε) < c * J T := by linarith
  exact lt_of_mul_lt_mul_left hcJT (by linarith)

/-- Abstract unsmoothing for a nonnegative locally bounded function `J` satisfying two-sided local
window bounds against shifted intervals. -/
private theorem tendsto_of_squaredSinc_convolution {J : ℝ → ℝ} {C : ℝ}
    (hJ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ J t)
    (hJloc : ∀ T₀ : ℝ, ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T₀, J t ≤ B)
    (hlow : ∀ c ∈ Ioo (0 : ℝ) 1, ∃ h > 0, ∃ s : ℝ, ∀ᶠ T in atTop,
      ∀ t ∈ Icc (T + s - h) (T + s + h), c * J T ≤ J t)
    (hhigh : ∀ c > (1 : ℝ), ∃ h > 0, ∃ s : ℝ, ∀ᶠ T in atTop,
      ∀ t ∈ Icc (T + s - h) (T + s + h), J t ≤ c * J T)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦ J t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ), J t * squaredSinc ell (t - T)) atTop (𝓝 C)) :
    Tendsto J atTop (𝓝 C) := by
  obtain ⟨M, hM, hJM⟩ := exists_bddAbove_of_squaredSinc_convolution hJ0 hJloc hlow hsmooth
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev := (eventually_lt_add_of_squaredSinc_convolution hε hJ0 hlow hsmooth).and
    (eventually_sub_lt_of_squaredSinc_convolution hε hM hJ0 hJM hhigh hsmooth)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  exact ⟨T₀, fun T hT ↦ by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [(hT₀ T hT).1, (hT₀ T hT).2]⟩

/-! ### Local slow oscillation of `delangeWeight k t * exp (-a * t)` -/

/-- On any compact interval `[0, T₀]`, `delangeWeight k t * exp (-a * t)` has a nonnegative uniform
bound in absolute value. -/
private theorem exists_bound_delangeWeight_mul_exp (a : ℝ) (k : ℕ) (T₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T₀, |delangeWeight k t * exp (-a * t)| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_delangeWeight k).mul
      (by fun_prop : Continuous fun t ↦ exp (-a * t))).continuousOn
    (s := Icc (0 : ℝ) (max T₀ 0))
  refine ⟨max B 0, le_max_right _ _, fun t ht ↦ ?_⟩
  have ht' : t ∈ Icc (0 : ℝ) (max T₀ 0) := ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
  exact (hB t ht').trans (le_max_left _ _)

/-- For every `c ∈ (0, 1)`, there is `h > 0` such that eventually for large `T`,
`c * (w_k(T) exp (-a T)) ≤ w_k(t) exp (-a t)` holds for all `|t - T| ≤ 2 h`. -/
private theorem exists_window_weight_exp_lower (a : ℝ) (k : ℕ) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ h > 0, ∀ᶠ T in atTop, ∀ t : ℝ, |t - T| ≤ 2 * h →
      c * (delangeWeight k T * exp (-a * T)) ≤ delangeWeight k t * exp (-a * t) := by
  have hcont : Tendsto (fun h : ℝ ↦ exp (-|a| * (2 * h))) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((by fun_prop : Continuous fun h : ℝ ↦ exp (-|a| * (2 * h))).tendsto 0).mono_left
      nhdsWithin_le_nhds
  obtain ⟨h, hhexp, hh⟩ :=
    ((hcont.eventually (Ioi_mem_nhds (by linarith [hc.2] : (1 + c) / 2 < 1))).and
      self_mem_nhdsWithin).exists
  let η : ℝ := 1 - c / ((1 + c) / 2)
  have hη : 0 < η := sub_pos.mpr ((div_lt_one (by linarith [hc.1])).mpr (by linarith [hc.2]))
  refine ⟨h, hh, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_delangeWeight_add_div k (2 * h)) η hη]
    with T hT hw t ht
  have hwT : 0 < delangeWeight k T := delangeWeight_pos hT
  have hd := hw (t - T) (abs_le.mp ht)
  rw [add_sub_cancel, Real.dist_eq, abs_sub_lt_iff] at hd
  have hwr : 1 - η < delangeWeight k t / delangeWeight k T := by linarith [hd.1, hd.2]
  have hwle : (1 - η) * delangeWeight k T ≤ delangeWeight k t := (le_div_iff₀ hwT).mp hwr.le
  have hexple : exp (-|a| * (2 * h)) * exp (-a * T) ≤ exp (-a * t) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    have habs : a * (t - T) ≤ |a| * (2 * h) :=
      (le_abs_self _).trans
        ((abs_mul a (t - T)).le.trans (mul_le_mul_of_nonneg_left ht (abs_nonneg a)))
    linarith
  have h1η : 1 - η = c / ((1 + c) / 2) := by simp [η]
  have h1η_nonneg : 0 ≤ 1 - η := by rw [h1η]; exact div_nonneg hc.1.le (by linarith [hc.1])
  have hc_le : c ≤ (1 - η) * exp (-|a| * (2 * h)) := by
    rw [h1η]
    calc c = c / ((1 + c) / 2) * ((1 + c) / 2) := (div_mul_cancel₀ c (by linarith [hc.1])).symm
      _ ≤ c / ((1 + c) / 2) * exp (-|a| * (2 * h)) :=
          mul_le_mul_of_nonneg_left hhexp.le (div_nonneg hc.1.le (by linarith [hc.1]))
  calc c * (delangeWeight k T * exp (-a * T))
      ≤ ((1 - η) * exp (-|a| * (2 * h))) * (delangeWeight k T * exp (-a * T)) :=
          mul_le_mul_of_nonneg_right hc_le (mul_nonneg hwT.le (exp_pos _).le)
    _ = ((1 - η) * delangeWeight k T) * (exp (-|a| * (2 * h)) * exp (-a * T)) := by ring
    _ ≤ delangeWeight k t * exp (-a * t) :=
          mul_le_mul hwle hexple (by positivity) (le_trans (mul_nonneg h1η_nonneg hwT.le) hwle)

/-- For every `c > 1`, there is `h > 0` such that eventually for large `T`,
`w_k(t) exp (-a t) ≤ c * (w_k(T) exp (-a T))` holds for all `|t - T| ≤ 2 h`. -/
private theorem exists_window_weight_exp_upper (a : ℝ) (k : ℕ) {c : ℝ} (hc : 1 < c) :
    ∃ h > 0, ∀ᶠ T in atTop, ∀ t : ℝ, |t - T| ≤ 2 * h →
      delangeWeight k t * exp (-a * t) ≤ c * (delangeWeight k T * exp (-a * T)) := by
  have hcont : Tendsto (fun h : ℝ ↦ exp (|a| * (2 * h))) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((by fun_prop : Continuous fun h : ℝ ↦ exp (|a| * (2 * h))).tendsto 0).mono_left
      nhdsWithin_le_nhds
  obtain ⟨h, hhexp, hh⟩ :=
    ((hcont.eventually (Iio_mem_nhds (by linarith : (1 : ℝ) < (1 + c) / 2))).and
      self_mem_nhdsWithin).exists
  let η : ℝ := c / ((1 + c) / 2) - 1
  have hη : 0 < η := sub_pos.mpr ((one_lt_div (by linarith)).mpr (by linarith))
  refine ⟨h, hh, ?_⟩
  filter_upwards [eventually_gt_atTop (2 * h),
    Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_delangeWeight_add_div k (2 * h)) η hη]
    with T hT hw t ht
  have hwT : 0 < delangeWeight k T := delangeWeight_pos (lt_trans (by positivity) hT)
  have hd := hw (t - T) (abs_le.mp ht)
  rw [add_sub_cancel, Real.dist_eq, abs_sub_lt_iff] at hd
  have hwr : delangeWeight k t / delangeWeight k T < 1 + η := by linarith [hd.1, hd.2]
  have hwle : delangeWeight k t ≤ (1 + η) * delangeWeight k T := (div_le_iff₀ hwT).mp hwr.le
  have hexple : exp (-a * t) ≤ exp (|a| * (2 * h)) * exp (-a * T) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    have habs : -(a * (t - T)) ≤ |a| * (2 * h) :=
      (neg_le_abs _).trans
        ((abs_mul a (t - T)).le.trans (mul_le_mul_of_nonneg_left ht (abs_nonneg a)))
    linarith
  have h1η : 1 + η = c / ((1 + c) / 2) := by simp [η]
  have hle_c : (1 + η) * exp (|a| * (2 * h)) ≤ c := by
    rw [h1η]
    calc c / ((1 + c) / 2) * exp (|a| * (2 * h))
        ≤ c / ((1 + c) / 2) * ((1 + c) / 2) := by gcongr
      _ = c := div_mul_cancel₀ _ (by linarith)
  calc delangeWeight k t * exp (-a * t)
      ≤ ((1 + η) * delangeWeight k T) * (exp (|a| * (2 * h)) * exp (-a * T)) :=
          mul_le_mul hwle hexple (exp_pos _).le (mul_nonneg (by linarith) hwT.le)
    _ = ((1 + η) * exp (|a| * (2 * h))) * (delangeWeight k T * exp (-a * T)) := by ring
    _ ≤ c * (delangeWeight k T * exp (-a * T)) :=
          mul_le_mul_of_nonneg_right hle_c (mul_nonneg hwT.le (exp_pos _).le)

/-! ### Nonnegative monotone and antitone unsmoothing -/

/-- Unsmoothing for `t ↦ delangeWeight k t * exp (-a * t) * f t` from nonnegativity, local upper
bounds, and one-sided shifted-window comparisons on `f`. -/
private theorem tendsto_weighted_of_window_bounds {f : ℝ → ℝ} {a C : ℝ} {k : ℕ}
    (hf0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t)
    (hfloc : ∀ T₀ : ℝ, ∃ A : ℝ, ∀ t ∈ Icc (0 : ℝ) T₀, f t ≤ A)
    (hflow : ∀ h > (0 : ℝ), ∃ s : ℝ, |s| ≤ h ∧ ∀ᶠ T in atTop,
      ∀ t ∈ Icc (T + s - h) (T + s + h), 0 ≤ t ∧ f T ≤ f t)
    (hfhigh : ∀ h > (0 : ℝ), ∃ s : ℝ, |s| ≤ h ∧ ∀ᶠ T in atTop,
      ∀ t ∈ Icc (T + s - h) (T + s + h), 0 ≤ t ∧ f t ≤ f T)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦
        delangeWeight k t * exp (-a * t) * f t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
        delangeWeight k t * exp (-a * t) * f t * squaredSinc ell (t - T))
        atTop (𝓝 C)) :
    Tendsto (fun t : ℝ ↦ delangeWeight k t * exp (-a * t) * f t) atTop (𝓝 C) := by
  refine tendsto_of_squaredSinc_convolution
    (fun t ht ↦ mul_nonneg (mul_nonneg (delangeWeight_nonneg ht) (exp_pos _).le) (hf0 t ht))
    (fun T₀ ↦ ?_) (fun c hc ↦ ?_) (fun c hc ↦ ?_) hsmooth
  · obtain ⟨B, hB0, hB⟩ := exists_bound_delangeWeight_mul_exp a k T₀
    obtain ⟨A, hA⟩ := hfloc T₀
    exact ⟨B * max A 0, fun t ht ↦ mul_le_mul ((le_abs_self _).trans (hB t ht))
      ((hA t ht).trans (le_max_left _ _)) (hf0 t ht.1) hB0⟩
  · obtain ⟨h, hh, hev⟩ := exists_window_weight_exp_lower a k hc
    obtain ⟨s, hs, hfwin⟩ := hflow h hh
    refine ⟨h, hh, s, ?_⟩
    filter_upwards [hev, hfwin, eventually_ge_atTop (0 : ℝ)] with T hT hfT hT0 t ht
    obtain ⟨ht0, hft⟩ := hfT t ht
    have habs : |t - T| ≤ 2 * h := abs_le.mpr
      ⟨by linarith [ht.1, (abs_le.mp hs).1], by linarith [ht.2, (abs_le.mp hs).2]⟩
    calc c * (delangeWeight k T * exp (-a * T) * f T)
        = (c * (delangeWeight k T * exp (-a * T))) * f T := by ring
      _ ≤ (delangeWeight k t * exp (-a * t)) * f t :=
          mul_le_mul (hT t habs) hft (hf0 T hT0)
            (mul_nonneg (delangeWeight_nonneg ht0) (exp_pos _).le)
  · obtain ⟨h, hh, hev⟩ := exists_window_weight_exp_upper a k hc
    obtain ⟨s, hs, hfwin⟩ := hfhigh h hh
    refine ⟨h, hh, s, ?_⟩
    filter_upwards [hev, hfwin, eventually_ge_atTop (0 : ℝ)] with T hT hfT hT0 t ht
    obtain ⟨ht0, hft⟩ := hfT t ht
    have habs : |t - T| ≤ 2 * h := abs_le.mpr
      ⟨by linarith [ht.1, (abs_le.mp hs).1], by linarith [ht.2, (abs_le.mp hs).2]⟩
    calc delangeWeight k t * exp (-a * t) * f t
        ≤ (c * (delangeWeight k T * exp (-a * T))) * f T :=
          mul_le_mul (hT t habs) hft (hf0 t ht0)
            (mul_nonneg (by linarith) (mul_nonneg (delangeWeight_nonneg hT0) (exp_pos _).le))
      _ = c * (delangeWeight k T * exp (-a * T) * f T) := by ring

/-- Unsmoothing for a nonnegative nondecreasing function `α` on `[0, ∞)` (arbitrary `a : ℝ`). -/
private theorem tendsto_weighted_of_monotoneOn_nonneg {α : ℝ → ℝ} {a C : ℝ} {k : ℕ}
    (hα : MonotoneOn α (Ici 0)) (hα0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ α t)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T))
        atTop (𝓝 C)) :
    Tendsto (fun t : ℝ ↦ delangeWeight k t * exp (-a * t) * α t) atTop (𝓝 C) := by
  refine tendsto_weighted_of_window_bounds hα0
    (fun T₀ ↦ ⟨α (max T₀ 0), fun t ht ↦
      hα ht.1 (le_max_right _ _) (ht.2.trans (le_max_left _ _))⟩)
    (fun h hh ↦ ⟨h, (abs_of_pos hh).le, ?_⟩)
    (fun h hh ↦ ⟨-h, by rw [abs_neg, abs_of_pos hh], ?_⟩) hsmooth
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT t ht
    have hTt : T ≤ t := by linarith [ht.1]
    exact ⟨hT.trans hTt, hα hT (hT.trans hTt) hTt⟩
  · filter_upwards [eventually_ge_atTop (2 * h)] with T _ t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have htT : t ≤ T := by linarith [ht.2]
    exact ⟨ht0, hα ht0 (ht0.trans htT) htT⟩

/-- Unsmoothing for a nonnegative nonincreasing function `g` on `[0, ∞)` (arbitrary `a : ℝ`). -/
private theorem tendsto_weighted_of_antitoneOn_nonneg {g : ℝ → ℝ} {a C : ℝ} {k : ℕ}
    (hg : AntitoneOn g (Ici 0)) (hg0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ g t)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦
        delangeWeight k t * exp (-a * t) * g t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
        delangeWeight k t * exp (-a * t) * g t * squaredSinc ell (t - T))
        atTop (𝓝 C)) :
    Tendsto (fun t : ℝ ↦ delangeWeight k t * exp (-a * t) * g t) atTop (𝓝 C) := by
  refine tendsto_weighted_of_window_bounds hg0
    (fun _ ↦ ⟨g 0, fun t ht ↦ hg le_rfl ht.1 ht.1⟩)
    (fun h hh ↦ ⟨-h, by rw [abs_neg, abs_of_pos hh], ?_⟩)
    (fun h hh ↦ ⟨h, (abs_of_pos hh).le, ?_⟩) hsmooth
  · filter_upwards [eventually_ge_atTop (2 * h)] with T _ t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have htT : t ≤ T := by linarith [ht.2]
    exact ⟨ht0, hg ht0 (ht0.trans htT) htT⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT t ht
    have hTt : T ≤ t := by linarith [ht.1]
    exact ⟨hT.trans hTt, hg hT (hT.trans hTt) hTt⟩

/-! ### Compactly supported perturbations and main unsmoothing theorem -/

/-- A bounded measurable function on `[0, ∞)` vanishing beyond `t₀` is integrable against every
shifted `squaredSinc` kernel. -/
private theorem integrableOn_of_compact_support {D : ℝ → ℝ} {t₀ B ell : ℝ} (hB : 0 ≤ B)
    (hDmeas : AEStronglyMeasurable D (volume.restrict (Ici 0)))
    (hDsupp : ∀ t : ℝ, t₀ < t → D t = 0)
    (hDbd : ∀ t ∈ Icc (0 : ℝ) t₀, |D t| ≤ B) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ D t * squaredSinc ell (t - T)) (Ici 0) :=
  ((integrable_squaredSinc ell).comp_sub_right T).integrableOn.bdd_mul hDmeas
    (ae_restrict_of_forall_mem measurableSet_Ici fun t ht ↦ by
      rw [Real.norm_eq_abs]
      rcases le_or_gt t t₀ with hle | hgt
      · exact hDbd t ⟨ht, hle⟩
      · simpa [hDsupp t hgt] using hB)

/-- A bounded measurable function on `[0, ∞)` vanishing beyond `t₀` has `squaredSinc` convolution
tending to `0` as `T → ∞`. -/
private theorem tendsto_zero_of_compact_support {D : ℝ → ℝ} {t₀ B ell : ℝ}
    (ht₀ : 0 ≤ t₀) (hB : 0 ≤ B) (hell : 0 < ell)
    (hDmeas : AEStronglyMeasurable D (volume.restrict (Ici 0)))
    (hDsupp : ∀ t : ℝ, t₀ < t → D t = 0)
    (hDbd : ∀ t ∈ Icc (0 : ℝ) t₀, |D t| ≤ B) :
    Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ), D t * squaredSinc ell (t - T)) atTop (𝓝 0) := by
  have hint := integrableOn_of_compact_support (ell := ell) hB hDmeas hDsupp hDbd
  have hupper : Tendsto (fun T : ℝ ↦ B * t₀ * (π * ell * (T - t₀) ^ 2)⁻¹) atTop (𝓝 0) := by
    have hsub : Tendsto (fun T : ℝ ↦ T - t₀) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_id.atTop_add (tendsto_const_nhds (x := -t₀))
    have hsq : Tendsto (fun T : ℝ ↦ π * ell * (T - t₀) ^ 2) atTop atTop :=
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hsub).const_mul_atTop (mul_pos pi_pos hell)
    simpa only [Function.comp_apply, mul_zero] using
      (tendsto_inv_atTop_zero.comp hsq).const_mul (B * t₀)
  refine squeeze_zero_norm' ?_ hupper
  filter_upwards [eventually_gt_atTop t₀] with T hT
  have heq : ∫ t in Ici (0 : ℝ), D t * squaredSinc ell (t - T) =
      ∫ t in Icc (0 : ℝ) t₀, D t * squaredSinc ell (t - T) := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ici.nullMeasurableSet
      (fun t ht ↦ ht.1) (ae_of_all _ fun t ht ↦ ?_)
    have hnot : t₀ < t := lt_of_not_ge fun hle ↦ ht.2 ⟨ht.1, hle⟩
    rw [hDsupp t hnot, zero_mul]
  rw [heq]
  have hbd : ∀ t ∈ Icc (0 : ℝ) t₀,
      ‖D t * squaredSinc ell (t - T)‖ ≤ B * (π * ell * (T - t₀) ^ 2)⁻¹ := fun t ht ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (squaredSinc_nonneg hell.le _)]
    have hK : squaredSinc ell (t - T) ≤ (π * ell * (T - t₀) ^ 2)⁻¹ := calc
      squaredSinc ell (t - T) = squaredSinc ell (-(T - t)) := by ring_nf
      _ = squaredSinc ell (T - t) := squaredSinc_neg_right ell _
      _ ≤ (π * ell * (T - t) ^ 2)⁻¹ := squaredSinc_le_inv_mul_sq hell.le (by linarith [ht.2])
      _ ≤ (π * ell * (T - t₀) ^ 2)⁻¹ := by gcongr; linarith [ht.2]
    exact mul_le_mul (hDbd t ht) hK (squaredSinc_nonneg hell.le _) hB
  calc ‖∫ t in Icc (0 : ℝ) t₀, D t * squaredSinc ell (t - T)‖
      ≤ ∫ t in Icc (0 : ℝ) t₀, ‖D t * squaredSinc ell (t - T)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ in Icc (0 : ℝ) t₀, B * (π * ell * (T - t₀) ^ 2)⁻¹ :=
        setIntegral_mono_on ((hint T).mono_set (Icc_subset_Ici_self : Icc (0 : ℝ) t₀ ⊆ Ici 0)).norm
          (integrableOn_const (by simp)) measurableSet_Icc hbd
    _ = B * t₀ * (π * ell * (T - t₀) ^ 2)⁻¹ := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le ht₀, sub_zero]
        ring

/-- For a nondecreasing `α` on `[0, ∞)` with `0 ≤ α t₀`, the compactly supported perturbation
`D(t) = w_k(t) exp (-a t) (max (α t) 0 - α t)` is integrable against every shifted `squaredSinc`
kernel and its half-line convolution tends to `0`. -/
private theorem integrableOn_and_tendsto_zero_max_sub {α : ℝ → ℝ} {a t₀ ell : ℝ} {k : ℕ}
    (hα : MonotoneOn α (Ici 0)) (ht₀ : t₀ ∈ Ici (0 : ℝ)) (hαt₀ : 0 ≤ α t₀) (hell : 0 < ell) :
    let D : ℝ → ℝ := fun t ↦ delangeWeight k t * exp (-a * t) * (max (α t) 0 - α t)
    (∀ T : ℝ, IntegrableOn (fun t : ℝ ↦ D t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ), D t * squaredSinc ell (t - T)) atTop (𝓝 0) := by
  intro D
  have hαmeas : AEStronglyMeasurable α (volume.restrict (Ici 0)) :=
    (aemeasurable_restrict_of_monotoneOn measurableSet_Ici hα).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable D (volume.restrict (Ici 0)) :=
    ((continuous_delangeWeight k).mul (by fun_prop : Continuous fun t ↦ exp (-a * t)))
      |>.aestronglyMeasurable.mul ((hαmeas.sup aestronglyMeasurable_const).sub hαmeas)
  have hDsupp : ∀ t : ℝ, t₀ < t → D t = 0 := fun t ht ↦ by
    simp [D, max_eq_left (le_trans hαt₀ (hα ht₀ (le_trans ht₀ ht.le) ht.le))]
  obtain ⟨Mwe, hMwe0, hMwe⟩ := exists_bound_delangeWeight_mul_exp a k t₀
  have hB : 0 ≤ Mwe * max (-α 0) 0 := mul_nonneg hMwe0 (le_max_right _ _)
  have hDbd : ∀ t ∈ Icc (0 : ℝ) t₀, |D t| ≤ Mwe * max (-α 0) 0 := fun t ht ↦ by
    have hba : |max (α t) 0 - α t| ≤ max (-α 0) 0 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
      rcases le_total 0 (α t) with h | h
      · simp [max_eq_left h]
      · rw [max_eq_right h, zero_sub]
        exact le_trans (neg_le_neg (hα le_rfl ht.1 ht.1)) (le_max_left _ _)
    rw [abs_mul]
    exact mul_le_mul (hMwe t ht) hba (abs_nonneg _) hMwe0
  exact ⟨integrableOn_of_compact_support hB hDmeas hDsupp hDbd,
    tendsto_zero_of_compact_support ht₀ hB hell hDmeas hDsupp hDbd⟩

/-- If `α` is nondecreasing on `[0, ∞)`, satisfies `0 ≤ α t₀` at some `t₀ ≥ 0`, and has frequent
eventually integrable `squaredSinc` convolutions converging to `C`, then
`delangeWeight k t * exp (-a * t) * α t → C` as `t → ∞`. -/
private theorem tendsto_weighted_of_monotoneOn_eventually_nonneg {α : ℝ → ℝ} {a C t₀ : ℝ} {k : ℕ}
    (hα : MonotoneOn α (Ici 0)) (ht₀ : t₀ ∈ Ici (0 : ℝ)) (hαt₀ : 0 ≤ α t₀)
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T))
        atTop (𝓝 C)) :
    Tendsto (fun t : ℝ ↦ delangeWeight k t * exp (-a * t) * α t) atTop (𝓝 C) := by
  let β : ℝ → ℝ := fun t ↦ max (α t) 0
  let D : ℝ → ℝ := fun t ↦ delangeWeight k t * exp (-a * t) * (β t - α t)
  have hβsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦
        delangeWeight k t * exp (-a * t) * β t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
        delangeWeight k t * exp (-a * t) * β t * squaredSinc ell (t - T)) atTop (𝓝 C) := by
    refine (hsmooth.and_eventually (eventually_gt_atTop (0 : ℝ))).mono
      fun ell ⟨⟨hint, hlim⟩, hell⟩ ↦ ?_
    obtain ⟨hDint, hDlim⟩ :=
      integrableOn_and_tendsto_zero_max_sub (a := a) (k := k) hα ht₀ hαt₀ hell
    have hdec : ∀ T t, delangeWeight k t * exp (-a * t) * β t * squaredSinc ell (t - T) =
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T) +
          D t * squaredSinc ell (t - T) := fun T t ↦ by simp only [D]; ring
    refine ⟨hint.mono fun T hT ↦ (hT.add (hDint T)).congr (ae_of_all _ fun t ↦ (hdec T t).symm), ?_⟩
    have hsum : Tendsto (fun T : ℝ ↦
        (∫ t in Ici (0 : ℝ), delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T)) +
          ∫ t in Ici (0 : ℝ), D t * squaredSinc ell (t - T)) atTop (𝓝 C) := by
      simpa only [add_zero] using hlim.add hDlim
    refine hsum.congr' (hint.mono fun T hT ↦ ?_)
    rw [← integral_add hT (hDint T)]
    congr 1 with t
    exact (hdec T t).symm
  have hβlim := tendsto_weighted_of_monotoneOn_nonneg
    (fun x hx y hy hxy ↦ max_le_max_right 0 (hα hx hy hxy)) (fun _ _ ↦ le_max_right _ _) hβsmooth
  refine hβlim.congr' ?_
  filter_upwards [eventually_ge_atTop t₀] with t ht
  simp [max_eq_left (le_trans hαt₀ (hα ht₀ (le_trans ht₀ ht) ht))]

/-- Because `delangeWeight k t * t ^ k → 1` as `t → ∞`, convergence of `α t / (exp (a * t) * t ^ k)`
to `C` is equivalent to convergence of `delangeWeight k t * exp (-a * t) * α t` to `C`. -/
private theorem tendsto_div_exp_mul_pow_iff {α : ℝ → ℝ} {a C : ℝ} {k : ℕ} :
    Tendsto (fun t : ℝ ↦ α t / (exp (a * t) * t ^ k)) atTop (𝓝 C) ↔
      Tendsto (fun t : ℝ ↦ delangeWeight k t * exp (-a * t) * α t) atTop (𝓝 C) := by
  have heq : ∀ t > (0 : ℝ),
      α t / (exp (a * t) * t ^ k) * (delangeWeight k t * t ^ k) =
        delangeWeight k t * exp (-a * t) * α t := fun t ht ↦ by
    rw [neg_mul, exp_neg]
    field_simp [(exp_pos (a * t)).ne', (pow_pos ht k).ne']
  constructor
  · intro h
    simpa only [mul_one] using (h.mul (tendsto_delangeWeight_mul_pow_atTop k)).congr'
      ((eventually_gt_atTop (0 : ℝ)).mono heq)
  · intro h
    have hdiv := h.div (tendsto_delangeWeight_mul_pow_atTop k) one_ne_zero
    rw [div_one] at hdiv
    refine hdiv.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun t ht ↦ ?_)
    exact (div_eq_iff (mul_ne_zero (delangeWeight_pos ht).ne' (pow_pos ht k).ne')).mpr
      (heq t ht).symm

/-- **Monotone removal of `squaredSinc` smoothing** (Delange 1954, §3.4, pp. 227–228): if `α` is
nondecreasing on `[0, ∞)` and, along arbitrarily large bandwidths `ell`, the weighted integrands
`t ↦ delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T)` are eventually integrable on
`[0, ∞)` as `T → ∞` and their integrals converge to `C`, then `α t / (exp (a * t) * t ^ k) → C` as
`t → ∞`.

No sign hypothesis on `a` or `α` is needed; a single bandwidth does not suffice (see
`exists_not_tendsto_of_single_bandwidth`). -/
theorem monotoneUnsmoothing {α : ℝ → ℝ} {a C : ℝ} {k : ℕ}
    (hα : MonotoneOn α (Ici 0))
    (hsmooth : ∃ᶠ ell in atTop,
      (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T))
        atTop (𝓝 C)) :
    Tendsto (fun t : ℝ ↦ α t / (exp (a * t) * t ^ k)) atTop (𝓝 C) := by
  rw [tendsto_div_exp_mul_pow_iff]
  by_cases hpos : ∃ t₀ ∈ Ici (0 : ℝ), 0 ≤ α t₀
  · obtain ⟨t₀, ht₀, hαt₀⟩ := hpos
    exact tendsto_weighted_of_monotoneOn_eventually_nonneg hα ht₀ hαt₀ hsmooth
  · push Not at hpos
    let g : ℝ → ℝ := fun t ↦ -α t
    have hgsmooth : ∃ᶠ ell in atTop,
        (∀ᶠ T in atTop, IntegrableOn (fun t : ℝ ↦
          delangeWeight k t * exp (-a * t) * g t * squaredSinc ell (t - T)) (Ici 0)) ∧
        Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
          delangeWeight k t * exp (-a * t) * g t * squaredSinc ell (t - T))
          atTop (𝓝 (-C)) := by
      refine hsmooth.mono fun ell ⟨hint, hlim⟩ ↦ ⟨hint.mono fun T hT ↦ ?_, ?_⟩
      · refine hT.neg.congr (ae_of_all _ fun t ↦ ?_)
        simp only [g, Pi.neg_apply]
        ring
      · simpa only [g, mul_neg, neg_mul, integral_neg] using hlim.neg
    have hglim := tendsto_weighted_of_antitoneOn_nonneg
      (fun x hx y hy hxy ↦ neg_le_neg (hα hx hy hxy))
      (fun t ht ↦ le_of_lt (neg_pos.mpr (hpos t ht))) hgsmooth
    simpa only [g, mul_neg, neg_neg] using hglim.neg

/-! ### Counterexample at a single bandwidth -/

/-- Derivative of the auxiliary oscillatory tail `(C + ε cos (3 ell t)) exp (a t) / w_k(t)` at any
`t > 0`. -/
private theorem hasDerivAt_counterexample_tail {a C ell ε t : ℝ} {k : ℕ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ ↦ (C + ε * cos (3 * ell * x)) * exp (a * x) / delangeWeight k x)
      (exp (a * t) / delangeWeight k t *
        (-3 * ell * ε * sin (3 * ell * t) +
          (a - deriv (delangeWeight k) t / delangeWeight k t) *
            (C + ε * cos (3 * ell * t)))) t := by
  have hw_pos : 0 < delangeWeight k t := delangeWeight_pos ht
  have h1 : HasDerivAt (fun x : ℝ ↦ C + ε * cos (3 * ell * x))
      (-3 * ell * ε * sin (3 * ell * t)) t := by
    have hmul : HasDerivAt (fun x : ℝ ↦ 3 * ell * x) (3 * ell) t := by
      simpa using (hasDerivAt_id' t).const_mul (3 * ell)
    convert (hmul.cos.const_mul ε).const_add C using 1
    ring
  have h2 : HasDerivAt (fun x : ℝ ↦ exp (a * x)) (a * exp (a * t)) t := by
    have hmul : HasDerivAt (fun x : ℝ ↦ a * x) a t := by
      simpa using (hasDerivAt_id' t).const_mul a
    convert hmul.exp using 1
    ring
  have h3 : HasDerivAt (delangeWeight k) (deriv (delangeWeight k) t) t :=
    (hasDerivAt_delangeWeight k t).differentiableAt.hasDerivAt
  convert (h1.mul h2).div h3 hw_pos.ne' using 1
  simp only [Pi.mul_apply]
  field_simp [hw_pos.ne']
  ring

/-- The auxiliary smooth function `f(t) = (C + ε cos (3 ell t)) exp (a t) / w_k(t)` is
nondecreasing on `[t₀, ∞)` once `w_k'(t) / w_k(t) ≤ a / 2` and `ε = a C / (2 (a + 6 ell))`. -/
private theorem monotoneOn_counterexample_tail {a C ell t₀ : ℝ} {k : ℕ}
    (ha : 0 < a) (hC : 0 < C) (hell : 0 < ell) (ht₀ : 0 < t₀)
    (hlog : ∀ t ≥ t₀, deriv (delangeWeight k) t / delangeWeight k t ≤ a / 2) :
    let ε := a * C / (2 * (a + 6 * ell))
    MonotoneOn (fun t : ℝ ↦ (C + ε * cos (3 * ell * t)) * exp (a * t) / delangeWeight k t)
      (Ici t₀) := by
  intro ε
  have hε_pos : 0 < ε := by positivity
  have hε_eq : (a / 2) * (C - ε) - 3 * ell * ε = a * C / 4 := by
    simp only [ε]
    field_simp [(by positivity : 2 * (a + 6 * ell) ≠ 0)]
    ring
  have hCε : 0 < C - ε := by
    have : 2 * (a + 6 * ell) * ε = a * C := mul_div_cancel₀ _ (by positivity)
    nlinarith
  refine monotoneOn_of_deriv_nonneg (convex_Ici t₀)
    (fun t ht ↦ (hasDerivAt_counterexample_tail
      (lt_of_lt_of_le ht₀ ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hasDerivAt_counterexample_tail
      (lt_of_lt_of_le ht₀ (interior_subset ht))).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ ?_)
  have ht' : t ∈ Ici t₀ := interior_subset ht
  have ht_pos : 0 < t := lt_of_lt_of_le ht₀ ht'
  rw [(hasDerivAt_counterexample_tail ht_pos).deriv]
  refine mul_nonneg (div_nonneg (exp_pos _).le (delangeWeight_pos ht_pos).le) ?_
  have hcos : C - ε ≤ C + ε * cos (3 * ell * t) := by nlinarith [neg_one_le_cos (3 * ell * t)]
  have hsin : -3 * ell * ε ≤ -3 * ell * ε * sin (3 * ell * t) := by
    nlinarith [sin_le_one (3 * ell * t), mul_pos hell hε_pos]
  have hprod : (a / 2) * (C - ε) ≤
      (a - deriv (delangeWeight k) t / delangeWeight k t) * (C + ε * cos (3 * ell * t)) :=
    mul_le_mul (by linarith [hlog t ht']) hcos hCε.le (by linarith [hlog t ht'])
  linarith [hε_eq, mul_pos ha hC]

/-- Full-line `squaredSinc ell` convolution of `t ↦ C + ε cos (3 ell t)` equals `C`. -/
private theorem integral_counterexample_full {C ell ε : ℝ} (hell : 0 < ell) (T : ℝ) :
    ∫ t : ℝ, (C + ε * cos (3 * ell * t)) * squaredSinc ell (t - T) = C := by
  have hsplit : (fun t : ℝ ↦ (C + ε * cos (3 * ell * t)) * squaredSinc ell (t - T)) =
      fun t ↦ C * squaredSinc ell (t - T) + ε * (cos (3 * ell * t) * squaredSinc ell (t - T)) :=
    funext fun t ↦ by ring
  have hcos_int : Integrable (fun t : ℝ ↦ cos (3 * ell * t) * squaredSinc ell (t - T)) :=
    ((integrable_squaredSinc ell).comp_sub_right T).bdd_mul
      (by fun_prop : Continuous fun t ↦ cos (3 * ell * t)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ abs_cos_le_one (3 * ell * t))
  rw [hsplit, integral_add (((integrable_squaredSinc ell).comp_sub_right T).const_mul C)
    (hcos_int.const_mul ε), integral_const_mul, integral_const_mul,
    integral_sub_right_eq_self (squaredSinc ell) T, squaredSinc_mass hell,
    integral_cos_mul_squaredSinc_eq_zero hell.le (by rw [abs_of_pos (by positivity)]; linarith) T]
  ring

/-- For `0 ≤ C` and `0 ≤ ε`, the oscillatory profile `C + ε cos x` has absolute value at most
`C + ε`. -/
private theorem abs_add_mul_cos_le {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (x : ℝ) :
    |C + ε * cos x| ≤ C + ε :=
  abs_le.mpr ⟨by nlinarith [neg_one_le_cos x], by nlinarith [cos_le_one x]⟩

/-- The truncated oscillatory profile `t ↦ if t < t₀ then 0 else C + ε cos (3 ell t)` has
`squaredSinc ell` half-line convolution tending to `C` as `T → ∞`. -/
private theorem tendsto_counterexample_convolution {C ell ε t₀ : ℝ} (hC : 0 < C) (hell : 0 < ell)
    (hε : 0 < ε) (ht₀ : 0 < t₀) :
    Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
      (if t < t₀ then 0 else C + ε * cos (3 * ell * t)) * squaredSinc ell (t - T)) atTop (𝓝 C) := by
  let J0 : ℝ → ℝ := fun t ↦ C + ε * cos (3 * ell * t)
  have hJ0_abs : ∀ t : ℝ, |J0 t| ≤ C + ε := fun t ↦ abs_add_mul_cos_le hC.le hε.le _
  have hJ0K_int : ∀ T : ℝ, Integrable (fun t : ℝ ↦ J0 t * squaredSinc ell (t - T)) := fun T ↦
    ((integrable_squaredSinc ell).comp_sub_right T).bdd_mul
      (by fun_prop : Continuous J0).aestronglyMeasurable (Eventually.of_forall hJ0_abs)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hupper : Tendsto (fun T : ℝ ↦ (C + ε) * (2 / (π * ell * (T - t₀)))) atTop (𝓝 0) := by
    have hden : Tendsto (fun T : ℝ ↦ π * ell * (T - t₀)) atTop atTop :=
      ((tendsto_id.atTop_add (tendsto_const_nhds (x := -t₀))).congr
        fun _ ↦ (sub_eq_add_neg _ _).symm).const_mul_atTop (mul_pos pi_pos hell)
    simpa only [mul_zero] using (tendsto_const_nhds.div_atTop hden).const_mul (C + ε)
  refine squeeze_zero_norm' ?_ hupper
  filter_upwards [eventually_gt_atTop t₀] with T hT
  have hIci : ∫ t in Ici (0 : ℝ), (if t < t₀ then 0 else J0 t) * squaredSinc ell (t - T) =
      ∫ t in Ici t₀, J0 t * squaredSinc ell (t - T) :=
    (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ici.nullMeasurableSet
      (Ici_subset_Ici.mpr ht₀.le) (ae_of_all _ fun t ht ↦ by simp [not_le.mp ht.2])).trans
      (setIntegral_congr_fun measurableSet_Ici fun t ht ↦ by simp [not_lt.mpr ht])
  have hdiff : (∫ t in Ici t₀, J0 t * squaredSinc ell (t - T)) - C =
      -(∫ t in Iio t₀, J0 t * squaredSinc ell (t - T)) := by
    have hsp := integral_add_compl (s := Ici t₀) measurableSet_Ici (hJ0K_int T)
    rw [compl_Ici, integral_counterexample_full hell T] at hsp
    linarith
  rw [Real.norm_eq_abs, abs_norm, hIci, hdiff, norm_neg]
  calc ‖∫ t in Iio t₀, J0 t * squaredSinc ell (t - T)‖
      ≤ ∫ t in Iio t₀, ‖J0 t * squaredSinc ell (t - T)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Iio t₀, (C + ε) * squaredSinc ell (t - T) :=
        setIntegral_mono_on (hJ0K_int T).integrableOn.norm
          (((integrable_squaredSinc ell).comp_sub_right T).const_mul (C + ε)).integrableOn
          measurableSet_Iio fun t _ ↦ by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (squaredSinc_nonneg hell.le _)]
            exact mul_le_mul_of_nonneg_right (hJ0_abs t) (squaredSinc_nonneg hell.le _)
    _ = (C + ε) * ∫ t in Iio t₀, squaredSinc ell (t - T) := integral_const_mul _ _
    _ ≤ (C + ε) * ∫ v in {v : ℝ | T - t₀ ≤ |v|}, squaredSinc ell v :=
        mul_le_mul_of_nonneg_left (setIntegral_Iio_squaredSinc_le hell.le) (by linarith)
    _ ≤ (C + ε) * (2 / (π * ell * (T - t₀))) :=
        mul_le_mul_of_nonneg_left (integral_squaredSinc_tail_le hell.le (sub_pos.mpr hT))
          (by linarith)

/-- The truncated oscillatory profile `t ↦ if t < t₀ then 0 else C + ε cos (3 ell t)` is
integrable on `[0, ∞)` against every shifted `squaredSinc ell` kernel. -/
private theorem integrableOn_counterexample_profile {C ell ε t₀ : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦
      (if t < t₀ then 0 else C + ε * cos (3 * ell * t)) * squaredSinc ell (t - T)) (Ici 0) :=
  ((integrable_squaredSinc ell).comp_sub_right T).integrableOn.bdd_mul (c := C + ε)
    (Measurable.ite measurableSet_Iio measurable_const
      (by fun_prop : Continuous fun t : ℝ ↦ C + ε * cos (3 * ell * t)).measurable
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs]
      split_ifs
      · rw [abs_zero]
        positivity
      · exact abs_add_mul_cos_le hC.le hε.le _)

/-- If `delangeWeight k t * exp (-a * t) * α t` vanishes for `t < t₀` and equals
`C + ε * cos (3 * ell * t)` for `t ≥ t₀` (with `0 < ell` and `0 < ε`), then the normalised ratio
`α t / (exp (a * t) * t ^ k)` does not tend to `C` as `t → ∞`. -/
private theorem not_tendsto_counterexample {α : ℝ → ℝ} {a C ell ε t₀ : ℝ} {k : ℕ}
    (hell : 0 < ell) (hε : 0 < ε)
    (hJeq : ∀ t : ℝ, delangeWeight k t * exp (-a * t) * α t =
      if t < t₀ then 0 else C + ε * cos (3 * ell * t)) :
    ¬ Tendsto (fun t : ℝ ↦ α t / (exp (a * t) * t ^ k)) atTop (𝓝 C) := by
  rw [tendsto_div_exp_mul_pow_iff]
  intro hJlim
  have hseq : Tendsto (fun n : ℕ ↦ (2 * π * n) / (3 * ell)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos two_pos pi_pos)).atTop_div_const
      (by positivity)
  have hconst : Tendsto (fun n : ℕ ↦ delangeWeight k ((2 * π * n) / (3 * ell)) *
      exp (-a * ((2 * π * n) / (3 * ell))) * α ((2 * π * n) / (3 * ell))) atTop (𝓝 (C + ε)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hseq.eventually (eventually_ge_atTop t₀)] with n hn
    rw [hJeq]
    simp only [not_lt.mpr hn, ↓reduceIte]
    have harg : 3 * ell * ((2 * π * n) / (3 * ell)) = (n : ℝ) * (2 * π) := by
      field_simp [hell.ne']
    rw [harg, cos_nat_mul_two_pi, mul_one]
  linarith [tendsto_nhds_unique (hJlim.comp hseq) hconst]

/-- **One bandwidth does not suffice for monotone unsmoothing.** For every `a > 0`, `C > 0`,
`ell > 0`, and `k : ℕ`, there exists a nonnegative nondecreasing function `α` on `[0, ∞)` such that
for every `T : ℝ` the weighted integrand
`t ↦ delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T)` is integrable on `[0, ∞)` and
its integral over `[0, ∞)` tends to `C` as `T → ∞`, yet `α(t) / (exp (a t) t ^ k)` fails to converge
to `C`. -/
theorem exists_not_tendsto_of_single_bandwidth {a C ell : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hell : 0 < ell) (k : ℕ) :
    ∃ α : ℝ → ℝ, MonotoneOn α (Ici 0) ∧ (∀ t ∈ Ici (0 : ℝ), 0 ≤ α t) ∧
      (∀ T : ℝ, IntegrableOn (fun t : ℝ ↦
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T)) (Ici 0)) ∧
      Tendsto (fun T : ℝ ↦ ∫ t in Ici (0 : ℝ),
        delangeWeight k t * exp (-a * t) * α t * squaredSinc ell (t - T))
        atTop (𝓝 C) ∧
      ¬ Tendsto (fun t : ℝ ↦ α t / (exp (a * t) * t ^ k)) atTop (𝓝 C) := by
  let ε : ℝ := a * C / (2 * (a + 6 * ell))
  have hε_pos : 0 < ε := by positivity
  have hCε : 0 < C - ε := by
    have : 2 * (a + 6 * ell) * ε = a * C := mul_div_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨t₀, ht₀_ge⟩ := eventually_atTop.mp
    ((tendsto_deriv_delangeWeight_div_atTop k).eventually
      (Iic_mem_nhds (by positivity : (0 : ℝ) < a / 2)) |>.and (eventually_ge_atTop (1 : ℝ)))
  have ht₀_pos : 0 < t₀ := lt_of_lt_of_le zero_lt_one (ht₀_ge t₀ le_rfl).2
  let J0 : ℝ → ℝ := fun t ↦ C + ε * cos (3 * ell * t)
  let α : ℝ → ℝ := fun t ↦ if t < t₀ then 0 else J0 t * exp (a * t) / delangeWeight k t
  have hJ0_pos : ∀ t : ℝ, 0 < J0 t := fun t ↦ by
    have : C - ε ≤ J0 t := by simp only [J0]; nlinarith [neg_one_le_cos (3 * ell * t)]
    linarith
  have hα_nonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ α t := fun t _ ↦ by
    by_cases ht : t < t₀
    · simp [α, ht]
    · simp only [α, ht, ↓reduceIte]
      exact div_nonneg (mul_nonneg (hJ0_pos t).le (exp_pos _).le)
        (delangeWeight_pos (lt_of_lt_of_le ht₀_pos (not_lt.mp ht))).le
  have hα_mono : MonotoneOn α (Ici 0) := fun x _ y _ hxy ↦ by
    by_cases hy : y < t₀
    · simp [α, lt_of_le_of_lt hxy hy, hy]
    · by_cases hx : x < t₀
      · simp only [α, hx, ↓reduceIte]
        exact hα_nonneg y (le_trans ht₀_pos.le (not_lt.mp hy))
      · simp only [α, hx, hy, ↓reduceIte]
        exact monotoneOn_counterexample_tail ha hC hell ht₀_pos (fun t ht ↦ (ht₀_ge t ht).1)
          (not_lt.mp hx) (not_lt.mp hy) hxy
  have hJeq : ∀ t : ℝ, delangeWeight k t * exp (-a * t) * α t = if t < t₀ then 0 else J0 t :=
    fun t ↦ by
      by_cases ht : t < t₀
      · simp [α, ht]
      · simp only [α, ht, ↓reduceIte]
        have hw : delangeWeight k t ≠ 0 :=
          (delangeWeight_pos (lt_of_lt_of_le ht₀_pos (not_lt.mp ht))).ne'
        rw [neg_mul, exp_neg]
        field_simp [hw, (exp_pos (a * t)).ne']
  refine ⟨α, hα_mono, hα_nonneg, ?_, ?_, not_tendsto_counterexample hell hε_pos hJeq⟩
  · intro T
    simpa only [hJeq] using integrableOn_counterexample_profile hC hε_pos T
  · simpa only [hJeq] using tendsto_counterexample_convolution hC hell hε_pos ht₀_pos

end TauCeti.HigherPoleTauberian
