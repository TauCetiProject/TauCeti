/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Log
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The John–Nirenberg rate is sharp for `log ‖x‖`

The John–Nirenberg inequality says that a function of bounded mean oscillation has exponentially
small distribution tails on every ball,
`|{x ∈ B : |f x - f_B| > t}| ≤ C₁ |B| exp (-C₂ t / ‖f‖_{BMO})`, and hence is exponentially
integrable on `B` at every rate below `C₂ / ‖f‖_{BMO}`. The function `log ‖x‖` shows that the rate
cannot be arbitrary. On a finite-dimensional real normed space `E` of dimension `n ≥ 1` with an
additive Haar measure `μ`, near the origin `exp (c |log ‖x‖ - a|)` is comparable to `‖x‖ ^ (-c)`,
whatever the constant `a`, and `‖x‖ ^ (-c)` is integrable near the origin exactly when `c < n`.
So:

* `exp (c |log ‖x‖ - a|)` is integrable on a ball centred at the origin exactly when `c < n`
  (`TauCeti.integrableOn_exp_mul_abs_log_norm_sub_iff`);
* an exponential tail bound `μ {x ∈ B(0, r) : |log ‖x‖ - a| > t} ≤ C e^{-κ t} μ(B(0, r))`, even
  only for large `t`, forces `κ ≤ n`
  (`TauCeti.le_finrank_of_eventually_measure_lt_abs_log_norm_sub_le`), since the set contains the
  ball `B(0, e^{-t - |log r - a|} r)`, of measure `e^{-n (t + |log r - a|)} μ(B(0, r))`;
* consequently every John–Nirenberg constant `C₂` valid for `log ‖·‖` on a ball centred at the
  origin satisfies `C₂ ≤ n ‖log ‖·‖‖_{BMO}`
  (`TauCeti.le_finrank_mul_toReal_bmoSeminorm_log_norm`), a non-vacuous bound on the constant,
  since `‖log ‖·‖‖_{BMO}` is finite and positive by `TauCeti.bmoSeminorm_log_norm_le` and
  `TauCeti.ofReal_le_setLAverage_enorm_log_norm_sub_setAverage_ball_zero`.

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Theorem 3.1.6 and Section 3.1.
* F. John, L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
  **14** (1961), 415–426.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- For `L ≤ b`, the distance from `L` to `a` is `b - L` up to the error `|b - a|`. -/
private theorem abs_sub_mem_Icc {L a b : ℝ} (hL : L ≤ b) :
    |L - a| ∈ Icc (b - L - |b - a|) (b - L + |b - a|) := by
  have h₁ := le_abs_self (b - a)
  have h₂ := neg_abs_le (b - a)
  exact ⟨by linarith [neg_abs_le (L - a)], abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- **Exponential integrability of `log ‖x‖` is sharp.** On a nontrivial finite-dimensional real
normed space of dimension `n` with an additive Haar measure, for every constant `a`, the function
`exp (c |log ‖x‖ - a|)` is integrable on a ball of positive radius centred at the origin exactly
when `c < n`. Taking for `a` the mean of `log ‖·‖` over the ball, this shows that the
exponential integrability given by the John–Nirenberg inequality holds only up to a finite rate. -/
theorem integrableOn_exp_mul_abs_log_norm_sub_iff [Nontrivial E] {r : ℝ} (hr : 0 < r)
    (a c : ℝ) :
    IntegrableOn (fun x : E => Real.exp (c * |Real.log ‖x‖ - a|)) (ball 0 r) μ ↔
      c < finrank ℝ E := by
  have hmeas : AEStronglyMeasurable (fun x : E => Real.exp (c * |Real.log ‖x‖ - a|))
      (μ.restrict (ball 0 r)) :=
    (by fun_prop : Measurable fun x : E => Real.exp (c * |Real.log ‖x‖ - a|)).aestronglyMeasurable
  have hn : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos (R := ℝ) (M := E)
  rcases lt_or_ge c 0 with hc | hc
  · -- For `c < 0` the integrand is at most `1` on a ball of finite measure.
    refine iff_of_true ((integrableOn_const (C := (1 : ℝ)) measure_ball_lt_top.ne).mono' hmeas
      (ae_of_all _ fun x => ?_)) (by linarith)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hc.le (abs_nonneg _)
  set δ := |Real.log r - a|
  -- Off the null set `{0}`, `‖x‖ ^ (-c) = exp (-c log ‖x‖)` and `log ‖x‖ < log r`.
  have hae : ∀ᵐ x ∂μ.restrict (ball (0 : E) r), 0 < ‖x‖ ∧ Real.log ‖x‖ ≤ Real.log r ∧
      ‖x‖ ^ (-c) = Real.exp (-(c * Real.log ‖x‖)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (μ := μ) (0 : E)))] with x hx hx0
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 (by simpa using hx0)
    refine ⟨hpos, Real.log_le_log hpos (mem_ball_zero_iff.1 hx).le, ?_⟩
    rw [Real.rpow_def_of_pos hpos]
    ring_nf
  constructor
  · intro hint
    -- `‖x‖ ^ (-c) ≤ exp (-c (log r - δ)) exp (c |log ‖x‖ - a|)`.
    have hrpow : IntegrableOn (fun x : E => ‖x‖ ^ (-c)) (ball 0 r) μ := by
      refine (hint.const_mul (Real.exp (-(c * (Real.log r - δ))))).mono'
        (by fun_prop : Measurable fun x : E => ‖x‖ ^ (-c)).aestronglyMeasurable
        (hae.mono fun x ⟨hpos, hlog, hx⟩ => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _), hx, ← Real.exp_add]
      have := mul_le_mul_of_nonneg_left (abs_sub_mem_Icc (a := a) hlog).1 hc
      exact Real.exp_le_exp.2 (by nlinarith)
    have := (integrableOn_norm_rpow_ball_iff (mu := μ) hr).1 hrpow
    linarith
  · intro hcn
    -- `exp (c |log ‖x‖ - a|) ≤ exp (c (log r + δ)) ‖x‖ ^ (-c)`.
    refine ((integrableOn_norm_rpow_ball (mu := μ) (s := -c) (by linarith) (R := r)).const_mul
      (Real.exp (c * (Real.log r + δ)))).mono' hmeas (hae.mono fun x ⟨_, hlog, hx⟩ => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, hx, ← Real.exp_add]
    have := mul_le_mul_of_nonneg_left (abs_sub_mem_Icc (a := a) hlog).2 hc
    exact Real.exp_le_exp.2 (by nlinarith)

/-- **The exponential tail rate of `log ‖x‖` is at most the dimension.** On a nontrivial
finite-dimensional real normed space of dimension `n` with an additive Haar measure, let `a` be a
constant and `B = B(0, r)` a ball of positive radius. If for all large `t`

`μ {x ∈ B : t < |log ‖x‖ - a|} ≤ C exp (-κ t) μ(B)`,

then `κ ≤ n`. -/
theorem le_finrank_of_eventually_measure_lt_abs_log_norm_sub_le [Nontrivial E] {r : ℝ}
    (hr : 0 < r) (a : ℝ) {C κ : ℝ}
    (h : ∀ᶠ t in atTop, μ {x ∈ ball (0 : E) r | t < |Real.log ‖x‖ - a|} ≤
      ENNReal.ofReal (C * Real.exp (-(κ * t))) * μ (ball 0 r)) :
    κ ≤ finrank ℝ E := by
  set n : ℕ := finrank ℝ E
  set δ := |Real.log r - a|
  by_contra! hκ
  have hB0 : μ (ball (0 : E) r) ≠ 0 := (measure_ball_pos μ 0 hr).ne'
  have hkey : ∀ᶠ t in atTop, Real.exp ((κ - n) * t) ≤ C * Real.exp (n * δ) := by
    filter_upwards [h, eventually_ge_atTop 0] with t ht ht0
    -- Up to its centre, the ball `B(0, ρ)` with `ρ = e^{-δ - t} r` lies in the superlevel set, so
    -- `e^{-n (δ + t)} μ(B) ≤ C e^{-κ t} μ(B)`.
    set ρ := Real.exp (-(δ + t)) * r
    have hρr : ρ ≤ r := mul_le_of_le_one_left hr.le
      (Real.exp_le_one_iff.2 (by linarith [abs_nonneg (Real.log r - a)]))
    have hsub : ball (0 : E) ρ \ {0} ⊆ {x ∈ ball (0 : E) r | t < |Real.log ‖x‖ - a|} := by
      rintro x ⟨hx, hx0⟩
      have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.1 hx
      refine ⟨mem_ball_zero_iff.2 (hxρ.trans_le hρr), ?_⟩
      have hlog := Real.log_lt_log (norm_pos_iff.2 hx0) hxρ
      rw [Real.log_mul (Real.exp_pos _).ne' hr.ne', Real.log_exp] at hlog
      rw [abs_sub_comm]
      exact (by linarith [le_abs_self (Real.log r - a)] : t < a - Real.log ‖x‖).trans_le
        (le_abs_self _)
    have hball : ENNReal.ofReal (Real.exp (-(δ + t)) ^ n) * μ (ball (0 : E) r) ≤
        ENNReal.ofReal (C * Real.exp (-(κ * t))) * μ (ball 0 r) :=
      calc ENNReal.ofReal (Real.exp (-(δ + t)) ^ n) * μ (ball (0 : E) r) = μ (ball (0 : E) ρ) :=
            (Measure.addHaar_ball_mul_of_pos μ 0 (Real.exp_pos _) r).symm
        _ = μ (ball (0 : E) ρ \ {0}) := (measure_sdiff_null (measure_singleton 0)).symm
        _ ≤ _ := (measure_mono hsub).trans ht
    rw [ENNReal.mul_le_mul_iff_left hB0 measure_ball_lt_top.ne, ENNReal.ofReal_le_ofReal_iff',
      ← Real.exp_natCast_mul] at hball
    have hle : Real.exp (n * -(δ + t)) ≤ C * Real.exp (-(κ * t)) :=
      hball.resolve_right (Real.exp_pos _).not_ge
    calc Real.exp ((κ - n) * t) = Real.exp (n * -(δ + t)) * Real.exp (κ * t + n * δ) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ C * Real.exp (-(κ * t)) * Real.exp (κ * t + n * δ) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = C * Real.exp (n * δ) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have htend : Tendsto (fun t : ℝ => Real.exp ((κ - n) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.2 hκ))
  obtain ⟨t, ht₁, ht₂⟩ := (hkey.and (htend.eventually_gt_atTop (C * Real.exp (n * δ)))).exists
  exact ht₁.not_gt ht₂

/-- **A bound on the John–Nirenberg constant.** On a nontrivial finite-dimensional real normed
space of dimension `n` with an additive Haar measure, write `‖log‖_{BMO}` for the BMO seminorm
of `log ‖·‖`, which is finite and positive. If the John–Nirenberg inequality holds for `log ‖·‖`
on a ball `B = B(0, r)` of positive radius with constants `C₁` and `C₂`, for all large `t`,

`μ {x ∈ B : t < |log ‖x‖ - (log ‖·‖)_B|} ≤ C₁ exp (-C₂ t / ‖log‖_{BMO}) μ(B)`,

then `C₂ ≤ n ‖log‖_{BMO}`. -/
theorem le_finrank_mul_toReal_bmoSeminorm_log_norm [Nontrivial E] {r : ℝ} (hr : 0 < r)
    {C₁ C₂ : ℝ}
    (h : ∀ᶠ t in atTop, μ {x ∈ ball (0 : E) r |
        t < |Real.log ‖x‖ - ⨍ y in ball (0 : E) r, Real.log ‖y‖ ∂μ|} ≤
      ENNReal.ofReal (C₁ * Real.exp (-(C₂ * t /
        (bmoSeminorm (fun x : E => Real.log ‖x‖) μ).toReal))) * μ (ball 0 r)) :
    C₂ ≤ finrank ℝ E * (bmoSeminorm (fun x : E => Real.log ‖x‖) μ).toReal := by
  set M := bmoSeminorm (fun x : E => Real.log ‖x‖) μ
  have hM : 0 < M.toReal := by
    refine ENNReal.toReal_pos (lt_of_lt_of_le ?_
      ((ofReal_le_setLAverage_enorm_log_norm_sub_setAverage_ball_zero (μ := μ) one_pos).trans
        (setLAverage_enorm_sub_setAverage_le_bmoSeminorm _ μ 0 1))).ne'
      (bmoSeminorm_log_norm_le.trans_lt (by finiteness)).ne
    exact ENNReal.ofReal_pos.2 (div_pos (Real.log_pos one_lt_two) (by positivity))
  have hκ := le_finrank_of_eventually_measure_lt_abs_log_norm_sub_le (μ := μ) hr
    (⨍ y in ball (0 : E) r, Real.log ‖y‖ ∂μ) (C := C₁) (κ := C₂ / M.toReal)
    (h.mono fun t ht => by rwa [div_mul_eq_mul_div])
  rwa [div_le_iff₀ hM] at hκ

end TauCeti
