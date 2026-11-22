/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.FunctionalEquation

/-!
# Vertical-strip bounds for the logarithmic derivative of the Riemann zeta function

Away from the pole `s = 1`, the logarithmic derivative of `riemannZeta` on the half-plane
`1 < Re s` is bounded via the Hadamard partial-fraction positivity of `zetaEntireCompletion` on
`1 < Re s ≤ 2` and directly via the von Mangoldt Dirichlet series on `2 ≤ Re s`.

On `1 < Re s ≤ 2`, separating the poles of `zetaEntireCompletion` at `0` and `1` and dropping the
nonnegative sum over zeros (or keeping a single zero `ρ = β + i u` in the critical strip) yields
explicit upper bounds on `-Re (ζ'/ζ)(1 + δ + i u)` in terms of `δ / (δ ^ 2 + u ^ 2)` and
`log (|u| + 3)`. Taking `|t| ≥ t₀ > 1` absorbs the pole term at `s = 1` into `C * log |t|`, giving
the two Davenport §13 bounds `TauCeti.neg_re_logDeriv_riemannZeta_le`.

## Main results

* `TauCeti.norm_logDeriv_riemannZeta_le_of_two_le_re`: uniform bound
  `‖ζ'/ζ(s)‖ ≤ -(ζ'/ζ)(2).re` for `2 ≤ Re s`.
* `TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le`: strip upper bound for `0 < δ ≤ 1` and
  all real `u`, retaining the explicit pole contribution `δ / (δ ^ 2 + u ^ 2)`.
* `TauCeti.neg_re_logDeriv_riemannZeta_le`: Davenport's bounds for `-Re (ζ'/ζ)(1 + δ + 2 i t)` and
  `-Re (ζ'/ζ)(1 + δ + i t)` for all `δ > 0` and `|t| ≥ t₀ > 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13.
-/

public section

open Complex Filter LSeries Set TauCeti.LFunctions
open scoped LSeries.notation Topology

namespace TauCeti

/-- On the half-plane `2 ≤ Re s`, `‖ζ'/ζ(s)‖` is bounded by `-(ζ'/ζ)(2).re`. -/
theorem norm_logDeriv_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ -(logDeriv riemannZeta 2).re := by
  have hs1 : 1 < s.re := by linarith
  have h2 : 1 < ((2 : ℂ)).re := by norm_num
  have heq (z : ℂ) (hz : 1 < z.re) :
      logDeriv riemannZeta z = -LSeries ↗ArithmeticFunction.vonMangoldt z := by
    rw [logDeriv_apply]
    calc
      deriv riemannZeta z / riemannZeta z = -(-deriv riemannZeta z / riemannZeta z) := by ring
      _ = -LSeries ↗ArithmeticFunction.vonMangoldt z := by
          rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz]
  rw [heq s hs1, heq 2 h2, norm_neg, Complex.neg_re, neg_neg, LSeries, LSeries,
    Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt h2)]
  have hs2 : Summable fun n : ℕ ↦ (term ↗ArithmeticFunction.vonMangoldt (2 : ℂ) n).re :=
    Complex.reCLM.summable (ArithmeticFunction.LSeriesSummable_vonMangoldt h2)
  refine tsum_of_norm_bounded hs2.hasSum fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnpos : (0 : ℝ) < n := by positivity
  simp only [norm_term_eq, hn, ↓reduceIte]
  rw [term_of_ne_zero hn]
  have hcp : (n : ℂ) ^ (2 : ℂ) = (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, Complex.ofReal_cpow hnpos.le]
  rw [hcp, Complex.div_ofReal_re, Complex.ofReal_re, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  gcongr

private theorem exists_norm_logDeriv_Gammaℝ_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1 : ℝ) 2 →
      ‖logDeriv Gammaℝ s‖ ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨C, hC0, hC⟩ := Complex.exists_norm_digamma_le_log (a := 1 / 2) (b := 1) (by norm_num)
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  refine ⟨C / 2 + |Real.log Real.pi| / 2 + 1, by positivity, fun s hs ↦ ?_⟩
  have hpole : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [neg_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im] at hre
    linarith [hs.1, (n.cast_nonneg : (0 : ℝ) ≤ n)]
  rw [Complex.logDeriv_Gammaℝ hpole]
  have hs_half : (s / 2).re ∈ Icc (1 / 2 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · simp only [div_ofNat_re]
      linarith [hs.1]
    · simp only [div_ofNat_re]
      linarith [hs.2]
  have hψ := hC (s / 2) hs_half
  have him : |(s / 2).im| + 2 ≤ |s.im| + 3 := by
    simp only [div_ofNat_im, abs_div, abs_two]
    linarith [abs_nonneg s.im]
  have hlog_le : Real.log (|(s / 2).im| + 2) ≤ Real.log (|s.im| + 3) :=
    Real.log_le_log (by positivity) him
  have hlog3_le : 1 ≤ Real.log (|s.im| + 3) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im]))
  have h1 : ‖digamma (s / 2) / 2‖ ≤ (C / 2) * Real.log (|s.im| + 3) := by
    rw [norm_div, Complex.norm_two]
    have hmul : ‖digamma (s / 2)‖ ≤ C * Real.log (|s.im| + 3) :=
      hψ.trans (mul_le_mul_of_nonneg_left hlog_le hC0.le)
    linarith
  have h2 : ‖(Real.log Real.pi : ℂ) / 2‖ ≤ (|Real.log Real.pi| / 2) * Real.log (|s.im| + 3) := by
    rw [norm_div, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
    have hmul := mul_le_mul_of_nonneg_left hlog3_le (by positivity : 0 ≤ |Real.log Real.pi| / 2)
    linarith
  calc
    ‖digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖
        ≤ ‖digamma (s / 2) / 2‖ + ‖(Real.log Real.pi : ℂ) / 2‖ := norm_sub_le _ _
    _ ≤ (C / 2 + |Real.log Real.pi| / 2) * Real.log (|s.im| + 3) := by linarith
    _ ≤ (C / 2 + |Real.log Real.pi| / 2 + 1) * Real.log (|s.im| + 3) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)

private theorem logDeriv_zetaEntireCompletion_eq_add {s : ℂ} (hs : 1 < s.re) :
    logDeriv zetaEntireCompletion s =
      1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  have heq : zetaEntireCompletion =ᶠ[𝓝 s] fun z : ℂ ↦ z * (z - 1) * completedRiemannZeta z := by
    have h01 : ∀ᶠ z in 𝓝 s, 0 < z.re ∧ 1 < z.re :=
      Filter.Eventually.and
        ((isOpen_lt continuous_const continuous_re).mem_nhds (zero_lt_one.trans hs))
        ((isOpen_lt continuous_const continuous_re).mem_nhds hs)
    filter_upwards [h01] with z hz
    have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
    exact zetaEntireCompletion_eq_mul hz0 hz1
  have hd_prod : DifferentiableAt ℂ (fun z : ℂ ↦ z * (z - 1)) s := by fun_prop
  have hd_Λ : DifferentiableAt ℂ completedRiemannZeta s := differentiableAt_completedZeta hs0 hs1
  have hprod0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  have hld_prod : logDeriv (fun z : ℂ ↦ z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
    rw [logDeriv_fun_mul (f := fun z : ℂ ↦ z) (g := fun z : ℂ ↦ z - 1) s
      hs0 (sub_ne_zero.mpr hs1) (by fun_prop) (by fun_prop)]
    simp [logDeriv_apply]
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul (f := fun z : ℂ ↦ z * (z - 1)) (g := completedRiemannZeta)
      s hprod0 hΛ hd_prod hd_Λ,
    hld_prod, logDeriv_riemannZeta_eq_completedRiemannZeta_sub_Gammaℝ hs0 hs1 hζ]
  ring

/-- On the vertical strip `1 < Re s ≤ 2` (`s = 1 + η + i u`), `-Re (ζ'/ζ)(1 + η + i u)` is
bounded above by `η / (η ^ 2 + u ^ 2) + C * log (|u| + 3)`, and if `ζ(β + i u) = 0` then it also
retains the single-zero term `-1 / (1 + η - β)`. -/
theorem exists_neg_re_logDeriv_riemannZeta_one_add_le :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤
        η / (η ^ 2 + u ^ 2) + C * Real.log (|u| + 3) ∧
      ∀ β : ℝ, riemannZeta (β + u * I) = 0 →
        -(logDeriv riemannZeta (1 + η + u * I)).re ≤
          -1 / (1 + η - β) + η / (η ^ 2 + u ^ 2) + C * Real.log (|u| + 3) := by
  obtain ⟨C₀, hC₀, hΓ⟩ := exists_norm_logDeriv_Gammaℝ_le_log
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  refine ⟨C₀ + 2, by positivity, fun η hη hη1 u ↦ ?_⟩
  set s : ℂ := 1 + η + u * I
  have hs_re : s.re = 1 + η := by simp [s]
  have hs_im : s.im = u := by simp [s]
  have hs1 : 1 < s.re := by linarith
  have hsIcc : s.re ∈ Icc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hsplit := congrArg Complex.re (logDeriv_zetaEntireCompletion_eq_add hs1)
  simp only [Complex.add_re] at hsplit
  have h1s : (1 / s).re ≤ 1 := by
    rw [one_div, Complex.inv_re]
    have hsq : s.re ^ 2 ≤ Complex.normSq s := by
      rw [Complex.normSq_apply, ← sq]
      nlinarith [sq_nonneg s.im]
    have hs0 : 0 < s.re := by linarith
    calc
      s.re / Complex.normSq s ≤ s.re / s.re ^ 2 :=
        div_le_div_of_nonneg_left hs0.le (sq_pos_of_pos hs0) hsq
      _ = 1 / s.re := by field_simp
      _ ≤ 1 := div_le_one_of_le₀ hs1.le (by linarith)
  have h1s1 : (1 / (s - 1)).re = η / (η ^ 2 + u ^ 2) := by
    have hs' : s - 1 = (η : ℂ) + u * I := by simp [s]; ring
    rw [hs', one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    ring
  have hΓs : (logDeriv Gammaℝ s).re ≤ C₀ * Real.log (|u| + 3) := by
    calc
      (logDeriv Gammaℝ s).re ≤ ‖logDeriv Gammaℝ s‖ := Complex.re_le_norm _
      _ ≤ C₀ * Real.log (|s.im| + 3) := hΓ s hsIcc
      _ = C₀ * Real.log (|u| + 3) := by rw [hs_im]
  have hlog3_le : 1 ≤ Real.log (|u| + 3) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg u]))
  have hξ_ne : zetaEntireCompletion s ≠ 0 := zetaEntireCompletion_ne_zero_of_one_le_re hs1.le
  have hξ0 : riemannZetaData.entireCompletion 0 ≠ 0 := by simp
  have hξ_le : ∀ ρ : ℂ, riemannZetaData.entireCompletion ρ = 0 → ρ.re ≤ s.re := by
    intro ρ hρ
    rw [riemannZetaData_entireCompletion] at hρ
    exact (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le.trans hs1.le
  have hξ_nonneg : 0 ≤ (logDeriv zetaEntireCompletion s).re := by
    simpa only [riemannZetaData_entireCompletion] using
      riemannZetaData_hasFunctionalEquation.re_logDeriv_entireCompletion_nonneg_of_zero_ne_zero
        riemannZetaData_hasMeromorphicContinuation
        (by simpa only [riemannZetaData_entireCompletion] using orderLE_zetaEntireCompletion)
        hξ0 (by simpa only [riemannZetaData_entireCompletion] using hξ_ne) hξ_le
  have hbase : -(logDeriv riemannZeta s).re ≤
      η / (η ^ 2 + u ^ 2) + (C₀ + 1) * Real.log (|u| + 3) := by
    linarith
  refine ⟨hbase.trans (by gcongr; linarith), fun β hβ ↦ ?_⟩
  by_cases hβ0 : β ≤ 0
  · have h1ηβ : 1 ≤ 1 + η - β := by linarith
    have hinv : -1 ≤ -1 / (1 + η - β) := by
      rw [neg_div, neg_le_neg_iff]
      exact div_le_one_of_le₀ h1ηβ (by linarith)
    linarith
  · push Not at hβ0
    have hβ1 : β < 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_le_re (by simpa using h) hβ
    set ρ : ℂ := β + u * I
    have hρ0 : ρ ≠ 0 := fun h ↦ by
      have := congrArg Complex.re h
      simp only [ρ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, zero_re] at this
      linarith
    have hρ1 : ρ ≠ 1 := fun h ↦ by
      have := congrArg Complex.re h
      simp only [ρ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, one_re] at this
      linarith
    have hΓρ : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simpa [ρ] using hβ0)
    have hΛρ : completedRiemannZeta ρ = 0 := by
      rw [riemannZeta_def_of_ne_zero hρ0, div_eq_zero_iff] at hβ
      exact hβ.resolve_right hΓρ
    have hξρ : zetaEntireCompletion ρ = 0 := by
      rw [zetaEntireCompletion_eq_mul hρ0 hρ1, hΛρ, mul_zero]
    have hsingle :=
      riemannZetaData_hasFunctionalEquation.re_one_div_sub_le_re_logDeriv_entireCompletion
        riemannZetaData_hasMeromorphicContinuation
        (by simpa only [riemannZetaData_entireCompletion] using orderLE_zetaEntireCompletion)
        hξ0 (by simpa only [riemannZetaData_entireCompletion] using hξ_ne) hξ_le
        (by simpa only [riemannZetaData_entireCompletion] using hξρ)
    rw [riemannZetaData_entireCompletion] at hsingle
    have hsρ : s - ρ = ((1 + η - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, ρ]
    rw [hsρ, one_div, ← ofReal_inv, ofReal_re, ← one_div] at hsingle
    rw [neg_div]
    linarith

/-- **Layer 6.4d at `K = ℚ`, off the real axis.** For every `t₀ > 1` there is `C` such that, for
`η > 0` and `|t| ≥ t₀`, `-Re (ζ'/ζ)(1 + η + 2it) ≤ C log |t|`, and
`-Re (ζ'/ζ)(1 + η + it) ≤ -1/(1 + η - β) + C log |t|` whenever `β + it` is a zero of `ζ`
(Davenport §13). -/
theorem neg_re_logDeriv_riemannZeta_le (t₀ : ℝ) (ht₀ : 1 < t₀) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ t : ℝ, t₀ ≤ |t| →
      -(logDeriv riemannZeta (1 + η + 2 * t * I)).re ≤ C * Real.log |t| ∧
        ∀ β : ℝ, riemannZeta (β + t * I) = 0 →
          -(logDeriv riemannZeta (1 + η + t * I)).re ≤ -1 / (1 + η - β) + C * Real.log |t| := by
  obtain ⟨C₁, hC₁, hstrip⟩ := exists_neg_re_logDeriv_riemannZeta_one_add_le
  have hlogt₀ : 0 < Real.log t₀ := Real.log_pos ht₀
  set Z2 : ℝ := max 0 (-(logDeriv riemannZeta 2).re) + 1
  set L5 : ℝ := Real.log 5 / Real.log t₀ + 1
  set C : ℝ := max (Z2 / Real.log t₀) (1 / Real.log t₀ + C₁ * L5)
  refine ⟨C, fun η hη t ht ↦ ?_⟩
  have htpos : 1 < |t| := ht₀.trans_le ht
  have hlogt_pos : 0 < Real.log |t| := Real.log_pos htpos
  have hlog_le : Real.log t₀ ≤ Real.log |t| := Real.log_le_log (by positivity) ht
  have h1_le : 1 ≤ (1 / Real.log t₀) * Real.log |t| := by
    have hmul := mul_le_mul_of_nonneg_left hlog_le (one_div_nonneg.mpr hlogt₀.le)
    rwa [one_div_mul_cancel hlogt₀.ne'] at hmul
  have hZ2_le : Z2 ≤ C * Real.log |t| := by
    have hZ2_pos : 0 ≤ Z2 := by positivity
    calc
      Z2 = Z2 * 1 := (mul_one Z2).symm
      _ ≤ Z2 * ((1 / Real.log t₀) * Real.log |t|) := mul_le_mul_of_nonneg_left h1_le hZ2_pos
      _ = (Z2 / Real.log t₀) * Real.log |t| := by ring
      _ ≤ C * Real.log |t| := mul_le_mul_of_nonneg_right (le_max_left _ _) hlogt_pos.le
  have hlog_u (u : ℝ) (hu : |u| ≤ 2 * |t|) : Real.log (|u| + 3) ≤ L5 * Real.log |t| := by
    have h5 : |u| + 3 ≤ 5 * |t| := by linarith
    have hlog5 : Real.log (5 * |t|) = Real.log 5 + Real.log |t| :=
      Real.log_mul (by norm_num) (by positivity)
    have hlog5_pos : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    have hterm5 : Real.log 5 ≤ (Real.log 5 / Real.log t₀) * Real.log |t| := by
      calc
        Real.log 5 = Real.log 5 * 1 := (mul_one _).symm
        _ ≤ Real.log 5 * ((1 / Real.log t₀) * Real.log |t|) :=
            mul_le_mul_of_nonneg_left h1_le hlog5_pos
        _ = (Real.log 5 / Real.log t₀) * Real.log |t| := by ring
    calc
      Real.log (|u| + 3) ≤ Real.log (5 * |t|) := Real.log_le_log (by positivity) h5
      _ = Real.log 5 + Real.log |t| := hlog5
      _ ≤ L5 * Real.log |t| := by dsimp [L5]; linarith
  by_cases hη1 : η ≤ 1
  · have hpole_u (u : ℝ) (hu : 1 ≤ |u|) : η / (η ^ 2 + u ^ 2) ≤ 1 := by
      have hu2 : 1 ≤ u ^ 2 := by
        simpa only [one_pow, sq_abs] using (sq_le_sq₀ zero_le_one (abs_nonneg u)).mpr hu
      calc
        η / (η ^ 2 + u ^ 2) ≤ 1 / (0 + 1) :=
          div_le_div₀ (by positivity) hη1 (by positivity) (by nlinarith [sq_nonneg η])
        _ = 1 := by norm_num
    have hmain (u : ℝ) (hu1 : 1 ≤ |u|) (hu2 : |u| ≤ 2 * |t|) :
        η / (η ^ 2 + u ^ 2) + C₁ * Real.log (|u| + 3) ≤ C * Real.log |t| := by
      calc
        η / (η ^ 2 + u ^ 2) + C₁ * Real.log (|u| + 3)
            ≤ 1 + C₁ * (L5 * Real.log |t|) :=
              add_le_add (hpole_u u hu1) (mul_le_mul_of_nonneg_left (hlog_u u hu2) hC₁.le)
        _ ≤ (1 / Real.log t₀) * Real.log |t| + C₁ * (L5 * Real.log |t|) := by linarith
        _ = (1 / Real.log t₀ + C₁ * L5) * Real.log |t| := by ring
        _ ≤ C * Real.log |t| := mul_le_mul_of_nonneg_right (le_max_right _ _) hlogt_pos.le
    obtain ⟨h2t, -⟩ := hstrip η hη hη1 (2 * t)
    obtain ⟨-, htβ⟩ := hstrip η hη hη1 t
    have h2t_mul : (1 : ℂ) + η + 2 * t * I = 1 + η + ((2 * t : ℝ) : ℂ) * I := by
      push_cast; ring
    refine ⟨?_, fun β hβ ↦ ?_⟩
    · rw [h2t_mul]
      refine h2t.trans (hmain (2 * t) ?_ ?_)
      · rw [abs_mul, abs_two]; linarith
      · rw [abs_mul, abs_two]
    · have hle := htβ β hβ
      have hC := hmain t htpos.le (by linarith [abs_nonneg t])
      linarith
  · push Not at hη1
    have hre2 (u : ℝ) : 2 ≤ ((1 : ℂ) + η + u * I).re := by
      simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      linarith
    have hnorm (u : ℝ) :
        -(logDeriv riemannZeta (1 + η + u * I)).re ≤ -(logDeriv riemannZeta 2).re := by
      rw [← Complex.neg_re]
      exact (Complex.re_le_norm (-logDeriv riemannZeta (1 + η + u * I))).trans
        (norm_neg (logDeriv riemannZeta (1 + η + u * I)) ▸
          norm_logDeriv_riemannZeta_le_of_two_le_re (hre2 u))
    refine ⟨?_, fun β hβ ↦ ?_⟩
    · have hz : -(logDeriv riemannZeta (1 + η + 2 * t * I)).re ≤ -(logDeriv riemannZeta 2).re := by
        simpa [mul_assoc] using hnorm (2 * t)
      have : -(logDeriv riemannZeta 2).re ≤ Z2 := by
        dsimp [Z2]; linarith [le_max_right 0 (-(logDeriv riemannZeta 2).re)]
      linarith
    · have hβ1 : β < 1 := by
        by_contra h
        push Not at h
        exact riemannZeta_ne_zero_of_one_le_re (by simpa using h) hβ
      have h1ηβ : 1 ≤ 1 + η - β := by linarith
      have hinv : -1 ≤ -1 / (1 + η - β) := by
        rw [neg_div, neg_le_neg_iff]
        exact div_le_one_of_le₀ h1ηβ (by linarith)
      have hz := hnorm t
      have : -(logDeriv riemannZeta 2).re + 1 ≤ Z2 := by
        dsimp [Z2]; linarith [le_max_right 0 (-(logDeriv riemannZeta 2).re)]
      linarith

end TauCeti
