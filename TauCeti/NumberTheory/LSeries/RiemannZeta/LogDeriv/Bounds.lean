/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Bound
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.LogDeriv
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Basic

/-!
# Vertical-strip bounds for the logarithmic derivative of the Riemann zeta function

Away from the pole `s = 1`, the logarithmic derivative of `riemannZeta` on the half-plane
`1 < Re s` is bounded via the Hadamard partial-fraction positivity of `zetaEntireCompletion` on
`1 < Re s ≤ 2` and directly via `TauCeti.norm_logDeriv_riemannZeta_le_of_two_le_re` on
`2 ≤ Re s` (built on Michael Stoll's
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` via
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`).

On `1 < Re s ≤ 2`, using `logDeriv_zetaEntireCompletion_eq_add` separates the archimedean term and
the reciprocal terms `1 / s + 1 / (s - 1)` arising from the logarithmic derivative of the
pole-clearing factor `s * (s - 1)` removing the simple poles of `completedRiemannZeta` at `0`
and `1`. Dropping the nonnegative sum over zeros (or keeping a single zero `ρ = β + i u` in the
critical strip) yields explicit upper bounds on `-Re (ζ'/ζ)(1 + η + i u)` in terms of
`η / (η ^ 2 + u ^ 2)` and `log (|u| + 3)`. Taking `|t| ≥ t₀ > 1` absorbs the pole term at `s = 1`
into `C * log |t|`, giving the two Davenport §13 bounds `TauCeti.neg_re_logDeriv_riemannZeta_le`.

## Main results

* `TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_mul_I_le`: strip upper bound for `0 < η ≤ 1`
  and all real `u`, retaining the explicit pole contribution `η / (η ^ 2 + u ^ 2)`.
* `TauCeti.neg_re_logDeriv_riemannZeta_le`: Davenport's bounds for `-Re (ζ'/ζ)(1 + η + 2 i t)` and
  `-Re (ζ'/ζ)(1 + η + i t)` for all `η > 0` and `|t| ≥ t₀ > 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13.
-/

public section

open Complex Filter LSeries Set TauCeti.LFunctions
open scoped LSeries.notation Topology

namespace TauCeti

private theorem re_one_div_le_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (1 / s).re ≤ 1 := by
  have hs0 : 0 < s.re := by linarith
  have hsq : s.re ^ 2 ≤ Complex.normSq s := by
    rw [Complex.normSq_apply, ← sq]
    nlinarith [sq_nonneg s.im]
  rw [one_div, Complex.inv_re]
  calc
    s.re / Complex.normSq s ≤ s.re / s.re ^ 2 :=
      div_le_div_of_nonneg_left hs0.le (sq_pos_of_pos hs0) hsq
    _ = 1 / s.re := by field_simp
    _ ≤ 1 := div_le_one_of_le₀ hs.le hs0.le

private theorem one_le_log_abs_add_three (u : ℝ) : 1 ≤ Real.log (|u| + 3) := by
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  exact hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg u]))

private theorem neg_re_logDeriv_riemannZeta_one_add_of_le_re_logDeriv {C₀ : ℝ}
    (hΓ : ∀ s : ℂ, s.re ∈ Icc (1 : ℝ) 2 → ‖logDeriv Gammaℝ s‖ ≤ C₀ * Real.log (|s.im| + 3))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (u r : ℝ)
    (hr : r ≤ (logDeriv zetaEntireCompletion (1 + η + u * I)).re) :
    -(logDeriv riemannZeta (1 + η + u * I)).re ≤
      -r + η / (η ^ 2 + u ^ 2) + (C₀ + 1) * Real.log (|u| + 3) := by
  set s : ℂ := 1 + η + u * I
  have hs_re : s.re = 1 + η := by simp [s]
  have hs_im : s.im = u := by simp [s]
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs1; linarith
  have hsne1 : s ≠ 1 := fun h ↦ by simp [h] at hs1
  have hsplit := congrArg Complex.re
    (logDeriv_zetaEntireCompletion_eq_add hs0 hsne1 (riemannZeta_ne_zero_of_one_le_re hs1.le))
  simp only [Complex.add_re] at hsplit
  have h1s1 : (1 / (s - 1)).re = η / (η ^ 2 + u ^ 2) := by
    have hs' : s - 1 = (η : ℂ) + u * I := by simp [s]; ring
    rw [hs', one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    ring
  have hΓs : (logDeriv Gammaℝ s).re ≤ C₀ * Real.log (|u| + 3) :=
    (Complex.re_le_norm _).trans ((hΓ s ⟨by linarith, by linarith⟩).trans_eq (by rw [hs_im]))
  linarith [re_one_div_le_one_of_one_lt_re hs1, one_le_log_abs_add_three u]

private theorem zetaEntireCompletion_zero_hypotheses {s : ℂ} (hs1 : 1 < s.re) :
    riemannZetaData.entireCompletion 0 ≠ 0 ∧
      riemannZetaData.entireCompletion s ≠ 0 ∧
      ∀ ρ : ℂ, riemannZetaData.entireCompletion ρ = 0 → ρ.re ≤ s.re := by
  refine ⟨by simp, ?_, fun ρ hρ ↦ ?_⟩
  · simpa only [riemannZetaData_entireCompletion] using
      zetaEntireCompletion_ne_zero_of_one_le_re hs1.le
  · rw [riemannZetaData_entireCompletion] at hρ
    exact (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le.trans hs1.le

private theorem neg_re_logDeriv_riemannZeta_one_add_zero_le {C₀ : ℝ}
    (hΓ : ∀ s : ℂ, s.re ∈ Icc (1 : ℝ) 2 → ‖logDeriv Gammaℝ s‖ ≤ C₀ * Real.log (|s.im| + 3))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (u β : ℝ) (hβ : riemannZeta (β + u * I) = 0) :
    -(logDeriv riemannZeta (1 + η + u * I)).re ≤
      -1 / (1 + η - β) + η / (η ^ 2 + u ^ 2) + (C₀ + 2) * Real.log (|u| + 3) := by
  set s : ℂ := 1 + η + u * I
  have hs1 : 1 < s.re := by simp [s, hη]
  obtain ⟨hξ0, hξ_ne, hξ_le⟩ := zetaEntireCompletion_zero_hypotheses hs1
  have hlog3 := one_le_log_abs_add_three u
  by_cases hβ0 : β ≤ 0
  · have hξ_nonneg : 0 ≤ (logDeriv zetaEntireCompletion s).re := by
      simpa only [riemannZetaData_entireCompletion] using
        riemannZetaData_hasFunctionalEquation.re_logDeriv_entireCompletion_nonneg_of_zero_ne_zero
          riemannZetaData_hasMeromorphicContinuation
          (by simpa only [riemannZetaData_entireCompletion] using orderLE_zetaEntireCompletion)
          hξ0 hξ_ne hξ_le
    have hbase := neg_re_logDeriv_riemannZeta_one_add_of_le_re_logDeriv hΓ hη hη1 u 0 hξ_nonneg
    have hinv : -1 ≤ -1 / (1 + η - β) := by
      rw [neg_div, neg_le_neg_iff]
      exact div_le_one_of_le₀ (by linarith) (by linarith)
    linarith
  · push Not at hβ0
    have hβ1 : β < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (by simpa using not_lt.mp h) hβ
    set ρ : ℂ := β + u * I
    have hρ0 : ρ ≠ 0 := fun h ↦ by
      have := congrArg Complex.re h; simp [ρ] at this; linarith
    have hρ1 : ρ ≠ 1 := fun h ↦ by
      have := congrArg Complex.re h; simp [ρ] at this; linarith
    have hΛρ : completedRiemannZeta ρ = 0 := by
      rw [riemannZeta_def_of_ne_zero hρ0, div_eq_zero_iff] at hβ
      exact hβ.resolve_right (Gammaℝ_ne_zero_of_re_pos (by simpa [ρ] using hβ0))
    have hξρ : riemannZetaData.entireCompletion ρ = 0 := by
      rw [riemannZetaData_entireCompletion, zetaEntireCompletion_eq_mul hρ0 hρ1, hΛρ, mul_zero]
    have hsingle :=
      riemannZetaData_hasFunctionalEquation.re_one_div_sub_le_re_logDeriv_entireCompletion
        riemannZetaData_hasMeromorphicContinuation
        (by simpa only [riemannZetaData_entireCompletion] using orderLE_zetaEntireCompletion)
        hξ0 hξ_ne hξ_le hξρ
    have hsρ : s - ρ = ((1 + η - β : ℝ) : ℂ) := by apply Complex.ext <;> simp [s, ρ]
    rw [riemannZetaData_entireCompletion, hsρ, one_div, ← ofReal_inv, ofReal_re,
      ← one_div] at hsingle
    have hbound := neg_re_logDeriv_riemannZeta_one_add_of_le_re_logDeriv hΓ hη hη1 u
      (1 / (1 + η - β)) hsingle
    rw [neg_div]
    linarith

/-- On the vertical strip `1 < Re s ≤ 2` (`s = 1 + η + i u`), `-Re (ζ'/ζ)(1 + η + i u)` is
bounded above by `η / (η ^ 2 + u ^ 2) + C * log (|u| + 3)`, and if `ζ(β + i u) = 0` then it also
retains the single-zero term `-1 / (1 + η - β)`. -/
theorem exists_neg_re_logDeriv_riemannZeta_one_add_mul_I_le :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤
        η / (η ^ 2 + u ^ 2) + C * Real.log (|u| + 3) ∧
      ∀ β : ℝ, riemannZeta (β + u * I) = 0 →
        -(logDeriv riemannZeta (1 + η + u * I)).re ≤
          -1 / (1 + η - β) + η / (η ^ 2 + u ^ 2) + C * Real.log (|u| + 3) := by
  obtain ⟨C₀, hC₀, hΓ⟩ := Complex.exists_norm_logDeriv_Gammaℝ_le_log (a := 1) (b := 2) zero_lt_one
  refine ⟨C₀ + 2, by positivity, fun η hη hη1 u ↦ ?_⟩
  set s : ℂ := 1 + η + u * I
  have hs1 : 1 < s.re := by simp [s, hη]
  obtain ⟨hξ0, hξ_ne, hξ_le⟩ := zetaEntireCompletion_zero_hypotheses hs1
  have hξ_nonneg : 0 ≤ (logDeriv zetaEntireCompletion s).re := by
    simpa only [riemannZetaData_entireCompletion] using
      riemannZetaData_hasFunctionalEquation.re_logDeriv_entireCompletion_nonneg_of_zero_ne_zero
        riemannZetaData_hasMeromorphicContinuation
        (by simpa only [riemannZetaData_entireCompletion] using orderLE_zetaEntireCompletion)
        hξ0 hξ_ne hξ_le
  have hbase := neg_re_logDeriv_riemannZeta_one_add_of_le_re_logDeriv hΓ hη hη1 u 0 hξ_nonneg
  have hlog0 : 0 ≤ Real.log (|u| + 3) := Real.log_nonneg (by linarith [abs_nonneg u])
  refine ⟨by linarith [mul_le_mul_of_nonneg_right (by linarith : C₀ + 1 ≤ C₀ + 2) hlog0],
    fun β hβ ↦ neg_re_logDeriv_riemannZeta_one_add_zero_le hΓ hη hη1 u β hβ⟩

private theorem pole_add_mul_log_le {t₀ C₁ η u t : ℝ} (ht₀ : 1 < t₀) (hC₁ : 0 < C₁)
    (hη1 : η ≤ 1) (ht : t₀ ≤ |t|) (hu1 : 1 ≤ |u|) (hu2 : |u| ≤ 2 * |t|) :
    η / (η ^ 2 + u ^ 2) + C₁ * Real.log (|u| + 3) ≤
      (1 / Real.log t₀ + C₁ * (Real.log 5 / Real.log t₀ + 1)) * Real.log |t| := by
  have hlogt₀ : 0 < Real.log t₀ := Real.log_pos ht₀
  have htpos : 1 < |t| := ht₀.trans_le ht
  have h1_le : 1 ≤ (1 / Real.log t₀) * Real.log |t| := by
    have hmul := mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ht)
      (one_div_nonneg.mpr hlogt₀.le)
    rwa [one_div_mul_cancel hlogt₀.ne'] at hmul
  have hpole : η / (η ^ 2 + u ^ 2) ≤ 1 := by
    have hu2' : 1 ≤ u ^ 2 := by
      simpa only [one_pow, sq_abs] using (sq_le_sq₀ zero_le_one (abs_nonneg u)).mpr hu1
    calc
      η / (η ^ 2 + u ^ 2) ≤ 1 / (0 + 1) :=
        div_le_div₀ (by positivity) hη1 (by positivity) (by nlinarith [sq_nonneg η])
      _ = 1 := by norm_num
  have hlog_u : Real.log (|u| + 3) ≤ (Real.log 5 / Real.log t₀ + 1) * Real.log |t| := by
    have hlog5 : Real.log (5 * |t|) = Real.log 5 + Real.log |t| :=
      Real.log_mul (by norm_num) (by positivity)
    have hterm5 : Real.log 5 ≤ (Real.log 5 / Real.log t₀) * Real.log |t| := by
      calc
        Real.log 5 = Real.log 5 * 1 := (mul_one _).symm
        _ ≤ Real.log 5 * ((1 / Real.log t₀) * Real.log |t|) :=
            mul_le_mul_of_nonneg_left h1_le (Real.log_nonneg (by norm_num))
        _ = (Real.log 5 / Real.log t₀) * Real.log |t| := by ring
    calc
      Real.log (|u| + 3) ≤ Real.log (5 * |t|) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 5 + Real.log |t| := hlog5
      _ ≤ (Real.log 5 / Real.log t₀ + 1) * Real.log |t| := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog_u hC₁.le
  calc
    η / (η ^ 2 + u ^ 2) + C₁ * Real.log (|u| + 3)
        ≤ (1 / Real.log t₀) * Real.log |t| +
            C₁ * ((Real.log 5 / Real.log t₀ + 1) * Real.log |t|) := by
          linarith [hpole]
    _ = (1 / Real.log t₀ + C₁ * (Real.log 5 / Real.log t₀ + 1)) * Real.log |t| := by ring

private theorem neg_re_logDeriv_riemannZeta_le_of_le_one {t₀ C₁ : ℝ} (ht₀ : 1 < t₀) (hC₁ : 0 < C₁)
    (hstrip : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤
        η / (η ^ 2 + u ^ 2) + C₁ * Real.log (|u| + 3) ∧
      ∀ β : ℝ, riemannZeta (β + u * I) = 0 →
        -(logDeriv riemannZeta (1 + η + u * I)).re ≤
          -1 / (1 + η - β) + η / (η ^ 2 + u ^ 2) + C₁ * Real.log (|u| + 3))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {t : ℝ} (ht : t₀ ≤ |t|) :
    -(logDeriv riemannZeta (1 + η + 2 * t * I)).re ≤
        (1 / Real.log t₀ + C₁ * (Real.log 5 / Real.log t₀ + 1)) * Real.log |t| ∧
      ∀ β : ℝ, riemannZeta (β + t * I) = 0 →
        -(logDeriv riemannZeta (1 + η + t * I)).re ≤
          -1 / (1 + η - β) +
            (1 / Real.log t₀ + C₁ * (Real.log 5 / Real.log t₀ + 1)) * Real.log |t| := by
  have htpos : 1 < |t| := ht₀.trans_le ht
  obtain ⟨h2t, -⟩ := hstrip η hη hη1 (2 * t)
  obtain ⟨-, htβ⟩ := hstrip η hη hη1 t
  have h2t_mul : (1 : ℂ) + η + 2 * t * I = 1 + η + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
  refine ⟨?_, fun β hβ ↦ ?_⟩
  · rw [h2t_mul]
    exact h2t.trans (pole_add_mul_log_le ht₀ hC₁ hη1 ht
      (by rw [abs_mul, abs_two]; linarith) (by rw [abs_mul, abs_two]))
  · exact (htβ β hβ).trans (by
      linarith [pole_add_mul_log_le ht₀ hC₁ hη1 ht htpos.le (by linarith [abs_nonneg t])])

private theorem neg_re_logDeriv_riemannZeta_le_of_one_lt {η : ℝ} (hη : 1 < η) (t : ℝ) :
    -(logDeriv riemannZeta (1 + η + 2 * t * I)).re ≤ max 0 (-(logDeriv riemannZeta 2).re) + 1 ∧
      ∀ β : ℝ, riemannZeta (β + t * I) = 0 →
        -(logDeriv riemannZeta (1 + η + t * I)).re ≤
          -1 / (1 + η - β) + (max 0 (-(logDeriv riemannZeta 2).re) + 1) := by
  set Z2 : ℝ := max 0 (-(logDeriv riemannZeta 2).re) + 1
  have hre2 (u : ℝ) : 2 ≤ ((1 : ℂ) + η + u * I).re := by
    simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    linarith
  have hnorm (u : ℝ) :
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤ -(logDeriv riemannZeta 2).re := by
    rw [← Complex.neg_re]
    exact (Complex.re_le_norm _).trans
      (norm_neg (logDeriv riemannZeta (1 + η + u * I)) ▸
        norm_logDeriv_riemannZeta_le_of_two_le_re (hre2 u))
  have hZ2 : -(logDeriv riemannZeta 2).re + 1 ≤ Z2 := by
    dsimp [Z2]; linarith [le_max_right 0 (-(logDeriv riemannZeta 2).re)]
  refine ⟨?_, fun β hβ ↦ ?_⟩
  · have hz : -(logDeriv riemannZeta (1 + η + 2 * t * I)).re ≤ -(logDeriv riemannZeta 2).re := by
      simpa [mul_assoc] using hnorm (2 * t)
    linarith
  · have hβ1 : β < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (by simpa using not_lt.mp h) hβ
    have hinv : -1 ≤ -1 / (1 + η - β) := by
      rw [neg_div, neg_le_neg_iff]
      exact div_le_one_of_le₀ (by linarith) (by linarith)
    linarith [hnorm t]

/-- For every `t₀ > 1` there is `C` such that, for `η > 0` and `|t| ≥ t₀`,
`-Re (ζ'/ζ)(1 + η + 2it) ≤ C log |t|`, and `-Re (ζ'/ζ)(1 + η + it) ≤ -1/(1 + η - β) + C log |t|`
whenever `β + it` is a zero of `ζ` (Davenport §13). -/
theorem neg_re_logDeriv_riemannZeta_le (t₀ : ℝ) (ht₀ : 1 < t₀) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ t : ℝ, t₀ ≤ |t| →
      -(logDeriv riemannZeta (1 + η + 2 * t * I)).re ≤ C * Real.log |t| ∧
        ∀ β : ℝ, riemannZeta (β + t * I) = 0 →
          -(logDeriv riemannZeta (1 + η + t * I)).re ≤ -1 / (1 + η - β) + C * Real.log |t| := by
  obtain ⟨C₁, hC₁, hstrip⟩ := exists_neg_re_logDeriv_riemannZeta_one_add_mul_I_le
  have hlogt₀ : 0 < Real.log t₀ := Real.log_pos ht₀
  set Z2 : ℝ := max 0 (-(logDeriv riemannZeta 2).re) + 1
  set L5 : ℝ := Real.log 5 / Real.log t₀ + 1
  set C : ℝ := max (Z2 / Real.log t₀) (1 / Real.log t₀ + C₁ * L5)
  refine ⟨C, fun η hη t ht ↦ ?_⟩
  have hlogt_pos : 0 < Real.log |t| := Real.log_pos (ht₀.trans_le ht)
  have hlog_le : Real.log t₀ ≤ Real.log |t| := Real.log_le_log (by positivity) ht
  by_cases hη1 : η ≤ 1
  · obtain ⟨h2t, htβ⟩ := neg_re_logDeriv_riemannZeta_le_of_le_one ht₀ hC₁ hstrip hη hη1 ht
    have hC := mul_le_mul_of_nonneg_right
      (le_max_right (Z2 / Real.log t₀) (1 / Real.log t₀ + C₁ * L5)) hlogt_pos.le
    exact ⟨h2t.trans hC, fun β hβ ↦ (htβ β hβ).trans (by linarith)⟩
  · obtain ⟨h2t, htβ⟩ := neg_re_logDeriv_riemannZeta_le_of_one_lt (not_le.mp hη1) t
    have h1_le : 1 ≤ (1 / Real.log t₀) * Real.log |t| := by
      have hmul := mul_le_mul_of_nonneg_left hlog_le (one_div_nonneg.mpr hlogt₀.le)
      rwa [one_div_mul_cancel hlogt₀.ne'] at hmul
    have hZ2_le : Z2 ≤ C * Real.log |t| := by
      calc
        Z2 = Z2 * 1 := (mul_one Z2).symm
        _ ≤ Z2 * ((1 / Real.log t₀) * Real.log |t|) :=
            mul_le_mul_of_nonneg_left h1_le (by positivity)
        _ = (Z2 / Real.log t₀) * Real.log |t| := by ring
        _ ≤ C * Real.log |t| := mul_le_mul_of_nonneg_right
            (le_max_left (Z2 / Real.log t₀) (1 / Real.log t₀ + C₁ * L5)) hlogt_pos.le
    exact ⟨h2t.trans hZ2_le, fun β hβ ↦ (htβ β hβ).trans (by linarith)⟩

end TauCeti
