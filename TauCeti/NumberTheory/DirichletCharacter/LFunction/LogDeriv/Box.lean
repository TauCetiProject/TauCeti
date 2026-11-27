/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.DirichletEulerLog

/-!
# Logarithmic derivatives in zero-free boxes

For a nonprincipal Dirichlet character modulo `q`, a box free of zeros up to height `Q ≥ q`
gives an `O(log Q)` bound for `L′/L` at half the height and a fixed distance from its left edge.
The constant is uniform in the character and does not require primitivity. This is the bound
needed to shift a truncated contour in smoothed prime sums.

The zero-free disc argument uses the logarithmic-derivative form of Borel–Carathéodory, as in
Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 6.
-/

public section

open Complex Metric Real

namespace TauCeti

-- The Euler product at the center gives a lower bound independent of the level and height.
private theorem norm_LFunction_le_mul_norm_box_center {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {Q : ℝ} (hq : (q : ℝ) ≤ Q)
    {c z : ℂ} (hc : c.re = 3 / 2) (him : |c.im| ≤ Q / 2) (hz : ‖z - c‖ < 1) :
    ‖χ.LFunction z‖ ≤ (4 * Q ^ 2 * rexp |(riemannZeta (3 / 2 : ℝ)).re|) * ‖χ.LFunction c‖ := by
  have hlevel : (3 : ℝ) ≤ q := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have hQ := hlevel.trans hq
  have hzre : 1 / 2 < z.re := by
    have h := (abs_re_le_norm (z - c)).trans_lt hz
    rw [sub_re, hc] at h
    linarith [(abs_lt.mp h).1]
  have hcn : ‖c‖ ≤ 3 / 2 + Q / 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im c
    rw [hc, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
    linarith
  have hzn : ‖z‖ ≤ 2 * Q := by linarith [norm_le_norm_sub_add z c]
  have hgrowth : ‖χ.LFunction z‖ ≤ 4 * Q ^ 2 := calc
    ‖χ.LFunction z‖ ≤ (q : ℝ) * ‖z‖ / z.re :=
      χ.norm_LFunction_le_level_mul_norm_div_re hχ (by linarith)
    _ ≤ Q * (2 * Q) / (1 / 2) := by gcongr
    _ = 4 * Q ^ 2 := by ring
  have hlower : rexp (-|(riemannZeta (3 / 2 : ℝ)).re|) ≤ ‖χ.LFunction c‖ := by
    refine (Real.exp_le_exp.mpr (neg_le_neg (le_abs_self _))).trans ?_
    simpa only [hc] using χ.exp_neg_re_riemannZeta_le_norm_LFunction
      (s := c) (by rw [hc]; norm_num)
  have hmul := mul_le_mul_of_nonneg_left hlower (Real.exp_pos |(riemannZeta (3 / 2 : ℝ)).re|).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
  rw [mul_assoc]
  exact hgrowth.trans (le_mul_of_one_le_right (by positivity) hmul)

private theorem norm_logDeriv_LFunction_le_in_left_half_box {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {Q σ δ : ℝ} (hq : (q : ℝ) ≤ Q)
    (hσ : 1 / 2 ≤ σ) (hδ : 0 < δ)
    (hzero : ∀ z : ℂ, σ < z.re → |z.im| ≤ Q → χ.LFunction z ≠ 0)
    {s : ℂ} (hs : σ + δ ≤ s.re) (hsre : s.re ≤ 3 / 2) (hsim : |s.im| ≤ Q / 2) :
    ‖logDeriv χ.LFunction s‖ ≤
      8 / δ ^ 2 * Real.log (4 * Q ^ 2 * rexp |(riemannZeta (3 / 2 : ℝ)).re|) := by
  let c : ℂ := (3 / 2 : ℝ) + s.im * I
  let r : ℝ := 3 / 2 - σ
  have hlevel : (3 : ℝ) ≤ q := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have hQ := hlevel.trans hq
  have hc : c.re = 3 / 2 ∧ c.im = s.im := by simp [c]
  have hr : r ≤ 1 := by dsimp [r]; linarith
  have hdist : ‖s - c‖ = 3 / 2 - s.re := by
    have heq : s - c = ((s.re - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc.1, hc.2]
    rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hsre), neg_sub]
  have hgap : δ ≤ r - ‖s - c‖ := by rw [hdist]; dsimp [r]; linarith
  have hsr : ‖s - c‖ < r := by linarith
  have hball (z : ℂ) (hz : z ∈ ball c r) : χ.LFunction z ≠ 0 := by
    have hz' := mem_ball_iff_norm.mp hz
    have h₁ := (abs_re_le_norm (z - c)).trans_lt hz'
    have h₂ := (abs_im_le_norm (z - c)).trans_lt (hz'.trans_le hr)
    rw [sub_re, hc.1] at h₁
    rw [sub_im, hc.2] at h₂
    have him := abs_add_le (z.im - s.im) s.im
    rw [sub_add_cancel] at him
    exact hzero z (by dsimp [r] at h₁; linarith [(abs_lt.mp h₁).1]) (by linarith)
  refine (norm_logDeriv_le_of_forall_mem_ball_norm_le_mul
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn hball
    (fun _ hz ↦ norm_LFunction_le_mul_norm_box_center χ hχ hq hc.1 (hc.2 ▸ hsim)
      ((mem_ball_iff_norm.mp hz).trans_le hr)) hsr).trans ?_
  have hlog : 0 ≤ Real.log (4 * Q ^ 2 * rexp |(riemannZeta (3 / 2 : ℝ)).re|) := by
    apply Real.log_nonneg
    refine (show (1 : ℝ) ≤ 4 * Q ^ 2 by nlinarith).trans ?_
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (abs_nonneg _))
  apply mul_le_mul_of_nonneg_right _ hlog
  exact div_le_div₀ (by positivity) (by linarith) (by positivity)
    (pow_le_pow_left₀ hδ.le hgap 2)

/-- Uniform logarithmic-derivative bound in the interior of a zero-free box. If a nonprincipal
Dirichlet `L`-function is zero-free on `Re z > σ`, `|Im z| ≤ Q`, with `σ ≥ 1/2` and
`Q ≥ q`, then for `δ > 0` its logarithmic derivative on `Re s ≥ σ + δ`, `|Im s| ≤ Q/2` has norm
at most `C * (1 + δ⁻²) * log Q`, where `C` is absolute. -/
theorem exists_norm_logDeriv_LFunction_le_of_zero_free_box :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {Q σ δ : ℝ}, (q : ℝ) ≤ Q → 1 / 2 ≤ σ → 0 < δ →
        (∀ z : ℂ, σ < z.re → |z.im| ≤ Q → χ.LFunction z ≠ 0) →
        ∀ {s : ℂ}, σ + δ ≤ s.re → |s.im| ≤ Q / 2 →
          ‖logDeriv χ.LFunction s‖ ≤ C * (1 + 1 / δ ^ 2) * Real.log Q := by
  let B := |(riemannZeta (3 / 2 : ℝ)).re|
  let D := |(logDeriv riemannZeta (3 / 2 : ℝ)).re|
  let A := 8 * (4 + B / Real.log 2)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A, B]; positivity
  refine ⟨max A (D / Real.log 2), hA.trans_le (le_max_left ..),
    fun {q} _ χ hχ {Q σ δ} hq hσ hδ hzero {s} hs hsim ↦ ?_⟩
  have hlevel : (3 : ℝ) ≤ q := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have htwo : 2 ≤ Q := (by norm_num : (2 : ℝ) ≤ 3).trans (hlevel.trans hq)
  have hlog : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) htwo
  have hδ' : 0 ≤ 1 / δ ^ 2 := by positivity
  rcases le_total s.re (3 / 2) with hsre | hsre
  · have hM : Real.log (4 * Q ^ 2 * rexp B) ≤ (4 + B / Real.log 2) * Real.log Q := by
      have hB : 0 ≤ B / Real.log 2 := by dsimp [B]; positivity
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_mul (by norm_num)
        (by positivity), Real.log_pow, Real.log_exp, show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.log_pow, add_mul]
      have hB' : B ≤ B / Real.log 2 * Real.log Q := by
        simpa [div_mul_cancel₀ _ hlog₂.ne'] using mul_le_mul_of_nonneg_left hlog hB
      linarith
    calc
      ‖logDeriv χ.LFunction s‖ ≤ 8 / δ ^ 2 * Real.log (4 * Q ^ 2 * rexp B) :=
        norm_logDeriv_LFunction_le_in_left_half_box χ hχ hq hσ hδ hzero hs hsre hsim
      _ ≤ 8 / δ ^ 2 * ((4 + B / Real.log 2) * Real.log Q) := by gcongr
      _ = A * (1 / δ ^ 2) * Real.log Q := by dsimp [A]; ring
      _ ≤ max A (D / Real.log 2) * (1 + 1 / δ ^ 2) * Real.log Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (le_max_left ..) (by linarith) hδ' (hA.le.trans (le_max_left ..)))
          (hlog₂.le.trans hlog)
  · have hD : 0 ≤ D / Real.log 2 := by dsimp [D]; positivity
    calc
      ‖logDeriv χ.LFunction s‖ ≤ -(logDeriv riemannZeta (3 / 2 : ℝ)).re :=
        χ.norm_logDeriv_LFunction_le_of_le_re (by norm_num) hsre
      _ ≤ D := neg_le_abs _
      _ = D / Real.log 2 * 1 * Real.log 2 := by rw [mul_one, div_mul_cancel₀ _ hlog₂.ne']
      _ ≤ max A (D / Real.log 2) * (1 + 1 / δ ^ 2) * Real.log Q :=
        mul_le_mul (mul_le_mul (le_max_right ..) (by linarith) zero_le_one
          (hD.trans (le_max_right ..))) hlog hlog₂.le (by positivity)

end TauCeti
