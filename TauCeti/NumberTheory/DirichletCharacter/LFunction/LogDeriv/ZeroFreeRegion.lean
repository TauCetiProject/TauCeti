/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.GrowthNearOne
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A zero-free region with a bound for the logarithmic derivative

Let `χ` be a Dirichlet character modulo `N ≥ 1`, primitive or not, and `E_χ`
(`DirichletCharacter.entireLFunction`) its L-function with the pole of the principal character
removed. For a logarithmic scale `l`, `E_χ` has no zero in the region `Re s ≥ 1 - l⁻²⁵`,
`‖s‖ ≤ e^l`, and its logarithmic derivative is at most `2 l²⁵` there, in two forms:
uniformly in `l ≥ 10¹⁰` and `N ≤ e^l`, assuming `‖f_χ‖ ≥ 1 / l` within `1 / l` of `1` when `χ²`
is principal; or for one fixed `χ` and all `l` large in terms of `χ`.

The proof bounds `f_χ` (`DirichletCharacter.regularizedLFunction`) from below just to the right of
`Re s = 1` and carries the bound across the line with the derivative bound of
`DirichletCharacter.norm_deriv_regularizedLFunction_le`; there is no Hadamard product and no
exceptional zero. On `Re s ≥ 1 + η`, the inequality `‖L(σ, χ₀)³ L(σ + it, χ)⁴ L(σ + 2it, χ²)‖ ≥ 1`
(`DirichletCharacter.norm_LSeries_product_ge_one`), with `‖L(Re s, χ₀)‖ ≤ 2 / η`,
`‖L(s, χ)‖ ≤ 2 l ‖f_χ(s)‖` and the growth bound for `χ²`, gives `η³ ≤ 256 l⁷ ‖f_χ(s)‖⁴`, unless
`χ²` is principal and `s` is within `1 / l` of `1`. Uniformly in `N ≤ e^l` this needs, for real
characters, a lower bound for `‖f_χ‖` near `1`; for one character at a time that bound holds for all
large `l` because `f_χ(1) ≠ 0`.

## Main results

* `DirichletCharacter.eventually_le_norm_regularizedLFunction`: `‖f_χ(z)‖ ≥ r` for
  `‖z - 1‖ ≤ r` and all small `r > 0`.
* `DirichletCharacter.entireLFunction_ne_zero_and_norm_logDeriv_le`: the zero-free region and the
  bound for the logarithmic derivative, uniformly in `N ≤ e^l` under the lower bound near `1`.
* `DirichletCharacter.eventually_entireLFunction_ne_zero_and_norm_logDeriv_le`: the same for one
  character and all large `l`.
* `DirichletCharacter.exists_entireLFunction_ne_zero_and_norm_logDeriv_le_log_pow`: reformulation
  on a region whose width depends only on `|Im s|`, including the whole region to its right.

The exponent `25` and the threshold `10¹⁰` are what the numerical steps give; any fixed exponent
would do for the applications. The classical region `Re s ≥ 1 - c / log (N (|Im s| + 3))` is
`TauCeti.LFunctions.dirichletLFunction_zeroFreeRegion`; it does not bound the logarithmic
derivative.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean`
(`New.eventually_le_norm_regularL`, `New.pow_three_le_mul_norm_regularL_pow`,
`New.div_pow_le_norm_regularL`, `New.norm_logDeriv_regularL_le`, `New.norm_logDeriv_entireL_le`,
`New.eventually_norm_logDeriv_entireL_le`).

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge Studies in
  Advanced Mathematics 97 (2007), Chapter 11.
-/

public section

open Complex Real Filter Topology Metric

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}

/-- For all small `r`, `‖f_χ(z)‖ ≥ r` whenever `‖z - 1‖ ≤ r`. -/
theorem eventually_le_norm_regularizedLFunction :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ z : ℂ, ‖z - 1‖ ≤ r → r ≤ ‖χ.regularizedLFunction z‖ := by
  -- `f_χ(1) ≠ 0` and `f_χ` is continuous at `1`.
  have h_pos : 0 < ‖χ.regularizedLFunction 1‖ :=
    norm_pos_iff.2 (χ.regularizedLFunction_ne_zero_of_one_le_re (by simp))
  have h_near : ∀ᶠ z : ℂ in 𝓝 1, ‖χ.regularizedLFunction 1‖ / 2 ≤ ‖χ.regularizedLFunction z‖ :=
    (χ.differentiableAt_regularizedLFunction (.inl one_ne_zero)).continuousAt.norm
      |>.eventually_const_le (half_lt_self h_pos)
  filter_upwards [eventually_le_nhds (half_pos h_pos), eventually_closedBall_subset h_near]
    with r hr h_ball z hz using hr.trans (h_ball (mem_closedBall_iff_norm.2 hz))

/-- The lower bound from the `3-4-1` inequality: for `l ≥ 10¹⁰`, `N ≤ e^l` and `0 < η ≤ 1`,
`η³ ≤ 256 l⁷ ‖f_χ(s)‖⁴` on `Re s ≥ 1 + η`, `‖s‖ ≤ 3 e^l / 2`, if `χ²` is not principal or
`‖s - 1‖ ≥ 1 / l`. -/
theorem pow_three_le_mul_norm_regularizedLFunction_pow (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    {η : ℝ} (hη : 0 < η) (hη_le : η ≤ 1) (h_far : χ ^ 2 = 1 → 1 / l ≤ ‖s - 1‖)
    (h_re : 1 + η ≤ s.re) (h_norm : ‖s‖ ≤ 3 / 2 * rexp l) :
    η ^ 3 ≤ 256 * l ^ 7 * ‖χ.regularizedLFunction s‖ ^ 4 := by
  have hl_one : 1 ≤ l := by linarith
  -- The three points are `Re s`, `s` and `s₂ = Re s + 2 i Im s`.
  let s₂ : ℂ := s + s.im * I
  have re_s₂ : s₂.re = s.re := by simp [s₂]
  have norm_s₂ : ‖s₂‖ ≤ 3 * rexp l := by
    have h_im : ‖s.im * I‖ ≤ ‖s‖ := by simpa using abs_im_le_norm s
    linarith [norm_add_le s (s.im * I)]
  have dist_s₂ : ‖s - 1‖ ≤ ‖s₂ - 1‖ := by
    have h_sq : ‖s₂ - 1‖ ^ 2 = ‖s - 1‖ ^ 2 + 3 * s.im ^ 2 := by
      have im_s₂ : s₂.im = 2 * s.im := by simp [s₂, two_mul]
      simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, re_s₂, im_s₂, one_im]
      ring
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith [sq_nonneg s.im])
  have product : 1 ≤ ‖LSeries (fun n ↦ (1 : DirichletCharacter ℂ N) n) s.re‖ ^ 3 *
      ‖LSeries (fun n ↦ χ n) s‖ ^ 4 * ‖LSeries (fun n ↦ (χ ^ 2) n) s₂‖ := by
    have at_re : (1 : ℂ) + (s.re - 1 : ℝ) = s.re := by simp
    have at_s : s.re + I * s.im = s := by rw [mul_comm, re_add_im]
    have at_s₂ : s.re + 2 * I * s.im = s₂ := by linear_combination at_s
    simpa only [at_re, at_s, at_s₂, norm_mul, norm_pow, ge_iff_le] using
      χ.norm_LSeries_product_ge_one (by linarith : 0 < s.re - 1) s.im
  have one_le : ‖LSeries (fun n ↦ (1 : DirichletCharacter ℂ N) n) s.re‖ ≤ 2 / η := calc
    _ ≤ 1 + 1 / η := norm_LSeries_le_one_add 1 (one_div_pos.2 hη) (by simpa using h_re)
    _ ≤ 1 / η + 1 / η := by linarith [one_le_one_div hη hη_le]
    _ = 2 / η := by ring
  have char_le : ‖LSeries (fun n ↦ χ n) s‖ ≤ 2 * l * ‖χ.regularizedLFunction s‖ :=
    χ.norm_LSeries_le_mul_norm_regularizedLFunction (by linarith) hl_one
      fun hχ ↦ h_far (by simp [hχ])
  have sq_le : ‖LSeries (fun n ↦ (χ ^ 2) n) s₂‖ ≤ 2 * l * l ^ 2 := by
    have h_far₂ : χ ^ 2 = 1 → 1 / l ≤ ‖s₂ - 1‖ := fun hχ ↦ (h_far hχ).trans dist_s₂
    have re_s₂_ge : 1 - 1 / l ≤ s₂.re := by linarith [one_div_pos.2 (one_pos.trans_le hl_one)]
    grw [(χ ^ 2).norm_LSeries_le_mul_norm_regularizedLFunction (by linarith) hl_one h_far₂,
      (χ ^ 2).norm_regularizedLFunction_le_sq hl hN re_s₂_ge norm_s₂]
  calc η ^ 3 ≤ η ^ 3 * ((2 / η) ^ 3 * (2 * l * ‖χ.regularizedLFunction s‖) ^ 4 *
        (2 * l * l ^ 2)) := by
        grw [← one_le, ← char_le, ← sq_le, ← product, mul_one]
    _ = 256 * l ^ 7 * ‖χ.regularizedLFunction s‖ ^ 4 := by field

/-- For `l ≥ 10¹⁰` and `N ≤ e^l`, and, if `χ²` is principal, `‖f_χ‖ ≥ 1 / l` within `1 / l` of
`1`: `‖f_χ(s)‖ ≥ 12 / l²²` on `Re s ≥ 1 + l⁻²⁵`, `‖s‖ ≤ 3 e^l / 2`. -/
theorem div_pow_le_norm_regularizedLFunction (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖χ.regularizedLFunction z‖)
    (h_re : 1 + 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ 3 / 2 * rexp l) :
    12 / l ^ 22 ≤ ‖χ.regularizedLFunction s‖ := by
  have hl_one : 1 ≤ l := by linarith
  by_cases! h_far : χ ^ 2 = 1 → 1 / l ≤ ‖s - 1‖
  · -- If `χ²` is not principal or `s` is not near `1`, the `3-4-1` bound with `η = l⁻²⁵` applies.
    have hη_le : 1 / l ^ 25 ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ hl_one) (by positivity)
    have h_const : 256 * 12 ^ 4 ≤ l ^ 6 := by linarith [le_self_pow₀ hl_one (by norm_num : 6 ≠ 0)]
    have h_mul : 256 * l ^ 7 * (12 / l ^ 22) ^ 4 ≤ 256 * l ^ 7 * ‖χ.regularizedLFunction s‖ ^ 4 :=
      calc 256 * l ^ 7 * (12 / l ^ 22) ^ 4 = 256 * 12 ^ 4 / l ^ 81 := by field
        _ ≤ l ^ 6 / l ^ 81 := by gcongr
        _ = (1 / l ^ 25) ^ 3 := by field
        _ ≤ _ := χ.pow_three_le_mul_norm_regularizedLFunction_pow hl hN (by positivity) hη_le
          h_far h_re h_norm
    exact le_of_pow_le_pow_left₀ four_ne_zero (norm_nonneg _)
      (le_of_mul_le_mul_left h_mul (by positivity))
  · obtain ⟨hχ, h_close⟩ : χ ^ 2 = 1 ∧ ‖s - 1‖ < 1 / l := h_far
    calc 12 / l ^ 22 ≤ l / l ^ 2 := by gcongr <;> linarith
      _ = 1 / l := by field
      _ ≤ ‖χ.regularizedLFunction s‖ := h_near hχ s h_close.le

/-- Under the hypotheses of `div_pow_le_norm_regularizedLFunction`, `f_χ(s) ≠ 0` and
`‖f_χ'(s) / f_χ(s)‖ ≤ l²⁵` on `Re s ≥ 1 - l⁻²⁵`, `‖s‖ ≤ e^l`. -/
theorem regularizedLFunction_ne_zero_and_norm_logDeriv_le (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖χ.regularizedLFunction z‖)
    (h_re : 1 - 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ rexp l) :
    χ.regularizedLFunction s ≠ 0 ∧ ‖logDeriv χ.regularizedLFunction s‖ ≤ l ^ 25 := by
  have exp_ge : l + 1 ≤ rexp l := add_one_le_exp l
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  let η : ℝ := 1 / l ^ 25
  have hη_pos : 0 < η := by positivity
  have hη_le : η ≤ 1 / l / 6 := calc
    1 / l ^ 25 ≤ 1 / l ^ 2 := by gcongr <;> linarith
    _ = 1 / l * (1 / l) := by ring
    _ ≤ 1 / l / 6 := by grw [div_eq_mul_one_div (1 / l) 6, ← inv_le]
  have bounds (z : ℂ) (hz : z ∈ closedBall s (2 * η)) :
      1 - 1 / l / 2 ≤ z.re ∧ ‖z‖ ≤ 2 * rexp l := by
    rw [mem_closedBall_iff_norm] at hz
    have h_dist : |z.re - s.re| ≤ ‖z - s‖ := by simpa using abs_re_le_norm (z - s)
    exact ⟨by linarith [(abs_le.1 h_dist).1], by linarith [norm_le_norm_sub_add z s]⟩
  have deriv_le (z : ℂ) (hz : z ∈ closedBall s (2 * η)) :
      ‖deriv χ.regularizedLFunction z‖ ≤ 2 * l ^ 3 :=
    χ.norm_deriv_regularizedLFunction_le hl hN (bounds z hz).1 (bounds z hz).2
  have hs_mem : s ∈ closedBall s (2 * η) := mem_closedBall_self (by positivity)
  let v : ℂ := s + (2 * η : ℝ)
  have dist_v : ‖v - s‖ = 2 * η := by simp [v, hη_pos.le]
  have re_v : v.re = s.re + 2 * η := by simp [v]
  have change_le : ‖χ.regularizedLFunction v - χ.regularizedLFunction s‖ ≤ 4 / l ^ 22 := calc
    _ ≤ 2 * l ^ 3 * ‖v - s‖ :=
      (convex_closedBall s (2 * η)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz ↦ χ.differentiableAt_regularizedLFunction
          (.inl (ne_zero_of_re_pos (by linarith [(bounds z hz).1]))))
        deriv_le hs_mem (mem_closedBall_iff_norm.2 dist_v.le)
    _ = 4 / l ^ 22 := by rw [dist_v]; field
  have large_v : 12 / l ^ 22 ≤ ‖χ.regularizedLFunction v‖ :=
    χ.div_pow_le_norm_regularizedLFunction hl hN h_near (by linarith)
      (by linarith [norm_le_norm_sub_add v s])
  have large_s : 8 / l ^ 22 ≤ ‖χ.regularizedLFunction s‖ := calc
    _ = 12 / l ^ 22 - 4 / l ^ 22 := by ring
    _ ≤ ‖χ.regularizedLFunction s‖ := by
      linarith [norm_sub_norm_le (χ.regularizedLFunction v) (χ.regularizedLFunction s)]
  refine ⟨norm_pos_iff.1 (lt_of_lt_of_le (by positivity) large_s), ?_⟩
  calc ‖logDeriv χ.regularizedLFunction s‖ ≤ 2 * l ^ 3 / (8 / l ^ 22) := by
        grw [logDeriv_apply, norm_div, deriv_le s hs_mem, ← large_s]
    _ = l ^ 25 / 4 := by field
    _ ≤ l ^ 25 := div_le_self (by positivity) (by norm_num)

/-- *Zero-free region*, uniform form: let `l ≥ 10¹⁰` and `N ≤ e^l`, and, if `χ²` is principal,
suppose `‖f_χ(z)‖ ≥ 1 / l` whenever `‖z - 1‖ ≤ 1 / l`. Then for `Re s ≥ 1 - l⁻²⁵` and `‖s‖ ≤ e^l`,
`E_χ(s) ≠ 0` and `‖E_χ'(s) / E_χ(s)‖ ≤ 2 l²⁵`. -/
theorem entireLFunction_ne_zero_and_norm_logDeriv_le (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖χ.regularizedLFunction z‖)
    (h_re : 1 - 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ rexp l) :
    χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ 2 * l ^ 25 := by
  have two_le : 2 ≤ l ^ 25 := by
    linarith [le_self_pow₀ (by linarith : 1 ≤ l) (by norm_num : 25 ≠ 0)]
  obtain ⟨h_ne, h_bound⟩ := χ.regularizedLFunction_ne_zero_and_norm_logDeriv_le hl hN h_near h_re
    h_norm
  by_cases hχ : χ = 1
  · -- `E_χ(z) = z f_χ(z)`, so `E_χ' / E_χ = f_χ' / f_χ + 1 / z` with `‖1 / s‖ ≤ 2`.
    subst hχ
    have hs_re : 1 / 2 ≤ s.re := by linarith [one_div_le_one_div_of_le two_pos two_le]
    have hs_norm : 1 / 2 ≤ ‖s‖ := hs_re.trans (re_le_norm s)
    have hs_ne : s ≠ 0 := norm_pos_iff.1 (by linarith)
    have h_ev : (1 : DirichletCharacter ℂ N).entireLFunction =ᶠ[𝓝 s]
        fun z ↦ id z * (1 : DirichletCharacter ℂ N).regularizedLFunction z := by
      filter_upwards [isOpen_ne.mem_nhds hs_ne] with z hz
      rw [regularizedLFunction_one_apply, id, mul_div_cancel₀ _ hz]
    have h_split : logDeriv (1 : DirichletCharacter ℂ N).entireLFunction s =
        logDeriv id s + logDeriv (1 : DirichletCharacter ℂ N).regularizedLFunction s := by
      rw [logDeriv_apply, h_ev.deriv_eq, h_ev.eq_of_nhds, ← logDeriv_apply]
      exact logDeriv_mul s hs_ne h_ne differentiableAt_id
        ((1 : DirichletCharacter ℂ N).differentiableAt_regularizedLFunction
          (.inl (ne_zero_of_re_pos (by linarith))))
    refine ⟨by rw [h_ev.eq_of_nhds]; exact mul_ne_zero hs_ne h_ne, ?_⟩
    have h_id : ‖logDeriv id s‖ ≤ 2 := by
      simpa [logDeriv_apply] using (one_div_le (by linarith) two_pos).2 hs_norm
    rw [h_split]
    linarith [norm_add_le (logDeriv id s)
      (logDeriv (1 : DirichletCharacter ℂ N).regularizedLFunction s)]
  · rw [regularizedLFunction_of_ne_one χ hχ] at h_ne h_bound
    rw [entireLFunction_of_ne_one hχ]
    exact ⟨h_ne, h_bound.trans (by linarith)⟩

/-- *Zero-free region* for one character: for all large `l`, on `Re s ≥ 1 - l⁻²⁵`,
`‖s‖ ≤ e^l`, `E_χ(s) ≠ 0` and `‖E_χ'(s) / E_χ(s)‖ ≤ 2 l²⁵`. -/
theorem eventually_entireLFunction_ne_zero_and_norm_logDeriv_le :
    ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ 25 ≤ s.re → ‖s‖ ≤ rexp l →
      χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ 2 * l ^ 25 := by
  have inv_tendsto : Tendsto (fun l : ℝ ↦ 1 / l) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_ge_atTop (10 ^ 10), eventually_ge_atTop (N : ℝ),
    inv_tendsto.eventually χ.eventually_le_norm_regularizedLFunction] with l hl hN h_near s
  exact χ.entireLFunction_ne_zero_and_norm_logDeriv_le hl (by linarith [add_one_le_exp l])
    fun _ ↦ h_near

open scoped ArithmeticFunction.vonMangoldt in
private theorem norm_logDeriv_entireLFunction_le_of_two_le_re (hs : 2 ≤ s.re) :
    ‖logDeriv χ.entireLFunction s‖ ≤ 1 - (logDeriv riemannZeta 2).re := by
  classical
  have hs' : 1 < s.re := by linarith
  have hpole : ‖(if χ = 1 then (1 : ℂ) else 0) / (s - 1)‖ ≤ 1 := by
    have hdist : 1 ≤ ‖s - 1‖ := by linarith [re_le_norm (s - 1), sub_re s 1, one_re]
    rw [norm_div, div_le_iff₀ (by linarith : 0 < ‖s - 1‖), one_mul]
    exact (by split <;> simp : ‖(if χ = 1 then (1 : ℂ) else 0)‖ ≤ 1).trans hdist
  have hL := χ.norm_logDeriv_LFunction_le_of_le_re (σ := 2) (by norm_num) hs
  have hseries := (χ.LSeriesHasSum_twist_vonMangoldt hs').LSeries_eq
  simp only [ofReal_ofNat, χ.logDeriv_LFunction_eq_neg_LSeries hs', norm_neg, Pi.mul_def] at hL
  have hE : logDeriv χ.entireLFunction s =
      (if χ = 1 then 1 else 0) / (s - 1) - LSeries (fun n : ℕ ↦ χ n * Λ n) s := by
    rw [hseries]; ring
  rw [hE]
  exact (norm_sub_le _ _).trans (by linarith)

/-- For a fixed character, `E_χ` is zero-free on a log-power region determined by height
alone and its logarithmic derivative there grows at most as the reciprocal of the width. -/
theorem exists_entireLFunction_ne_zero_and_norm_logDeriv_le_log_pow :
    ∃ a > (0 : ℝ), ∃ C : ℝ, ∀ s : ℂ,
      1 - a / Real.log (|s.im| + 3) ^ 25 ≤ s.re →
      χ.entireLFunction s ≠ 0 ∧
        ‖logDeriv χ.entireLFunction s‖ ≤ C * Real.log (|s.im| + 3) ^ 25 := by
  obtain ⟨L, hL⟩ := eventually_atTop.1 χ.eventually_entireLFunction_ne_zero_and_norm_logDeriv_le
  let K : ℝ := max L 2
  have hK : 2 ≤ K := le_max_right _ _
  refine ⟨(K ^ 25)⁻¹, by positivity, max (2 * K ^ 25) (1 - (logDeriv riemannZeta 2).re),
    fun s hs ↦ ?_⟩
  let t : ℝ := |s.im| + 3
  have ht : 3 ≤ t := by dsimp [t]; linarith [abs_nonneg s.im]
  have hlog : 1 ≤ Real.log t := (Real.le_log_iff_exp_le (by positivity : 0 < t)).2
    (by linarith [Real.exp_one_lt_d9])
  have hp : 1 ≤ Real.log t ^ 25 := one_le_pow₀ hlog
  rcases le_or_gt 2 s.re with hright | hleft
  · refine ⟨χ.entireLFunction_ne_zero_of_one_le_re (by linarith),
      (norm_logDeriv_entireLFunction_le_of_two_le_re χ hright).trans ?_⟩
    exact (le_max_right _ _).trans (le_mul_of_one_le_right
      ((by positivity : 0 ≤ 2 * K ^ 25).trans (le_max_left _ _)) hp)
  set l : ℝ := K * Real.log t with hl_def
  have hKl : K ≤ l := le_mul_of_one_le_right (by positivity) hlog
  have hl : L ≤ l := (le_max_left _ _).trans hKl
  have hwidth : 1 / l ^ 25 = (K ^ 25)⁻¹ / Real.log t ^ 25 := by
    rw [hl_def, mul_pow, one_div, mul_inv, div_eq_mul_inv]
  have hσ : 1 - 1 / l ^ 25 ≤ s.re := by rwa [hwidth]
  have hσ₀ : 0 ≤ s.re := by
    have h : 1 ≤ l ^ 25 := one_le_pow₀ (by linarith)
    linarith [one_div_le_one_div_of_le zero_lt_one h]
  have hnorm : ‖s‖ ≤ Real.exp l := calc
    _ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
    _ ≤ t := by dsimp [t]; rw [abs_of_nonneg hσ₀]; linarith
    _ = Real.exp (Real.log t) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.2 (le_mul_of_one_le_left (by linarith) (by linarith))
  refine (hL l hl s hσ hnorm).imp_right fun hb ↦ hb.trans ?_
  rw [hl_def, mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end DirichletCharacter
