/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.SchlafliIntegral.Amplitude
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Asymptotic bounds and Laplace transformation of Schläfli's integral

Under the substitution `τ = cosh u - 1`, Schläfli's modified-Bessel / generalized-Airy integral
`∫₀^∞ e^{-ζ cosh u} cosh(p u) du` becomes the standard Laplace integral
`e^{-ζ} ∫₀^∞ e^{-ζ τ} τ^{-1/2} h_p(τ) dτ` with amplitude `h_p = TauCeti.schlafliAmplitude p`
defined in `TauCeti.Analysis.SpecialFunctions.SchlafliIntegral.Amplitude`.

This file supplies the analytic estimates and Bochner change-of-variables identities that connect
Schläfli's integral to Watson's lemma and its sectorial rotation:

1. **Subsector growth bounds:** on every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}` (`0 < δ ≤ π`)
   of `Complex.slitPlane`, `‖schlafliAmplitude p w‖` grows at most like
   `(1 + ‖w‖) ^ (|p.re| - 1/2)`. Consequently `w ↦ w ^ (-1/2) * schlafliAmplitude p w` is bounded
   at infinity on the subsector whenever `|p.re| ≤ 1` (covering all generalized Airy orders
   `p = 1 / (n + 2)` and `p = 1 / 2`) and has subexponential growth `=O(exp (σ ‖w‖))` for every
   `σ > 0` and arbitrary `p : ℂ`.
2. **All-order Taylor remainder bounds at `0`:** subtracting the `N`-term Maclaurin partial sum from
   `schlafliAmplitude p w` leaves a `=O[𝓝 0] (w ^ N)` remainder, so multiplying by `w ^ (-1/2)`
   yields a `=O[𝓝 0] (‖w‖ ^ (N - 1/2))` remainder on `ℂ` and `=O[𝓝[>] 0] (τ ^ (N - 1/2))` on
   `(0, ∞)`.
3. **Laplace change of variables `τ = cosh u - 1`:** the Bochner substitution on `(0, ∞)` for
   arbitrary `ℂ`-normed spaces, its specialization to `∫₀^∞ e^{-ζ cosh u} cosh(p u) du`, and
   convergence and holomorphy in `ζ` on the right half-plane `{ζ : ℂ | 0 < ζ.re}`.

## Main statements

* `TauCeti.norm_schlafliAmplitude_le_of_abs_arg_le`: explicit polynomial growth bound on closed
  subsectors `|w.arg| ≤ π - δ`.
* `TauCeti.isBigO_cpow_neg_half_mul_schlafliAmplitude_one_sector` and
  `TauCeti.isBigO_cpow_neg_half_mul_schlafliAmplitude_exp_sector`: boundedness (for `|p.re| ≤ 1`)
  and exponential growth bounds at infinity on closed subsectors of `Complex.slitPlane`.
* `TauCeti.isBigO_schlafliAmplitude_sub_sum`,
  `TauCeti.isBigO_cpow_neg_half_mul_schlafliAmplitude_sub_sum`, and
  `TauCeti.isBigO_cpow_neg_half_mul_schlafliAmplitude_sub_sum_nhdsGT`: all-order Taylor remainder
  estimates at `0`.
* `TauCeti.integrableOn_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi_iff` and
  `TauCeti.integral_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi`: Bochner substitution
  `τ = cosh u - 1` on `(0, ∞)`.
* `TauCeti.integral_cexp_neg_mul_cosh_mul_cosh_eq_cexp_mul_integral_schlafliAmplitude`,
  `TauCeti.integrableOn_cexp_neg_mul_cpow_neg_half_mul_schlafliAmplitude_Ioi`, and
  `TauCeti.differentiableOn_integral_cexp_neg_mul_cpow_neg_half_mul_schlafliAmplitude_Ioi`:
  Laplace integral representation and right-half-plane holomorphy.

## References

* NIST Digital Library of Mathematical Functions, §§9.13(i)–(ii), 10.17(i), 10.32(ii), 10.40(i),
  <https://dlmf.nist.gov/9.13>, <https://dlmf.nist.gov/10.17>, <https://dlmf.nist.gov/10.32>,
  <https://dlmf.nist.gov/10.40>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 4 and §7.4.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §§6.22, 7.2.
-/

public section

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set
open scoped Nat Topology

namespace TauCeti

/-! ### Subsector growth bounds for `schlafliAmplitude` -/

/-- On every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}` (`0 < δ ≤ π`), `‖schlafliAmplitude p w‖`
is bounded by an explicit constant times `(1 + ‖w‖) ^ (|p.re| - 1 / 2)`. -/
theorem norm_schlafliAmplitude_le_of_abs_arg_le (p : ℂ) {δ : ℝ} (hδ₀ : 0 < δ)
    (hδπ : δ ≤ Real.pi) {w : ℂ} (hw : |w.arg| ≤ Real.pi - δ) :
    ‖schlafliAmplitude p w‖ ≤
      4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2)) *
        (1 + ‖w‖) ^ (|p.re| - 1 / 2) := by
  have hs_pos : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1s : 0 ≤ 1 - Real.sin (δ / 2) ^ 2 := by nlinarith [Real.sin_le_one (δ / 2)]
  have hre : -‖w‖ * Real.cos δ ≤ w.re := by
    rw [← norm_mul_cos_arg w, ← Real.cos_abs w.arg]
    have hcos : -Real.cos δ ≤ Real.cos |w.arg| := by
      rw [← Real.cos_pi_sub]
      exact Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, hw.trans (by linarith)⟩
        ⟨by linarith, by linarith⟩ hw
    nlinarith [norm_nonneg w]
  have hw2_ge : Real.sin (δ / 2) * (1 + ‖w‖) ≤ ‖w + 2‖ := by
    rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
    have hw_sq : w.re * w.re + w.im * w.im = ‖w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have hcos2 : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
      have h2 := Real.cos_two_mul (δ / 2)
      rw [show 2 * (δ / 2) = δ by ring] at h2; linarith [Real.sin_sq_add_cos_sq (δ / 2)]
    rw [show (w + 2).re = w.re + 2 by simp, show (w + 2).im = w.im by simp]
    nlinarith [mul_nonneg h1s (sq_nonneg (‖w‖ - 2)), norm_nonneg w, hs_pos]
  have hw2_pos : 0 < ‖w + 2‖ := lt_of_lt_of_le (by positivity) hw2_ge
  have hden : Real.sqrt (Real.sin (δ / 2)) * (1 + ‖w‖) ^ (1 / 2 : ℝ) ≤
      ‖(w + 2) ^ (1 / 2 : ℂ)‖ := by
    rw [norm_cpow_of_ne_zero (norm_pos_iff.mp hw2_pos), show (1 / 2 : ℂ).re = 1 / 2 by simp,
      show (1 / 2 : ℂ).im = 0 by simp, mul_zero, Real.exp_zero, div_one, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hs_pos.le]
    exact Real.sqrt_le_sqrt hw2_ge
  have hnum : (1 + Real.sqrt (2 * ‖w‖)) ^ (2 * |p.re|) ≤ 4 ^ |p.re| * (1 + ‖w‖) ^ |p.re| := by
    have hbase : 1 + Real.sqrt (2 * ‖w‖) ≤ 2 * Real.sqrt (1 + ‖w‖) := by
      rw [← sq_le_sq₀ (by positivity) (by positivity)]
      nlinarith [Real.sq_sqrt (mul_nonneg zero_le_two (norm_nonneg w)),
        Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖w‖), sq_nonneg (Real.sqrt (2 * ‖w‖) - 1)]
    calc (1 + Real.sqrt (2 * ‖w‖)) ^ (2 * |p.re|)
        ≤ (2 * Real.sqrt (1 + ‖w‖)) ^ (2 * |p.re|) :=
          Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = 2 ^ (2 * |p.re|) * ((1 + ‖w‖) ^ (1 / 2 : ℝ)) ^ (2 * |p.re|) := by
          rw [Real.mul_rpow zero_le_two (by positivity), Real.sqrt_eq_rpow]
      _ = 4 ^ |p.re| * (1 + ‖w‖) ^ |p.re| := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul zero_le_two,
            ← Real.rpow_mul (by positivity)]
          congr 2; ring
  rw [schlafliAmplitude_def, norm_div]
  have htop := (norm_coshMulArcosh_one_add_le p w).trans
    (mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le)
  calc ‖coshMulArcosh p (1 + w)‖ / ‖(w + 2) ^ (1 / 2 : ℂ)‖
      ≤ (4 ^ |p.re| * (1 + ‖w‖) ^ |p.re| * Real.exp (Real.pi * |p.im|)) /
          (Real.sqrt (Real.sin (δ / 2)) * (1 + ‖w‖) ^ (1 / 2 : ℝ)) :=
        div_le_div₀ (by positivity) htop (by positivity) hden
    _ = 4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2)) *
          ((1 + ‖w‖) ^ |p.re| / (1 + ‖w‖) ^ (1 / 2 : ℝ)) := by ring
    _ = 4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2)) *
          (1 + ‖w‖) ^ (|p.re| - 1 / 2) := by rw [← Real.rpow_sub (by positivity)]

/-- When `|p.re| ≤ 1`, `w ↦ w ^ (-1 / 2) * schlafliAmplitude p w` is bounded near infinity on
every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}` (`0 < δ ≤ π`). -/
theorem isBigO_cpow_neg_half_mul_schlafliAmplitude_one_sector {p : ℂ} (hp : |p.re| ≤ 1)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    (fun w : ℂ ↦ w ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p w)
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | |w.arg| ≤ Real.pi - δ}] (fun _ ↦ (1 : ℝ)) := by
  set C := 4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2))
  have hs_pos : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine IsBigO.of_bound (Real.sqrt 2 * C) ?_
  filter_upwards [Filter.mem_inf_of_left (eventually_cobounded_le_norm 1),
    Filter.mem_inf_of_right (mem_principal_self _)] with w hw1 hw_sec
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hw1)
  have hwn : ‖w ^ (-(1 / 2 : ℂ))‖ = ‖w‖ ^ (-(1 / 2 : ℝ)) := by
    rw [norm_cpow_of_ne_zero hw0]; simp
  have hrpow : (1 + ‖w‖) ^ (|p.re| - 1 / 2) ≤ Real.sqrt 2 * ‖w‖ ^ (1 / 2 : ℝ) :=
    calc (1 + ‖w‖) ^ (|p.re| - 1 / 2)
        ≤ (1 + ‖w‖) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (2 * ‖w‖) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = Real.sqrt 2 * ‖w‖ ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow zero_le_two (norm_nonneg _), Real.sqrt_eq_rpow]
  have hcancel : ‖w‖ ^ (-(1 / 2 : ℝ)) * ‖w‖ ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hw1)]; norm_num
  rw [norm_mul, hwn, Real.norm_eq_abs, abs_one, mul_one]
  calc ‖w‖ ^ (-(1 / 2 : ℝ)) * ‖schlafliAmplitude p w‖
      ≤ ‖w‖ ^ (-(1 / 2 : ℝ)) * (C * (Real.sqrt 2 * ‖w‖ ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          ((norm_schlafliAmplitude_le_of_abs_arg_le p hδ₀ hδπ hw_sec).trans
            (mul_le_mul_of_nonneg_left hrpow hC)) (by positivity)
    _ = Real.sqrt 2 * C * (‖w‖ ^ (-(1 / 2 : ℝ)) * ‖w‖ ^ (1 / 2 : ℝ)) := by ring
    _ = Real.sqrt 2 * C := by rw [hcancel, mul_one]

/-- For every `p : ℂ` and `σ > 0`, `w ↦ w ^ (-1 / 2) * schlafliAmplitude p w` is
`=O(exp (σ * ‖w‖))` at infinity on every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}`
(`0 < δ ≤ π`). -/
theorem isBigO_cpow_neg_half_mul_schlafliAmplitude_exp_sector (p : ℂ) {δ σ : ℝ}
    (hδ₀ : 0 < δ) (hδπ : δ ≤ Real.pi) (hσ : 0 < σ) :
    (fun w : ℂ ↦ w ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p w)
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | |w.arg| ≤ Real.pi - δ}]
      (fun w : ℂ ↦ Real.exp (σ * ‖w‖)) := by
  set C := 4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2))
  set n := ⌈|p.re|⌉₊
  have hs_pos : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine IsBigO.of_bound (C * ((2 : ℝ) ^ n * (n ! : ℝ) / σ ^ n)) ?_
  filter_upwards [Filter.mem_inf_of_left (eventually_cobounded_le_norm 1),
    Filter.mem_inf_of_right (mem_principal_self _)] with w hw1 hw_sec
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hw1)
  have hwn : ‖w ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
    rw [norm_cpow_of_ne_zero hw0]
    simpa using Real.rpow_le_one_of_one_le_of_nonpos hw1 (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  have hpoly : (1 + ‖w‖) ^ (|p.re| - 1 / 2) ≤ (2 : ℝ) ^ n * ‖w‖ ^ n :=
    calc (1 + ‖w‖) ^ (|p.re| - 1 / 2)
        ≤ (1 + ‖w‖) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by linarith [Nat.le_ceil |p.re|])
      _ = (1 + ‖w‖) ^ n := Real.rpow_natCast _ n
      _ ≤ (2 * ‖w‖) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = (2 : ℝ) ^ n * ‖w‖ ^ n := mul_pow 2 ‖w‖ n
  have hexp : ‖w‖ ^ n ≤ (n ! : ℝ) / σ ^ n * Real.exp (σ * ‖w‖) := by
    have hle := Real.pow_div_factorial_le_exp (σ * ‖w‖) (mul_nonneg hσ.le (norm_nonneg w)) n
    have hpos : 0 < σ ^ n / (n ! : ℝ) := by positivity
    rw [mul_pow, mul_div_right_comm] at hle
    exact (le_div_iff₀' hpos).mpr hle |>.trans_eq (by field_simp)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hamp := (norm_schlafliAmplitude_le_of_abs_arg_le p hδ₀ hδπ hw_sec).trans
    (mul_le_mul_of_nonneg_left (hpoly.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) hC)
  calc ‖w ^ (-(1 / 2 : ℂ))‖ * ‖schlafliAmplitude p w‖
      ≤ 1 * (C * ((2 : ℝ) ^ n * ((n ! : ℝ) / σ ^ n * Real.exp (σ * ‖w‖)))) :=
        mul_le_mul hwn hamp (norm_nonneg _) zero_le_one
    _ = C * ((2 : ℝ) ^ n * (n ! : ℝ) / σ ^ n) * Real.exp (σ * ‖w‖) := by ring

/-! ### All-order Taylor remainder bounds at `0` -/

/-- Subtracting the `N`-term Maclaurin partial sum from `schlafliAmplitude p w` leaves a
`=O[𝓝 0] (w ^ N)` remainder. -/
theorem isBigO_schlafliAmplitude_sub_sum (p : ℂ) (N : ℕ) :
    (fun w : ℂ ↦ schlafliAmplitude p w -
      ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ k) =O[𝓝 0]
      (fun w : ℂ ↦ w ^ N) := by
  obtain ⟨F, hFa, hF⟩ := (analyticAt_schlafliAmplitude_zero p).exists_eventuallyEq_sum_add_pow_mul N
  have hev : (fun w : ℂ ↦ schlafliAmplitude p w -
      ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ k) =ᶠ[𝓝 0]
      fun w : ℂ ↦ w ^ N * F w := by
    filter_upwards [hF] with w hw
    rw [hw]
    have hsum : (∑ i ∈ Finset.range N,
        (w ^ i / (i ! : ℂ)) • iteratedDeriv i (schlafliAmplitude p) 0) =
        ∑ i ∈ Finset.range N, schlafliAmplitudeCoeff p i * w ^ i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [iteratedDeriv_schlafliAmplitude_zero, smul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)]
    rw [hsum, smul_eq_mul, add_sub_cancel_left]
  exact ((isBigO_refl (fun w : ℂ ↦ w ^ N) (𝓝 0)).mul
    (hFa.continuousAt.tendsto.isBigO_one ℂ)).congr' hev.symm
    (Eventually.of_forall fun w ↦ mul_one (w ^ N))

/-- Multiplying the `N`-term Taylor remainder of `schlafliAmplitude p` by `w ^ (-1 / 2)` gives a
`=O[𝓝 0] (‖w‖ ^ (N - 1 / 2))` remainder across a full neighborhood of `0` in `ℂ`. -/
theorem isBigO_cpow_neg_half_mul_schlafliAmplitude_sub_sum (p : ℂ) (N : ℕ) :
    (fun w : ℂ ↦ w ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p w -
      ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ ((k : ℂ) - 1 / 2))
      =O[𝓝 0] (fun w : ℂ ↦ ‖w‖ ^ ((N : ℝ) - 1 / 2)) := by
  obtain ⟨C, hC_pos, hC⟩ := (isBigO_schlafliAmplitude_sub_sum p N).exists_pos
  rw [Asymptotics.isBigOWith_iff] at hC
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with w hw
  have hexp_ne : ∀ m : ℕ, (m : ℂ) - 1 / 2 ≠ 0 := fun m hm ↦ by
    have hre : (m : ℝ) - 1 / 2 = 0 := by simpa using congr_arg Complex.re hm
    rcases m with _ | m <;> push_cast at hre <;> linarith
  by_cases hw0 : w = 0
  · subst hw0
    have h0_half : (0 : ℂ) ^ (-(1 / 2 : ℂ)) = 0 := zero_cpow (by norm_num)
    have h0_sum : (∑ k ∈ Finset.range N,
        schlafliAmplitudeCoeff p k * (0 : ℂ) ^ ((k : ℂ) - 1 / 2)) = 0 :=
      Finset.sum_eq_zero fun k _ ↦ by rw [zero_cpow (hexp_ne k), mul_zero]
    rw [h0_half, zero_mul, zero_sub, h0_sum, neg_zero, norm_zero]
    positivity
  · have hsum_eq : (∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ ((k : ℂ) - 1 / 2)) =
        w ^ (-(1 / 2 : ℂ)) * ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [show (k : ℂ) - 1 / 2 = -(1 / 2 : ℂ) + (k : ℂ) by ring, cpow_add _ _ hw0,
        cpow_natCast]
      ring
    rw [norm_pow] at hw
    rw [hsum_eq, ← mul_sub, norm_mul, norm_cpow_of_ne_zero hw0]
    simp only [neg_re, div_ofNat_re, one_re, neg_im, div_ofNat_im, one_im, zero_div, neg_zero,
      mul_zero, Real.exp_zero, div_one, Real.norm_eq_abs]
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    calc ‖w‖ ^ (-(1 / 2 : ℝ)) * ‖schlafliAmplitude p w -
          ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ k‖
        ≤ ‖w‖ ^ (-(1 / 2 : ℝ)) * (C * ‖w‖ ^ N) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = C * (‖w‖ ^ (-(1 / 2 : ℝ)) * ‖w‖ ^ (N : ℝ)) := by rw [Real.rpow_natCast]; ring
      _ = C * ‖w‖ ^ ((N : ℝ) - 1 / 2) := by
          rw [← Real.rpow_add hw_pos]; congr 2; ring
      _ ≤ C * |‖w‖ ^ ((N : ℝ) - 1 / 2)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hC_pos.le

/-- Real-line restriction of `isBigO_cpow_neg_half_mul_schlafliAmplitude_sub_sum` on `𝓝[>] 0`,
matching the hypothesis of Watson's lemma on `(0, ∞)`. -/
theorem isBigO_cpow_neg_half_mul_schlafliAmplitude_sub_sum_nhdsGT (p : ℂ) (N : ℕ) :
    (fun τ : ℝ ↦ (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ -
      ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * (τ : ℂ) ^ ((k : ℂ) - 1 / 2))
      =O[𝓝[>] (0 : ℝ)] (fun τ : ℝ ↦ τ ^ ((N : ℝ) - 1 / 2)) := by
  have htend : Tendsto (fun τ : ℝ ↦ (τ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hcomp := (isBigO_cpow_neg_half_mul_schlafliAmplitude_sub_sum p N).comp_tendsto htend
  refine hcomp.congr' EventuallyEq.rfl ?_
  filter_upwards [self_mem_nhdsWithin] with τ (hτ : 0 < τ)
  simp [Real.norm_of_nonneg hτ.le]

/-! ### Bochner change of variables `τ = cosh u - 1` and Schläfli's Laplace integral -/

private theorem sinh_smul_schlafliAmplitude_cosh_sub_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (p : ℂ) (g : ℝ → E)
    {u : ℝ} (hu : 0 < u) :
    |Real.sinh u| • (((Real.cosh u - 1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        schlafliAmplitude p (Real.cosh u - 1 : ℝ)) • g (Real.cosh u - 1) =
      Complex.cosh (p * u) • g (Real.cosh u - 1) := by
  have hsh_pos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hch_gt : 1 < Real.cosh u := Real.one_lt_cosh.mpr hu.ne'
  have hτ_pos : 0 < Real.cosh u - 1 := sub_pos.mpr hch_gt
  have hcpow : ((Real.cosh u - 1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.sqrt (Real.cosh u - 1))⁻¹ : ℝ) := by
    rw [cpow_neg, ofReal_inv]
    congr 1
    rw [Real.sqrt_eq_rpow, ofReal_cpow hτ_pos.le]
    push_cast; rfl
  have hprod : Real.sqrt (Real.cosh u - 1) * Real.sqrt (Real.cosh u + 1) = Real.sinh u := by
    rw [← Real.sqrt_mul hτ_pos.le,
      show (Real.cosh u - 1) * (Real.cosh u + 1) = Real.sinh u ^ 2 by
        linarith [Real.cosh_sq_sub_sinh_sq u],
      Real.sqrt_sq hsh_pos.le]
  have hs1 : (Real.sqrt (Real.cosh u - 1) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hτ_pos).ne'
  have hs2 : (Real.sqrt (Real.cosh u + 1) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [abs_of_pos hsh_pos, ← Complex.coe_smul, smul_smul, hcpow,
    schlafliAmplitude_ofReal_cosh_sub_one]
  congr 1
  have hprod_c : (Real.sqrt (Real.cosh u - 1) : ℂ) * (Real.sqrt (Real.cosh u + 1) : ℂ) =
      (Real.sinh u : ℂ) := by exact_mod_cast hprod
  rw [← hprod_c, ofReal_inv]
  field_simp [hs1, hs2]

/-- Integrability equivalence under the substitution `τ = cosh u - 1` on `(0, ∞)` for a
`ℂ`-Banach-space-valued integrand `g`. -/
theorem integrableOn_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (p : ℂ) (g : ℝ → E) :
    IntegrableOn (fun τ : ℝ ↦
      ((τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) • g τ) (Ioi 0) ↔
    IntegrableOn (fun u : ℝ ↦ Complex.cosh (p * u) • g (Real.cosh u - 1)) (Ioi 0) := by
  let f : ℝ → ℝ := fun u ↦ Real.cosh u - 1
  have himg : f '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext τ
    simp only [mem_image, mem_Ioi, f]
    refine ⟨fun ⟨u, hu, hτ⟩ ↦ ?_, fun hτ ↦ ⟨Real.arcosh (1 + τ), Real.arcosh_pos (by linarith), ?_⟩⟩
    · linarith [Real.one_lt_cosh.mpr hu.ne']
    · rw [Real.cosh_arcosh (by linarith)]; ring
  have hinj : InjOn f (Ioi 0) := fun u₁ hu₁ u₂ hu₂ heq ↦ by
    have hch : Real.cosh u₁ = Real.cosh u₂ := by dsimp [f] at heq; linarith
    simpa [Real.arcosh_cosh (le_of_lt hu₁), Real.arcosh_cosh (le_of_lt hu₂)] using
      congr_arg Real.arcosh hch
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt f (Real.sinh u) (Ioi 0) u :=
    fun u _ ↦ ((Real.hasDerivAt_cosh u).sub_const 1).hasDerivWithinAt
  conv_lhs => rw [← himg]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine integrableOn_congr_fun (fun u hu ↦ ?_) measurableSet_Ioi
  exact sinh_smul_schlafliAmplitude_cosh_sub_one p g hu

/-- Bochner change-of-variables identity `τ = cosh u - 1` on `(0, ∞)` for `schlafliAmplitude`. -/
theorem integral_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (p : ℂ) (g : ℝ → E) :
    (∫ τ in Ioi (0 : ℝ), ((τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) • g τ) =
      ∫ u in Ioi (0 : ℝ), Complex.cosh (p * u) • g (Real.cosh u - 1) := by
  let f : ℝ → ℝ := fun u ↦ Real.cosh u - 1
  have himg : f '' Ioi 0 = Ioi 0 := by
    ext τ
    simp only [mem_image, mem_Ioi, f]
    refine ⟨fun ⟨u, hu, hτ⟩ ↦ ?_, fun hτ ↦ ⟨Real.arcosh (1 + τ), Real.arcosh_pos (by linarith), ?_⟩⟩
    · linarith [Real.one_lt_cosh.mpr hu.ne']
    · rw [Real.cosh_arcosh (by linarith)]; ring
  have hinj : InjOn f (Ioi 0) := fun u₁ hu₁ u₂ hu₂ heq ↦ by
    have hch : Real.cosh u₁ = Real.cosh u₂ := by dsimp [f] at heq; linarith
    simpa [Real.arcosh_cosh (le_of_lt hu₁), Real.arcosh_cosh (le_of_lt hu₂)] using
      congr_arg Real.arcosh hch
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt f (Real.sinh u) (Ioi 0) u :=
    fun u _ ↦ ((Real.hasDerivAt_cosh u).sub_const 1).hasDerivWithinAt
  conv_lhs => rw [← himg]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  exact sinh_smul_schlafliAmplitude_cosh_sub_one p g hu

/-- Equivalence of integrability between Schläfli's `cosh`-integral and its Laplace form on
`(0, ∞)`. -/
theorem integrableOn_cexp_neg_mul_cosh_mul_cosh_Ioi_iff (ζ p : ℂ) :
    IntegrableOn (fun u : ℝ ↦ Complex.exp (-ζ * Real.cosh u) * Complex.cosh (p * u)) (Ioi 0) ↔
    IntegrableOn (fun τ : ℝ ↦
      Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) (Ioi 0) := by
  have hiff := (integrableOn_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi_iff p
    (fun τ : ℝ ↦ Complex.exp (-ζ * (1 + (τ : ℂ))))).symm
  refine (integrableOn_congr_fun (fun u _ ↦ ?_) measurableSet_Ioi).trans
    (hiff.trans ⟨fun h ↦ ?_, fun h ↦ ?_⟩)
  · simp only [smul_eq_mul, ofReal_sub, ofReal_one]
    rw [show (1 : ℂ) + ((Real.cosh u : ℂ) - 1) = Real.cosh u by ring, mul_comm]
  · refine IntegrableOn.congr_fun (h.const_mul (Complex.exp ζ)) (fun τ _ ↦ ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    rw [show -ζ * (1 + (τ : ℂ)) = -ζ + (-ζ * τ) by ring, Complex.exp_add]
    calc Complex.exp ζ * ((τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ *
          (Complex.exp (-ζ) * Complex.exp (-ζ * τ)))
        = (Complex.exp ζ * Complex.exp (-ζ)) *
            (Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) := by ring
      _ = Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ := by
          rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  · refine IntegrableOn.congr_fun (h.const_mul (Complex.exp (-ζ))) (fun τ _ ↦ ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    rw [show -ζ * (1 + (τ : ℂ)) = -ζ + (-ζ * τ) by ring, Complex.exp_add]
    ring

/-- The Laplace transformation `τ = cosh u - 1` of Schläfli's integral on `(0, ∞)`:
`∫₀^∞ e^{-ζ cosh u} cosh(p u) du = e^{-ζ} ∫₀^∞ e^{-ζ τ} τ^{-1/2} schlafliAmplitude p τ dτ`. -/
theorem integral_cexp_neg_mul_cosh_mul_cosh_eq_cexp_mul_integral_schlafliAmplitude (ζ p : ℂ) :
    (∫ u in Ioi (0 : ℝ), Complex.exp (-ζ * Real.cosh u) * Complex.cosh (p * u)) =
      Complex.exp (-ζ) * ∫ τ in Ioi (0 : ℝ),
        Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ := by
  have heq := (integral_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi p
    (fun τ : ℝ ↦ Complex.exp (-ζ * (1 + (τ : ℂ))))).symm
  have hlhs : (∫ u in Ioi (0 : ℝ),
      Complex.cosh (p * u) • Complex.exp (-ζ * (1 + ((Real.cosh u - 1 : ℝ) : ℂ)))) =
      ∫ u in Ioi (0 : ℝ), Complex.exp (-ζ * Real.cosh u) * Complex.cosh (p * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    simp only [smul_eq_mul, ofReal_sub, ofReal_one]
    rw [show (1 : ℂ) + ((Real.cosh u : ℂ) - 1) = Real.cosh u by ring, mul_comm]
  rw [← hlhs, heq, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ ↦ ?_
  simp only [smul_eq_mul]
  rw [show -ζ * (1 + (τ : ℂ)) = -ζ + (-ζ * τ) by ring, Complex.exp_add]
  ring

private theorem norm_schlafliAmplitude_ofReal_le_exp (p : ℂ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ B > 0, ∀ τ : ℝ, 0 ≤ τ → ‖schlafliAmplitude p τ‖ ≤ B * Real.exp (σ * τ) := by
  set C := 4 ^ |p.re| * Real.exp (Real.pi * |p.im|)
  set n := ⌈|p.re|⌉₊
  have hC_pos : 0 < C := by dsimp [C]; positivity
  refine ⟨C * ((n ! : ℝ) * Real.exp σ / σ ^ n), by positivity, fun τ hτ ↦ ?_⟩
  have harg : |(τ : ℂ).arg| ≤ Real.pi - Real.pi := by
    rw [arg_ofReal_of_nonneg hτ, abs_zero, sub_self]
  have hsec := norm_schlafliAmplitude_le_of_abs_arg_le p Real.pi_pos le_rfl harg
  rw [Real.sin_pi_div_two, Real.sqrt_one, div_one, Complex.norm_of_nonneg hτ] at hsec
  have hle := Real.pow_div_factorial_le_exp (σ * (1 + τ))
    (mul_nonneg hσ.le (by linarith : 0 ≤ 1 + τ)) n
  have hpos : 0 < σ ^ n / (n ! : ℝ) := by positivity
  rw [mul_pow, mul_div_right_comm, show σ * (1 + τ) = σ + σ * τ by ring, Real.exp_add] at hle
  have hexp : (1 + τ) ^ n ≤ (n ! : ℝ) * Real.exp σ / σ ^ n * Real.exp (σ * τ) :=
    (le_div_iff₀' hpos).mpr hle |>.trans_eq (by field_simp)
  have hrpow : (1 + τ) ^ (|p.re| - 1 / 2) ≤ (1 + τ) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Nat.le_ceil |p.re|])
  exact hsec.trans ((mul_le_mul_of_nonneg_left (hrpow.trans hexp) hC_pos.le).trans_eq (by ring))

private theorem continuousOn_schlafliLaplaceIntegrand (ζ p : ℂ) :
    ContinuousOn
      (fun τ : ℝ ↦ Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ)
      (Ioi 0) := by
  refine ((Continuous.continuousOn (by fun_prop)).mul ?_).mul ?_
  · intro τ (hτ : 0 < τ)
    have hcont : ContinuousAt (fun z : ℂ ↦ z ^ (-(1 / 2 : ℂ))) (τ : ℂ) :=
      (differentiableAt_id.cpow_const (ofReal_mem_slitPlane.mpr hτ)).continuousAt
    exact (hcont.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · exact (differentiableOn_schlafliAmplitude_slitPlane p).continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun τ hτ ↦ ofReal_mem_slitPlane.mpr hτ

/-- For `0 < ζ.re` and arbitrary `p : ℂ`, the transformed Schläfli–Laplace integrand
`τ ↦ e^{-ζ τ} τ^{-1/2} schlafliAmplitude p τ` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_cexp_neg_mul_cpow_neg_half_mul_schlafliAmplitude_Ioi
    {ζ : ℂ} (hζ : 0 < ζ.re) (p : ℂ) :
    IntegrableOn
      (fun τ : ℝ ↦ Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ)
      (Ioi 0) := by
  obtain ⟨B, _, hB⟩ := norm_schlafliAmplitude_ofReal_le_exp p (σ := ζ.re / 2) (by linarith)
  have hdom : Integrable (fun τ : ℝ ↦ B * (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(ζ.re / 2) * τ)))
      (volume.restrict (Ioi 0)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ)) (b := ζ.re / 2)
        (by norm_num) one_pos (by linarith)).const_mul B
  refine Integrable.mono' hdom
    ((continuousOn_schlafliLaplaceIntegrand ζ p).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hτ]
  have hexp_re : (-ζ * (τ : ℂ)).re = -ζ.re * τ := by simp
  have hpow_re : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by simp
  rw [hexp_re, hpow_re]
  calc Real.exp (-ζ.re * τ) * τ ^ (-(1 / 2 : ℝ)) * ‖schlafliAmplitude p τ‖
      ≤ Real.exp (-ζ.re * τ) * τ ^ (-(1 / 2 : ℝ)) * (B * Real.exp (ζ.re / 2 * τ)) :=
        mul_le_mul_of_nonneg_left (hB τ hτ.le) (by positivity)
    _ = B * (τ ^ (-(1 / 2 : ℝ)) * (Real.exp (-ζ.re * τ) * Real.exp (ζ.re / 2 * τ))) := by ring
    _ = B * (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(ζ.re / 2) * τ)) := by
        rw [← Real.exp_add]; congr 3; ring

/-- The Schläfli–Laplace integral `ζ ↦ ∫₀^∞ e^{-ζ τ} τ^{-1/2} schlafliAmplitude p τ dτ` is
holomorphic on the right half-plane `{ζ : ℂ | 0 < ζ.re}`. -/
theorem differentiableOn_integral_cexp_neg_mul_cpow_neg_half_mul_schlafliAmplitude_Ioi (p : ℂ) :
    DifferentiableOn ℂ
      (fun ζ : ℂ ↦ ∫ τ in Ioi (0 : ℝ),
        Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ)
      {ζ : ℂ | 0 < ζ.re} := by
  intro ζ₀ (hζ₀ : 0 < ζ₀.re)
  set δ := ζ₀.re / 4
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, _, hB⟩ := norm_schlafliAmplitude_ofReal_le_exp p hδ0
  have hre : ∀ ζ ∈ Metric.ball ζ₀ (2 * δ), 2 * δ < ζ.re := fun ζ hζ ↦ by
    have h1 := (abs_lt.mp (lt_of_le_of_lt (abs_re_le_norm (ζ - ζ₀)) (mem_ball_iff_norm.mp hζ))).1
    simp only [sub_re] at h1; dsimp [δ] at h1 ⊢; linarith
  have hbint : Integrable (fun τ : ℝ ↦ B * (τ ^ (1 / 2 : ℝ) * Real.exp (-δ * τ)))
      (volume.restrict (Ioi 0)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (1 / 2 : ℝ)) (b := δ)
        (by norm_num) one_pos hδ0).const_mul B
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun ζ (τ : ℝ) ↦ Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ)
    (F' := fun ζ (τ : ℝ) ↦
      -(τ : ℂ) * (Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ))
    (bound := fun τ : ℝ ↦ B * (τ ^ (1 / 2 : ℝ) * Real.exp (-δ * τ)))
    (Metric.ball_mem_nhds ζ₀ (show 0 < 2 * δ by positivity))
    (Eventually.of_forall fun ζ ↦
      (continuousOn_schlafliLaplaceIntegrand ζ p).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_cexp_neg_mul_cpow_neg_half_mul_schlafliAmplitude_Ioi hζ₀ p)
    ((Continuous.continuousOn (by fun_prop)).neg.mul
      (continuousOn_schlafliLaplaceIntegrand ζ₀ p) |>.aestronglyMeasurable measurableSet_Ioi)
    ?_ hbint ?_
  · exact h.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ) ζ hζ
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hτ.le, norm_mul, norm_mul,
      Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hτ]
    have hτ_pow : τ * τ ^ (-(1 / 2 : ℝ)) = τ ^ (1 / 2 : ℝ) := by
      calc τ * τ ^ (-(1 / 2 : ℝ)) = τ ^ (1 : ℝ) * τ ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = τ ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hτ]; norm_num
    rw [show (-ζ * (τ : ℂ)).re = -ζ.re * τ by simp, show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by simp]
    calc τ * (Real.exp (-ζ.re * τ) * τ ^ (-(1 / 2 : ℝ)) * ‖schlafliAmplitude p τ‖)
        = τ ^ (1 / 2 : ℝ) * Real.exp (-ζ.re * τ) * ‖schlafliAmplitude p τ‖ := by
          rw [← hτ_pow]; ring
      _ ≤ τ ^ (1 / 2 : ℝ) * Real.exp (-2 * δ * τ) * (B * Real.exp (δ * τ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
            (hB τ hτ.le) (norm_nonneg _) (by positivity)
          nlinarith [hre ζ hζ]
      _ = B * (τ ^ (1 / 2 : ℝ) * (Real.exp (-2 * δ * τ) * Real.exp (δ * τ))) := by ring
      _ = B * (τ ^ (1 / 2 : ℝ) * Real.exp (-δ * τ)) := by
          rw [← Real.exp_add]; congr 3; ring
  · filter_upwards with τ ζ _
    have hd := (((hasDerivAt_id' ζ).neg.mul_const (τ : ℂ)).cexp.mul_const
      ((τ : ℂ) ^ (-(1 / 2 : ℂ)))).mul_const (schlafliAmplitude p τ)
    exact hd.congr_deriv (by dsimp; ring)

end TauCeti
