/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.SchlafliIntegral.Amplitude
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.Complex.Sector.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# Asymptotic bounds and Laplace transformation of Schläfli's integral

Under the substitution `τ = cosh u - 1`, Schläfli's modified-Bessel / generalized-Airy integral
`∫₀^∞ e^{-ζ cosh u} cosh(p u) du` becomes the standard Laplace integral
`e^{-ζ} ∫₀^∞ e^{-ζ τ} τ^{-1/2} h_p(τ) dτ` with amplitude `h_p = TauCeti.schlafliAmplitude p`
defined in `TauCeti.Analysis.SpecialFunctions.SchlafliIntegral.Amplitude`.

This file supplies the analytic estimates and Bochner change-of-variables identities that connect
Schläfli's integral to Watson's lemma and its sectorial rotation:

1. **Subsector growth bounds:** on every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}` (`0 < δ`) of
   `Complex.slitPlane`, `‖schlafliAmplitude p w‖` grows at most like `(1 + ‖w‖) ^ (|p.re| - 1/2)`.
   Consequently `w ↦ w ^ (-1/2) * schlafliAmplitude p w` is `=O(‖w‖ ^ (|p.re| - 1))` at infinity on
   the subsector, hence bounded whenever `|p.re| ≤ 1` (covering all generalized Airy orders
   `p = 1 / (n + 2)` and `p = 1 / 2`) and `=O(exp (σ ‖w‖))` for every `σ > 0` and `p : ℂ`.
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
* `TauCeti.isBigO_cpow_neg_half_mul_schlafliAmplitude_rpow_sector`,
  `TauCeti.isBigO_cpow_neg_half_mul_schlafliAmplitude_one_sector`, and
  `TauCeti.isBigO_cpow_neg_half_mul_schlafliAmplitude_exp_sector`: polynomial, bounded (for
  `|p.re| ≤ 1`), and exponential growth bounds at infinity on closed subsectors of
  `Complex.slitPlane`.
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

/-- On every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}` (`0 < δ`), `‖schlafliAmplitude p w‖`
is bounded by an explicit constant times `(1 + ‖w‖) ^ (|p.re| - 1 / 2)`. -/
theorem norm_schlafliAmplitude_le_of_abs_arg_le (p : ℂ) {δ : ℝ} (hδ₀ : 0 < δ)
    {w : ℂ} (hw : |w.arg| ≤ Real.pi - δ) :
    ‖schlafliAmplitude p w‖ ≤
      4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2)) *
        (1 + ‖w‖) ^ (|p.re| - 1 / 2) := by
  have hδπ : δ ≤ Real.pi := by linarith [abs_nonneg w.arg]
  have hs_pos : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hw2_ge : Real.sin (δ / 2) * (1 + ‖w‖) ≤ ‖w + 2‖ := by
    have h := Complex.sin_half_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le hδ₀.le hw 2
    have hle : Real.sin (δ / 2) * (1 + ‖w‖) ≤ Real.sin (δ / 2) * (‖w‖ + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hs_pos.le
    simpa using hle.trans h
  have hden : Real.sqrt (Real.sin (δ / 2)) * (1 + ‖w‖) ^ (1 / 2 : ℝ) ≤
      ‖(w + 2) ^ (1 / 2 : ℂ)‖ := by
    have hhalf : ‖(w + 2) ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖w + 2‖ := by
      simpa [Real.sqrt_eq_rpow] using Complex.norm_cpow_real (w + 2) (1 / 2)
    rw [hhalf, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hs_pos.le]
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
          have hfour : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
          rw [hfour, ← Real.rpow_mul zero_le_two, ← Real.rpow_mul (by positivity)]
          congr 2; ring
  rw [schlafliAmplitude_def, norm_div]
  have hcosh : ‖coshMulArcosh p (1 + w)‖ ≤
      (1 + Real.sqrt (2 * ‖w‖)) ^ (2 * |p.re|) * Real.exp (Real.pi * |p.im|) := by
    simpa [add_sub_cancel_left] using norm_coshMulArcosh_le p (1 + w)
  have htop := hcosh.trans (mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le)
  calc ‖coshMulArcosh p (1 + w)‖ / ‖(w + 2) ^ (1 / 2 : ℂ)‖
      ≤ (4 ^ |p.re| * (1 + ‖w‖) ^ |p.re| * Real.exp (Real.pi * |p.im|)) /
          (Real.sqrt (Real.sin (δ / 2)) * (1 + ‖w‖) ^ (1 / 2 : ℝ)) :=
        div_le_div₀ (by positivity) htop (by positivity) hden
    _ = 4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2)) *
          ((1 + ‖w‖) ^ |p.re| / (1 + ‖w‖) ^ (1 / 2 : ℝ)) := by ring
    _ = 4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2)) *
          (1 + ‖w‖) ^ (|p.re| - 1 / 2) := by rw [← Real.rpow_sub (by positivity)]

/-- For every `p : ℂ`, `w ↦ w ^ (-1 / 2) * schlafliAmplitude p w` is `=O(‖w‖ ^ (|p.re| - 1))`
at infinity on every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}` (`0 < δ`). -/
theorem isBigO_cpow_neg_half_mul_schlafliAmplitude_rpow_sector (p : ℂ) {δ : ℝ} (hδ₀ : 0 < δ) :
    (fun w : ℂ ↦ w ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p w)
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | |w.arg| ≤ Real.pi - δ}]
      (fun w : ℂ ↦ ‖w‖ ^ (|p.re| - 1)) := by
  rcases lt_or_ge Real.pi δ with hπδ | hδπ
  · have hemp : {w : ℂ | |w.arg| ≤ Real.pi - δ} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun w hw ↦ by
        rw [mem_ofPred_eq] at hw; linarith [abs_nonneg w.arg]
    simp [hemp]
  · set C := 4 ^ |p.re| * Real.exp (Real.pi * |p.im|) / Real.sqrt (Real.sin (δ / 2))
    have hs_pos : 0 < Real.sin (δ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine IsBigO.of_bound (max (2 ^ (|p.re| - 1 / 2)) 1 * C) ?_
    filter_upwards [Filter.mem_inf_of_left (eventually_cobounded_le_norm 1),
      Filter.mem_inf_of_right (mem_principal_self _)] with w hw1 hw_sec
    have hw_pos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw1
    have hwn : ‖w ^ (-(1 / 2 : ℂ))‖ = ‖w‖ ^ (-(1 / 2 : ℝ)) := by
      simpa using Complex.norm_cpow_real w (-(1 / 2))
    have hrpow : (1 + ‖w‖) ^ (|p.re| - 1 / 2) ≤
        max (2 ^ (|p.re| - 1 / 2)) 1 * ‖w‖ ^ (|p.re| - 1 / 2) := by
      by_cases hexp : 0 ≤ |p.re| - 1 / 2
      · calc (1 + ‖w‖) ^ (|p.re| - 1 / 2)
            ≤ (2 * ‖w‖) ^ (|p.re| - 1 / 2) :=
              Real.rpow_le_rpow (by positivity) (by linarith) hexp
          _ = 2 ^ (|p.re| - 1 / 2) * ‖w‖ ^ (|p.re| - 1 / 2) :=
              Real.mul_rpow zero_le_two hw_pos.le
          _ ≤ max (2 ^ (|p.re| - 1 / 2)) 1 * ‖w‖ ^ (|p.re| - 1 / 2) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · calc (1 + ‖w‖) ^ (|p.re| - 1 / 2)
            ≤ ‖w‖ ^ (|p.re| - 1 / 2) :=
              Real.rpow_le_rpow_of_nonpos hw_pos (by linarith) (not_le.mp hexp).le
          _ = 1 * ‖w‖ ^ (|p.re| - 1 / 2) := (one_mul _).symm
          _ ≤ max (2 ^ (|p.re| - 1 / 2)) 1 * ‖w‖ ^ (|p.re| - 1 / 2) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hcombine : ‖w‖ ^ (-(1 / 2 : ℝ)) * ‖w‖ ^ (|p.re| - 1 / 2) = ‖w‖ ^ (|p.re| - 1) := by
      rw [← Real.rpow_add hw_pos]; congr 1; ring
    rw [norm_mul, hwn, Real.norm_of_nonneg (by positivity)]
    calc ‖w‖ ^ (-(1 / 2 : ℝ)) * ‖schlafliAmplitude p w‖
        ≤ ‖w‖ ^ (-(1 / 2 : ℝ)) *
            (C * (max (2 ^ (|p.re| - 1 / 2)) 1 * ‖w‖ ^ (|p.re| - 1 / 2))) :=
          mul_le_mul_of_nonneg_left
            ((norm_schlafliAmplitude_le_of_abs_arg_le p hδ₀ hw_sec).trans
              (mul_le_mul_of_nonneg_left hrpow hC)) (by positivity)
      _ = max (2 ^ (|p.re| - 1 / 2)) 1 * C *
            (‖w‖ ^ (-(1 / 2 : ℝ)) * ‖w‖ ^ (|p.re| - 1 / 2)) := by ring
      _ = max (2 ^ (|p.re| - 1 / 2)) 1 * C * ‖w‖ ^ (|p.re| - 1) := by rw [hcombine]

/-- When `|p.re| ≤ 1`, `w ↦ w ^ (-1 / 2) * schlafliAmplitude p w` is bounded near infinity on
every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}` (`0 < δ`). -/
theorem isBigO_cpow_neg_half_mul_schlafliAmplitude_one_sector {p : ℂ} (hp : |p.re| ≤ 1)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    (fun w : ℂ ↦ w ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p w)
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | |w.arg| ≤ Real.pi - δ}] (fun _ ↦ (1 : ℝ)) := by
  refine (isBigO_cpow_neg_half_mul_schlafliAmplitude_rpow_sector p hδ₀).trans
    (IsBigO.of_bound 1 ?_)
  filter_upwards [Filter.mem_inf_of_left (eventually_cobounded_le_norm 1)] with w hw1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, abs_one, one_mul]
  exact Real.rpow_le_one_of_one_le_of_nonpos hw1 (by linarith)

/-- For every `p : ℂ` and `σ > 0`, `w ↦ w ^ (-1 / 2) * schlafliAmplitude p w` is
`=O(exp (σ * ‖w‖))` at infinity on every closed subsector `{w : ℂ | |w.arg| ≤ π - δ}`
(`0 < δ`). -/
theorem isBigO_cpow_neg_half_mul_schlafliAmplitude_exp_sector (p : ℂ) {δ σ : ℝ}
    (hδ₀ : 0 < δ) (hσ : 0 < σ) :
    (fun w : ℂ ↦ w ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p w)
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | |w.arg| ≤ Real.pi - δ}]
      (fun w : ℂ ↦ Real.exp (σ * ‖w‖)) :=
  (isBigO_cpow_neg_half_mul_schlafliAmplitude_rpow_sector p hδ₀).trans
    (((isLittleO_rpow_exp_pos_mul_atTop (|p.re| - 1) hσ).isBigO.comp_tendsto
      tendsto_norm_cobounded_atTop).mono inf_le_left)

/-! ### All-order Taylor remainder bounds at `0` -/

/-- Subtracting the `N`-term Maclaurin partial sum from `schlafliAmplitude p w` leaves a
`=O[𝓝 0] (w ^ N)` remainder. -/
theorem isBigO_schlafliAmplitude_sub_sum (p : ℂ) (N : ℕ) :
    (fun w : ℂ ↦ schlafliAmplitude p w -
      ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ k) =O[𝓝 0]
      (fun w : ℂ ↦ w ^ N) := by
  simpa only [zero_add, partialSum_schlafliAmplitudeSeries, ← norm_pow, isBigO_norm_right] using
    (hasFPowerSeriesOnBall_schlafliAmplitude p).hasFPowerSeriesAt.isBigO_sub_partialSum_pow N

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
      rw [sub_eq_add_neg, cpow_add _ _ hw0, cpow_natCast]
      ring
    have hwn : ‖w ^ (-(1 / 2 : ℂ))‖ = ‖w‖ ^ (-(1 / 2 : ℝ)) := by
      simpa using Complex.norm_cpow_real w (-(1 / 2))
    rw [norm_pow] at hw
    rw [hsum_eq, ← mul_sub, norm_mul, hwn, Real.norm_eq_abs]
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
  have hsq : (Real.cosh u - 1) * (Real.cosh u + 1) = Real.sinh u ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq u]
  have hprod : Real.sqrt (Real.cosh u - 1) * Real.sqrt (Real.cosh u + 1) = Real.sinh u := by
    rw [← Real.sqrt_mul hτ_pos.le, hsq, Real.sqrt_sq hsh_pos.le]
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
`ℂ`-normed-space-valued integrand `g`. -/
theorem integrableOn_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (p : ℂ) (g : ℝ → E) :
    IntegrableOn (fun τ : ℝ ↦
      ((τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) • g τ) (Ioi 0) ↔
    IntegrableOn (fun u : ℝ ↦ Complex.cosh (p * u) • g (Real.cosh u - 1)) (Ioi 0) := by
  conv_lhs => rw [← Real.bijOn_cosh_sub_one_Ioi.image_eq]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u _ ↦ ((Real.hasDerivAt_cosh u).sub_const 1).hasDerivWithinAt)
    Real.bijOn_cosh_sub_one_Ioi.injOn]
  exact integrableOn_congr_fun (fun u hu ↦ sinh_smul_schlafliAmplitude_cosh_sub_one p g hu)
    measurableSet_Ioi

/-- Bochner change-of-variables identity `τ = cosh u - 1` on `(0, ∞)` for `schlafliAmplitude`. -/
theorem integral_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (p : ℂ) (g : ℝ → E) :
    (∫ τ in Ioi (0 : ℝ), ((τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) • g τ) =
      ∫ u in Ioi (0 : ℝ), Complex.cosh (p * u) • g (Real.cosh u - 1) := by
  conv_lhs => rw [← Real.bijOn_cosh_sub_one_Ioi.image_eq]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ ↦ ((Real.hasDerivAt_cosh u).sub_const 1).hasDerivWithinAt)
    Real.bijOn_cosh_sub_one_Ioi.injOn]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu ↦
    sinh_smul_schlafliAmplitude_cosh_sub_one p g hu

private theorem cexp_neg_mul_cosh_mul_cosh_eq (ζ p : ℂ) (u : ℝ) :
    Complex.exp (-ζ * Real.cosh u) * Complex.cosh (p * u) =
      Complex.exp (-ζ) *
        (Complex.cosh (p * u) • Complex.exp (-ζ * ((Real.cosh u - 1 : ℝ) : ℂ))) := by
  have hexp : -ζ * Real.cosh u = -ζ + -ζ * ((Real.cosh u - 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hexp, Complex.exp_add, smul_eq_mul]
  ring

/-- Equivalence of integrability between Schläfli's `cosh`-integral and its Laplace form on
`(0, ∞)`. -/
theorem integrableOn_cexp_neg_mul_cosh_mul_cosh_Ioi_iff (ζ p : ℂ) :
    IntegrableOn (fun u : ℝ ↦ Complex.exp (-ζ * Real.cosh u) * Complex.cosh (p * u)) (Ioi 0) ↔
    IntegrableOn (fun τ : ℝ ↦
      Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) (Ioi 0) := by
  have hmul :
      IntegrableOn (fun u : ℝ ↦ Complex.exp (-ζ * Real.cosh u) * Complex.cosh (p * u)) (Ioi 0) ↔
      IntegrableOn (fun u : ℝ ↦
        Complex.cosh (p * u) • Complex.exp (-ζ * ((Real.cosh u - 1 : ℝ) : ℂ))) (Ioi 0) := by
    simp_rw [cexp_neg_mul_cosh_mul_cosh_eq]
    exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Complex.exp_ne_zero (-ζ))) _
  have hτ :
      IntegrableOn (fun τ : ℝ ↦
        ((τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) • Complex.exp (-ζ * (τ : ℂ))) (Ioi 0) ↔
      IntegrableOn (fun τ : ℝ ↦
        Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ) (Ioi 0) :=
    integrableOn_congr_fun (fun τ _ ↦ by simp only [smul_eq_mul]; ring) measurableSet_Ioi
  exact hmul.trans ((integrableOn_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi_iff p
    (fun τ : ℝ ↦ Complex.exp (-ζ * τ))).symm.trans hτ)

/-- The Laplace transformation `τ = cosh u - 1` of Schläfli's integral on `(0, ∞)`:
`∫₀^∞ e^{-ζ cosh u} cosh(p u) du = e^{-ζ} ∫₀^∞ e^{-ζ τ} τ^{-1/2} schlafliAmplitude p τ dτ`. -/
theorem integral_cexp_neg_mul_cosh_mul_cosh_eq_cexp_mul_integral_schlafliAmplitude (ζ p : ℂ) :
    (∫ u in Ioi (0 : ℝ), Complex.exp (-ζ * Real.cosh u) * Complex.cosh (p * u)) =
      Complex.exp (-ζ) * ∫ τ in Ioi (0 : ℝ),
        Complex.exp (-ζ * τ) * (τ : ℂ) ^ (-(1 / 2 : ℂ)) * schlafliAmplitude p τ := by
  simp_rw [cexp_neg_mul_cosh_mul_cosh_eq]
  rw [integral_const_mul,
    ← integral_cpow_neg_half_mul_schlafliAmplitude_smul_Ioi p
      (fun τ : ℝ ↦ Complex.exp (-ζ * (τ : ℂ)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ ↦ ?_
  simp only [smul_eq_mul]
  ring

private theorem norm_schlafliAmplitude_ofReal_le_exp (p : ℂ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ B > 0, ∀ τ : ℝ, 0 ≤ τ → ‖schlafliAmplitude p τ‖ ≤ B * Real.exp (σ * τ) := by
  set C := 4 ^ |p.re| * Real.exp (Real.pi * |p.im|)
  have hC_pos : 0 < C := by dsimp [C]; positivity
  obtain ⟨M, hM0, hM⟩ := exists_rpow_mul_exp_neg_mul_le (abs_nonneg p.re) hσ
  refine ⟨C * ((M + 1) * Real.exp σ), by positivity, fun τ hτ ↦ ?_⟩
  have harg : |(τ : ℂ).arg| ≤ Real.pi - Real.pi := by
    rw [arg_ofReal_of_nonneg hτ, abs_zero, sub_self]
  have hsec := norm_schlafliAmplitude_le_of_abs_arg_le p Real.pi_pos harg
  rw [Real.sin_pi_div_two, Real.sqrt_one, div_one, Complex.norm_of_nonneg hτ] at hsec
  have hrpow : (1 + τ) ^ (|p.re| - 1 / 2) ≤ (1 + τ) ^ |p.re| :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hexp : (1 + τ) ^ |p.re| ≤ (M + 1) * Real.exp σ * Real.exp (σ * τ) := by
    have h1 := hM (1 + τ) (by linarith)
    have h2 : (1 + τ) ^ |p.re| ≤ M * Real.exp (σ * (1 + τ)) := by
      have hmul := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (σ * (1 + τ))).le
      rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
    rw [mul_add, mul_one, Real.exp_add] at h2
    calc (1 + τ) ^ |p.re| ≤ M * (Real.exp σ * Real.exp (σ * τ)) := h2
      _ ≤ (M + 1) * (Real.exp σ * Real.exp (σ * τ)) := by gcongr; linarith
      _ = (M + 1) * Real.exp σ * Real.exp (σ * τ) := by ring
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
    (Metric.ball_mem_nhds ζ₀ (mul_pos zero_lt_two hδ0))
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
    have hexp_re : (-ζ * (τ : ℂ)).re = -ζ.re * τ := by simp
    have hpow_re : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by simp
    rw [hexp_re, hpow_re]
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
