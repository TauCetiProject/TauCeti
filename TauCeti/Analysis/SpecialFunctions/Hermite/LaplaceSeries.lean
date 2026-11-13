/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import TauCeti.Analysis.SpecialFunctions.Gaussian.LaplaceIntegral

import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.MellinTransform.Growth
import TauCeti.Analysis.SpecialFunctions.Erf.Series
import TauCeti.Analysis.SpecialFunctions.Hermite.Bound
import TauCeti.RingTheory.Polynomial.Hermite.Derivative
import TauCeti.RingTheory.Polynomial.Hermite.GeneratingFunction

/-!
# The Laplace–Hermite rotational series and its endpoint limits

This file establishes convergence, Mellin-parameter holomorphy, exact summation, and radial
endpoint limits for the Laplace–Hermite series

  `∑_{m ≥ 0} r^m / m! * He_m(y) * ∫_{u > 0} u^{s + m - 1} exp(-u² / 2 - x u) du`,

which encodes the Laplace-integral core of the rotational addition formula for parabolic cylinder
functions (DLMF 12.13.5) via the Laplace representation of `U(s - 1 / 2, x)` (DLMF 12.5.1) and the
Hermite polynomial specialization `D_m(y) = exp(-y² / 4) He_m(y)`.

## Mathematical overview

1. **Half-Gamma majorant and shifted tails:** By the Gaussian Fourier moment estimate
   `TauCeti.abs_aeval_hermite_mul_exp_div_factorial_le`, each Hermite factor satisfies
   `|He_m(y)| |w|^m / m! ≤ exp(y² / 2) (|w| / √2)^m / Γ(m / 2 + 1)`.
   Summing a `2L`-shifted tail of the half-Gamma series via
   `Real.tsum_pow_add_two_mul_div_Gamma_div_two_add_one_le` near `u = 0` and the polynomial-free
   bound `Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp` for `u > 1` cancels
   `‖r‖² u² / 2` against `exp(-u² / 2)` without introducing any polynomial growth in `u`.
   Consequently, for every `M : ℕ` with `0 < s.re + M`, the `M`-shifted tail converges absolutely
   whenever `‖r‖ < 1`, whenever `‖r‖ ≤ 1` and `0 < x.re`, and at the critical case `‖r‖ ≤ 1`,
   `0 ≤ x.re`, `s.re < 0`.
2. **Holomorphy in `s`:** Uniform domination on small disks by pairs of real exponents yields
   complex differentiability of the `M`-shifted `tsum` on `{s : ℂ | 0 < s.re + M}` whenever
   `‖r‖ < 1` or `‖r‖ ≤ 1 ∧ 0 < x.re`, and on `{s : ℂ | 0 < s.re + M ∧ s.re < 0}` at the critical
   case `‖r‖ ≤ 1 ∧ 0 ≤ x.re`, enabling analytic continuation in `s` across horizontal strips.
3. **Closed form and rotational specialization:** Interchanging summation and integration via the
   exponential generating function of `Polynomial.hermite` and rescaling `v = √(1 + r²) u` sums the
   series for `0 < s.re` and `|r| < 1 ∨ (|r| ≤ 1 ∧ 0 < x.re)` to
   `(√(1 + r²))^{-s} ∫_{v > 0} v^{s - 1} exp(-v² / 2 - ((x - r y) / √(1 + r²)) v) dv`.
   Setting `r = -tan t` (`|t| < π / 4`, or `|t| ≤ π / 4` when `0 < x.re`) yields the rotated
   Gaussian–Laplace integral at `x cos t + y sin t` with prefactor `(cos t)^s`.
4. **Radial and Abel limits at the endpoint `|r| = 1`:** Because the closed form is valid for all
   `|r| < 1` and all `x : ℂ` and is continuous at `r = 1`, the radial limit as `r → 1⁻` exists
   for every `x : ℂ`, `y : ℝ`, and `0 < s.re` without sign restrictions on `x.re`. Combining this
   with Abel's limit theorem (`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`) shows that whenever
   the endpoint series at `r = -1` (`t = π / 4`) converges, its sum equals the rotated integral at
   `(x + y) / √2`.

## Main results

* `TauCeti.norm_aeval_hermite_mul_pow_div_factorial_le`: Gaussian moment bound
  `‖He_m(y) w^m / m!‖ ≤ exp(y² / 2) * ((‖w‖ / √2)^m / Γ(m / 2 + 1))`.
* `TauCeti.mul_integral_cpow_add_nat_eq_integral_mul`: pulls `r^m / m! * He_m(y)` inside the
  shifted half-line Gaussian–Laplace integral.
* `TauCeti.integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi`: integrability on `(0, ∞)` of the
  `2L`-shifted half-Gamma Laplace majorant across all three convergence regimes.
* `TauCeti.summable_integral_norm_cpow_mul_cexp_mul_hermite_add`,
  `TauCeti.summable_pow_div_factorial_mul_hermite_mul_integral_add`,
  `TauCeti.summable_pow_div_factorial_mul_hermite_mul_integral`: absolute summability of `M`-shifted
  and unshifted Laplace–Hermite series.
* `TauCeti.differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add`,
  `TauCeti.differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add_of_re_lt_zero`,
  `TauCeti.differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral`: holomorphy of the
  Laplace–Hermite `tsum` in the Mellin parameter `s`.
* `TauCeti.hasSum_pow_div_factorial_mul_hermite_mul_integral`,
  `TauCeti.hasSum_neg_tan_pow_div_factorial_mul_hermite_mul_integral`: closed-form `HasSum`
  evaluation and trigonometric rotational specialization (`r = -tan t`).
* `TauCeti.tendsto_tsum_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one`,
  `TauCeti.tendsto_tsum_neg_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one`: unrestricted
  radial endpoint limits as `r → 1⁻`.
* `TauCeti.eq_mul_integral_of_tendsto_sum_neg_one_pow_div_factorial_mul_hermite_mul_integral`,
  `TauCeti.hasSum_neg_one_pow_div_factorial_mul_hermite_mul_integral_of_summable`: endpoint
  evaluation at `r = -1` (`t = π / 4`) via Abel's limit theorem.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5(i)](https://dlmf.nist.gov/12.5.i) and
  [§12.13(ii)](https://dlmf.nist.gov/12.13.ii).
-/

public section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped Nat Topology

namespace TauCeti

/-! ### Termwise Hermite bound and integral-pullout identity -/

private theorem neg_sq_div_two_sub_eq (u : ℝ) (z : ℂ) :
    -(u : ℂ) ^ 2 / 2 - z * u = -((1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ 2 - z * u := by
  push_cast
  ring

/-- Uniform Gaussian-weighted bound on complex powers multiplied by real-argument Hermite
polynomials: `‖He_m(y) w^m / m!‖ ≤ exp(y² / 2) * ((‖w‖ / √2)^m / Γ(m / 2 + 1))`. -/
theorem norm_aeval_hermite_mul_pow_div_factorial_le (m : ℕ) (y : ℝ) (w : ℂ) :
    ‖aeval (y : ℂ) (hermite m) * w ^ m / (m ! : ℂ)‖ ≤
      rexp (y ^ 2 / 2) * ((‖w‖ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
  have heval : aeval (y : ℂ) (hermite m) = ((aeval y (hermite m) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y (hermite m)
  have hnorm : ‖aeval (y : ℂ) (hermite m) * w ^ m / (m ! : ℂ)‖ =
      |aeval y (hermite m)| * ‖w‖ ^ m / (m ! : ℝ) := by
    rw [heval, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      Complex.norm_natCast]
  have hpow : (2 : ℝ) ^ (-(m : ℝ) / 2) * ‖w‖ ^ m = (‖w‖ / √2) ^ m := by
    have hsqrt : (√2 : ℝ) ^ m = (2 : ℝ) ^ ((m : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [div_pow, hsqrt, show -(m : ℝ) / 2 = -((m : ℝ) / 2) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_mul_eq_div]
  have hb := mul_le_mul_of_nonneg_left (abs_aeval_hermite_mul_exp_div_factorial_le m y)
    (by positivity : 0 ≤ rexp (y ^ 2 / 2) * ‖w‖ ^ m)
  have hexp : rexp (y ^ 2 / 2) * rexp (-(y ^ 2) / 2) = 1 := by
    rw [← Real.exp_add, show y ^ 2 / 2 + -(y ^ 2) / 2 = 0 by ring, Real.exp_zero]
  rw [hnorm]
  calc |aeval y (hermite m)| * ‖w‖ ^ m / (m ! : ℝ)
      = (rexp (y ^ 2 / 2) * rexp (-(y ^ 2) / 2)) *
          (|aeval y (hermite m)| * ‖w‖ ^ m / (m ! : ℝ)) := by rw [hexp, one_mul]
    _ = rexp (y ^ 2 / 2) * ‖w‖ ^ m *
          (|aeval y (hermite m)| * rexp (-(y ^ 2) / 2) / (m ! : ℝ)) := by ring
    _ ≤ rexp (y ^ 2 / 2) * ‖w‖ ^ m *
          ((2 : ℝ) ^ (-(m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1)) := hb
    _ = rexp (y ^ 2 / 2) *
          (((2 : ℝ) ^ (-(m : ℝ) / 2) * ‖w‖ ^ m) / Real.Gamma ((m : ℝ) / 2 + 1)) := by ring
    _ = rexp (y ^ 2 / 2) * ((‖w‖ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by rw [hpow]

/-- Pulling `r^m / m! * He_m(y)` inside the shifted half-line Gaussian–Laplace integral turns
`u^{s + m - 1}` into `u^{s - 1} * (He_m(y) (r u)^m / m!)`. Holds unconditionally without
integrability hypotheses. -/
theorem mul_integral_cpow_add_nat_eq_integral_mul (s x r y : ℂ) (m : ℕ) :
    r ^ m / (m ! : ℂ) * aeval y (hermite m) *
        (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)) =
      ∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
          (aeval y (hermite m) * (r * u) ^ m / (m ! : ℂ)) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hcpow : (u : ℂ) ^ (s + (m : ℂ) - 1) = (u : ℂ) ^ (s - 1) * (u : ℂ) ^ m := by
    rw [show s + (m : ℂ) - 1 = (s - 1) + (m : ℂ) by ring, Complex.cpow_add _ _ hu0,
      Complex.cpow_natCast]
  rw [hcpow, mul_pow]
  ring

/-! ### Integrability of the `2L`-shifted half-Gamma Laplace majorant -/

private theorem continuous_tsum_pow_add_div_Gamma_div_two_add_one (M : ℕ) :
    Continuous fun z : ℝ => ∑' k : ℕ, z ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := by
  have heq : (fun z : ℝ => ∑' k : ℕ, z ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) =
      fun z : ℝ => rexp (z ^ 2) * (1 + TauCeti.Real.erf z) -
        ∑ m ∈ Finset.range M, z ^ m / Real.Gamma ((m : ℝ) / 2 + 1) := by
    ext z
    have hsplit := (Real.summable_pow_div_Gamma_div_two_add_one z).sum_add_tsum_nat_add M
    rw [TauCeti.Real.tsum_pow_div_Gamma_div_two_add_one] at hsplit
    linarith
  rw [heq]
  exact ((Real.continuous_exp.comp (continuous_pow 2)).mul
    (continuous_const.add TauCeti.Real.continuous_erf)).sub (by fun_prop)

private theorem integrableOn_rpow_mul_exp_neg_one_sub_sq_Ioi_one {σ x q : ℝ} (hq : 0 ≤ q)
    (hconv : q < 1 ∨ (q ≤ 1 ∧ (0 < x ∨ (0 ≤ x ∧ σ < 0)))) :
    IntegrableOn (fun u : ℝ => u ^ (σ - 1) * rexp (-((1 - q ^ 2) / 2) * u ^ 2 - x * u))
      (Ioi 1) := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => u ^ (σ - 1) * rexp (-((1 - q ^ 2) / 2) * u ^ 2 - x * u))
      (volume.restrict (Ioi 1)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  rcases hconv with hq1 | ⟨hq1, hx | ⟨hx, hσ0⟩⟩
  · have hb : 0 < (1 - q ^ 2) / 2 := by nlinarith [sq_lt_one_iff₀ hq |>.mpr hq1]
    exact integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos zero_lt_one hb (σ - 1) x
  · have hmaj := integrableOn_rpow_mul_exp_neg_mul_rpow_div (R := σ) hx zero_lt_one
    refine hmaj.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hq_sq : q ^ 2 ≤ 1 := by nlinarith
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_sub hu0, Real.rpow_one, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])) (by positivity))
      hu0.le
  · have hmaj : IntegrableOn (fun u : ℝ => u ^ (σ - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hmaj.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
    have hq_sq : q ^ 2 ≤ 1 := by nlinarith
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u]))

private theorem integrableOn_rpow_mul_exp_mul_tsum_Ioc_one {σ x q : ℝ} {L : ℕ} (hq : 0 ≤ q)
    (hσ : 0 < σ + 2 * (L : ℝ)) :
    IntegrableOn
      (fun u : ℝ =>
        u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) *
          ∑' k : ℕ, (q * u / √2) ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1))
      (Ioc 0 1) := by
  let S : ℝ → ℝ := fun u =>
    ∑' k : ℕ, (q * u / √2) ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1)
  have hS_meas : Measurable S :=
    (continuous_tsum_pow_add_div_Gamma_div_two_add_one (2 * L)).measurable.comp (by fun_prop)
  let C₀ : ℝ := 2 * (q / √2) ^ (2 * L) / (L ! : ℝ) * rexp (q ^ 2 / 2)
  have hmaj : IntegrableOn
      (fun u : ℝ => C₀ * (u ^ (σ + 2 * (L : ℝ) - 1) * rexp (-(1 / 2) * u ^ 2 - x * u)))
      (Ioc 0 1) :=
    ((integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2)
      (s := σ + 2 * (L : ℝ) - 1) (by linarith) x).mono_set Ioc_subset_Ioi_self).const_mul C₀
  refine hmaj.mono'
    ((by fun_prop : Measurable fun u : ℝ => u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u)).mul
      hS_meas).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u ⟨hu0, hu1⟩
  have hS_le : S u ≤ C₀ * u ^ (2 * L) := by
    have h1 := Real.tsum_pow_add_two_mul_div_Gamma_div_two_add_one_le (q * u / √2) L
    have hsq : (q * u / √2) ^ 2 ≤ q ^ 2 / 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have hu_sq : u ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg q]
    have hpow : (q * u / √2) ^ (2 * L) = (q / √2) ^ (2 * L) * u ^ (2 * L) := by
      rw [mul_div_right_comm, mul_pow]
    calc S u ≤ 2 * (q * u / √2) ^ (2 * L) / (L ! : ℝ) * rexp ((q * u / √2) ^ 2) := h1
      _ ≤ 2 * (q * u / √2) ^ (2 * L) / (L ! : ℝ) * rexp (q ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq) (by positivity)
      _ = C₀ * u ^ (2 * L) := by dsimp only [C₀]; rw [hpow]; ring
  have hrpow : u ^ (σ - 1) * u ^ (2 * L) = u ^ (σ + 2 * (L : ℝ) - 1) := by
    rw [← Real.rpow_natCast u (2 * L), ← Real.rpow_add hu0]
    congr 1
    push_cast
    ring
  have hS_nonneg : 0 ≤ S u :=
    tsum_nonneg fun k => div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hS_nonneg)]
  calc u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * S u
      ≤ u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * (C₀ * u ^ (2 * L)) :=
        mul_le_mul_of_nonneg_left hS_le (by positivity)
    _ = C₀ * ((u ^ (σ - 1) * u ^ (2 * L)) * rexp (-u ^ 2 / 2 - x * u)) := by ring
    _ = C₀ * (u ^ (σ + 2 * (L : ℝ) - 1) * rexp (-(1 / 2) * u ^ 2 - x * u)) := by
        rw [hrpow]
        congr 3
        ring

/-- Integrability on `(0, ∞)` of the `2L`-shifted half-Gamma Laplace majorant
`u ↦ u^{σ - 1} exp(-u² / 2 - x u) ∑_{k ≥ 0} (q u / √2)^{k + 2L} / Γ((k + 2L) / 2 + 1)`.
Near `0` the `2L`-shift contributes `O(u^{2L})`, requiring only `0 < σ + 2L`; at `∞` the
polynomial-free bound `< 2 exp(q² u² / 2)` yields integrability whenever `q < 1`, or `q ≤ 1` and
`0 < x`, or `q ≤ 1`, `0 ≤ x`, and `σ < 0`. -/
theorem integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi {σ x q : ℝ} {L : ℕ} (hq : 0 ≤ q)
    (hσ : 0 < σ + 2 * (L : ℝ)) (hconv : q < 1 ∨ (q ≤ 1 ∧ (0 < x ∨ (0 ≤ x ∧ σ < 0)))) :
    IntegrableOn
      (fun u : ℝ =>
        u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) *
          ∑' k : ℕ, (q * u / √2) ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1))
      (Ioi 0) := by
  let S : ℝ → ℝ := fun u =>
    ∑' k : ℕ, (q * u / √2) ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1)
  have hS_meas : Measurable S :=
    (continuous_tsum_pow_add_div_Gamma_div_two_add_one (2 * L)).measurable.comp (by fun_prop)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union (integrableOn_rpow_mul_exp_mul_tsum_Ioc_one hq hσ) ?_
  have hmaj := (integrableOn_rpow_mul_exp_neg_one_sub_sq_Ioi_one hq hconv).const_mul 2
  refine hmaj.mono'
    ((by fun_prop : Measurable fun u : ℝ => u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u)).mul
      hS_meas).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
  have hS_le : S u ≤ 2 * rexp (q ^ 2 / 2 * u ^ 2) := by
    have h1 := (Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp
      (q * u / √2) (2 * L)).le
    have hsq : (q * u / √2) ^ 2 = q ^ 2 / 2 * u ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rwa [hsq] at h1
  have hS_nonneg : 0 ≤ S u :=
    tsum_nonneg fun k => div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hS_nonneg)]
  calc u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * S u
      ≤ u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * (2 * rexp (q ^ 2 / 2 * u ^ 2)) :=
        mul_le_mul_of_nonneg_left hS_le (by positivity)
    _ = 2 * (u ^ (σ - 1) * (rexp (-u ^ 2 / 2 - x * u) * rexp (q ^ 2 / 2 * u ^ 2))) := by ring
    _ = 2 * (u ^ (σ - 1) * rexp (-((1 - q ^ 2) / 2) * u ^ 2 - x * u)) := by
        rw [← Real.exp_add]
        congr 3
        ring

/-! ### Shifted-tail absolute summability -/

private noncomputable def majorantTerm (σ x q y : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  rexp (y ^ 2 / 2) *
    (u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) *
      ((q * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)))

private theorem norm_integrand_le_majorantTerm (s x r : ℂ) (y : ℝ) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
        (aeval (y : ℂ) (hermite m) * (r * u) ^ m / (m ! : ℂ))‖ ≤
      majorantTerm s.re x.re ‖r‖ y m u := by
  have h1 : ‖(u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)‖ =
      u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - x.re * u) := by
    have hre : (-(u : ℂ) ^ 2 / 2 - x * u).re = -u ^ 2 / 2 - x.re * u := by
      simp [sq]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp, hre]
    simp
  have h2 := norm_aeval_hermite_mul_pow_div_factorial_le m y (r * u)
  rw [norm_mul r, Complex.norm_real, Real.norm_of_nonneg hu.le] at h2
  rw [norm_mul, h1]
  calc (u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - x.re * u)) *
        ‖aeval (y : ℂ) (hermite m) * (r * u) ^ m / (m ! : ℂ)‖
      ≤ (u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - x.re * u)) *
          (rexp (y ^ 2 / 2) * ((‖r‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = majorantTerm s.re x.re ‖r‖ y m u := by
        unfold majorantTerm
        ring

private theorem integrableOn_majorantTerm {σ : ℝ} {m : ℕ} (hσ : 0 < σ + (m : ℝ)) (x q y : ℝ) :
    IntegrableOn (majorantTerm σ x q y m) (Ioi 0) := by
  let C₁ : ℝ := rexp (y ^ 2 / 2) * ((q / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))
  have hmaj : IntegrableOn
      (fun u : ℝ => C₁ * (u ^ (σ + (m : ℝ) - 1) * rexp (-(1 / 2) * u ^ 2 - x * u))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2)
      (s := σ + (m : ℝ) - 1) (by linarith) x).const_mul C₁
  refine IntegrableOn.congr_fun hmaj ?_ measurableSet_Ioi
  intro u (hu : 0 < u)
  have hrpow : u ^ (σ + (m : ℝ) - 1) = u ^ (σ - 1) * u ^ m := by
    rw [show σ + (m : ℝ) - 1 = (σ - 1) + (m : ℝ) by ring, Real.rpow_add hu, Real.rpow_natCast]
  have hexp : -(1 / 2 : ℝ) * u ^ 2 - x * u = -u ^ 2 / 2 - x * u := by ring
  unfold majorantTerm
  dsimp [C₁]
  rw [hrpow, hexp, mul_div_right_comm q u, mul_pow]
  ring

private theorem summable_integral_majorantTerm_two_mul {σ x q : ℝ} (y : ℝ) (L : ℕ) (hq : 0 ≤ q)
    (hσ : 0 < σ + 2 * (L : ℝ)) (hconv : q < 1 ∨ (q ≤ 1 ∧ (0 < x ∨ (0 ≤ x ∧ σ < 0)))) :
    Summable fun k : ℕ => ∫ u in Ioi (0 : ℝ), majorantTerm σ x q y (k + 2 * L) u := by
  let S : ℝ → ℝ := fun u =>
    rexp (y ^ 2 / 2) *
      (u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) *
        ∑' k : ℕ, (q * u / √2) ^ (k + 2 * L) / Real.Gamma ((↑(k + 2 * L) : ℝ) / 2 + 1))
  have hhas : HasSum (fun k : ℕ => ∫ u in Ioi (0 : ℝ), majorantTerm σ x q y (k + 2 * L) u)
      (∫ u in Ioi (0 : ℝ), S u) := by
    refine hasSum_integral_of_dominated_convergence
      (fun k u => majorantTerm σ x q y (k + 2 * L) u)
      (fun k => Measurable.aestronglyMeasurable (by unfold majorantTerm; fun_prop))
      (fun k => ?_) ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      exact le_of_eq (Real.norm_of_nonneg (by
        unfold majorantTerm
        exact mul_nonneg (by positivity)
          (mul_nonneg (by positivity)
            (div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le))))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      exact (((summable_nat_add_iff (2 * L)).2
        (Real.summable_pow_div_Gamma_div_two_add_one (q * u / √2))).mul_left _).mul_left _
    · refine IntegrableOn.congr_fun
        ((integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi hq hσ hconv).const_mul
          (rexp (y ^ 2 / 2))) ?_ measurableSet_Ioi
      intro u _
      unfold majorantTerm
      dsimp only []
      rw [tsum_mul_left, tsum_mul_left]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      exact (((((summable_nat_add_iff (2 * L)).2
        (Real.summable_pow_div_Gamma_div_two_add_one (q * u / √2))).hasSum).mul_left _).mul_left _)
  exact hhas.summable

/-- For every `M : ℕ` with `0 < s.re + M`, the `L¹`-norms of the `M`-shifted Laplace–Hermite
integrands on `(0, ∞)` form a summable series whenever `‖r‖ < 1`, or `‖r‖ ≤ 1` and `0 < x.re`, or
`‖r‖ ≤ 1`, `0 ≤ x.re`, and `s.re < 0`. -/
theorem summable_integral_norm_cpow_mul_cexp_mul_hermite_add {s : ℂ} (M : ℕ) (x r : ℂ) (y : ℝ)
    (hs : 0 < s.re + (M : ℝ))
    (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0)))) :
    Summable fun k : ℕ =>
      ∫ u in Ioi (0 : ℝ),
        ‖(u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
          (aeval (y : ℂ) (hermite (k + M)) * (r * u) ^ (k + M) / ((k + M)! : ℂ))‖ := by
  rw [← summable_nat_add_iff M]
  have hmaj := summable_integral_majorantTerm_two_mul y M (norm_nonneg r) (by linarith) hconv
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
    hmaj
  have hk : k + M + M = k + 2 * M := by omega
  rw [hk]
  have hint_norm : IntegrableOn
      (fun u : ℝ =>
        ‖(u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
          (aeval (y : ℂ) (hermite (k + 2 * M)) * (r * u) ^ (k + 2 * M) / ((k + 2 * M)! : ℂ))‖)
      (Ioi 0) := by
    refine (integrableOn_majorantTerm (σ := s.re) (m := k + 2 * M)
      (by push_cast; linarith) x.re ‖r‖ y).mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_integrand_le_majorantTerm s x r y (k + 2 * M) hu
  refine setIntegral_mono_on hint_norm
    (integrableOn_majorantTerm (by push_cast; linarith) x.re ‖r‖ y) measurableSet_Ioi
    fun u hu => norm_integrand_le_majorantTerm s x r y (k + 2 * M) hu

/-- Absolute summability of the `M`-shifted Laplace–Hermite series for any `M : ℕ` with
`0 < s.re + M`, covering all interior parameters `‖r‖ < 1` as well as the critical circle `‖r‖ = 1`
when `0 < x.re` or when `0 ≤ x.re` and `s.re < 0`. -/
theorem summable_pow_div_factorial_mul_hermite_mul_integral_add {s : ℂ} (M : ℕ) (x r : ℂ) (y : ℝ)
    (hs : 0 < s.re + (M : ℝ))
    (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0)))) :
    Summable fun k : ℕ =>
      r ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s + ((k + M : ℕ) : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
  refine Summable.of_norm_bounded
    (summable_integral_norm_cpow_mul_cexp_mul_hermite_add M x r y hs hconv) fun k => ?_
  rw [mul_integral_cpow_add_nat_eq_integral_mul]
  exact norm_integral_le_integral_norm _

/-- Unshifted (`M = 0`) summability of the Laplace–Hermite series on the open right half-plane
`0 < s.re` whenever `‖r‖ < 1` or `‖r‖ ≤ 1 ∧ 0 < x.re`. -/
theorem summable_pow_div_factorial_mul_hermite_mul_integral {s : ℂ} (hs : 0 < s.re) (x r : ℂ)
    (y : ℝ) (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < x.re)) :
    Summable fun m : ℕ =>
      r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
  have hconv' : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0))) :=
    hconv.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩
  simpa using summable_pow_div_factorial_mul_hermite_mul_integral_add 0 x r y (by simpa using hs)
    hconv'

/-! ### Complex differentiability in the Mellin parameter `s` -/

private theorem rpow_le_add_rpow_of_mem_Icc {u p p₁ p₂ : ℝ} (hu : 0 < u) (hp₁ : p₁ ≤ p)
    (hp₂ : p ≤ p₂) : u ^ p ≤ u ^ p₁ + u ^ p₂ := by
  rcases le_total u 1 with hu1 | hu1
  · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_ge hu hu1 hp₁) (by positivity)
  · exact le_add_of_nonneg_of_le (by positivity) (Real.rpow_le_rpow_of_exponent_le hu1 hp₂)

private theorem differentiableOn_term_add (m : ℕ) (x r : ℂ) (y : ℝ) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      {s : ℂ | 0 < s.re + (m : ℝ)} := by
  have hint : DifferentiableOn ℂ
      (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      {w : ℂ | 0 < w.re} := by
    simpa only [neg_sq_div_two_sub_eq] using
      differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi
        (b := 1 / 2) (by norm_num) x
  have hcomp : DifferentiableOn ℂ
      (fun s : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      {s : ℂ | 0 < s.re + (m : ℝ)} :=
    hint.comp (differentiable_id.add (differentiable_const (m : ℂ))).differentiableOn
      fun s hs => by simpa using hs
  exact hcomp.const_mul (r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m))

private theorem norm_term_le_integral_majorantTerm_add {s : ℂ} {σ₁ σ₂ : ℝ} (m : ℕ) (x r : ℂ)
    (y : ℝ) (hσ₁ : 0 < σ₁ + (m : ℝ)) (hσ₂ : 0 < σ₂ + (m : ℝ)) (hs₁ : σ₁ ≤ s.re)
    (hs₂ : s.re ≤ σ₂) :
    ‖r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)‖ ≤
      (∫ u in Ioi (0 : ℝ), majorantTerm σ₁ x.re ‖r‖ y m u) +
        ∫ u in Ioi (0 : ℝ), majorantTerm σ₂ x.re ‖r‖ y m u := by
  have hint₁ := integrableOn_majorantTerm hσ₁ x.re ‖r‖ y
  have hint₂ := integrableOn_majorantTerm hσ₂ x.re ‖r‖ y
  rw [mul_integral_cpow_add_nat_eq_integral_mul, ← integral_add hint₁ hint₂]
  refine norm_integral_le_of_norm_le (hint₁.add hint₂) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  refine (norm_integrand_le_majorantTerm s x r y m hu).trans ?_
  have hrpow := rpow_le_add_rpow_of_mem_Icc hu (p := s.re - 1) (p₁ := σ₁ - 1) (p₂ := σ₂ - 1)
    (by linarith) (by linarith)
  unfold majorantTerm
  calc rexp (y ^ 2 / 2) *
        (u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - x.re * u) *
          ((‖r‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)))
      ≤ rexp (y ^ 2 / 2) *
        ((u ^ (σ₁ - 1) + u ^ (σ₂ - 1)) * rexp (-u ^ 2 / 2 - x.re * u) *
          ((‖r‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) := by gcongr
    _ = rexp (y ^ 2 / 2) *
          (u ^ (σ₁ - 1) * rexp (-u ^ 2 / 2 - x.re * u) *
            ((‖r‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) +
        rexp (y ^ 2 / 2) *
          (u ^ (σ₂ - 1) * rexp (-u ^ 2 / 2 - x.re * u) *
            ((‖r‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) := by ring

private theorem differentiableAt_tsum_add_of_ball (M : ℕ) (x r : ℂ) (y : ℝ) {s₀ : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hσ₁ : 0 < s₀.re - δ + (M : ℝ))
    (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s₀.re + δ < 0)))) :
    DifferentiableAt ℂ
      (fun s : ℂ =>
        ∑' k : ℕ,
          r ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (s + ((k + M : ℕ) : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      s₀ := by
  let term : ℕ → ℂ → ℂ := fun m s =>
    r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + (m : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)
  let σ₁ : ℝ := s₀.re - δ
  let σ₂ : ℝ := s₀.re + δ
  have hconv₁ : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ σ₁ < 0))) :=
    hconv.imp_right fun ⟨h1, h2⟩ =>
      ⟨h1, h2.imp_right fun ⟨h3, _⟩ => ⟨h3, by dsimp [σ₁]; linarith⟩⟩
  have hball : ∀ {s : ℂ}, s ∈ Metric.ball s₀ δ → σ₁ < s.re ∧ s.re < σ₂ := fun {s} hs => by
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hre := lt_of_le_of_lt (Complex.abs_re_le_norm (s - s₀)) hs
    rw [Complex.sub_re] at hre
    exact ⟨by dsimp [σ₁]; linarith [(abs_lt.mp hre).1],
      by dsimp [σ₂]; linarith [(abs_lt.mp hre).2]⟩
  have hu_sum : Summable fun k : ℕ =>
      (∫ u in Ioi (0 : ℝ), majorantTerm σ₁ x.re ‖r‖ y (k + 2 * M) u) +
        ∫ u in Ioi (0 : ℝ), majorantTerm σ₂ x.re ‖r‖ y (k + 2 * M) u :=
    (summable_integral_majorantTerm_two_mul y M (norm_nonneg r) (by dsimp [σ₁]; linarith)
      hconv₁).add
      (summable_integral_majorantTerm_two_mul y M (norm_nonneg r) (by dsimp [σ₂]; linarith) hconv)
  have htail : DifferentiableOn ℂ (fun s : ℂ => ∑' k : ℕ, term (k + 2 * M) s)
      (Metric.ball s₀ δ) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu_sum
      (fun k => (differentiableOn_term_add (k + 2 * M) x r y).mono fun s hs => ?_)
      Metric.isOpen_ball (fun k s hs => ?_)
    · have h1 := (hball hs).1
      have : 0 < s.re + ((k + 2 * M : ℕ) : ℝ) := by push_cast; dsimp [σ₁] at h1; linarith
      exact this
    · obtain ⟨hs₁, hs₂⟩ := hball hs
      exact norm_term_le_integral_majorantTerm_add (k + 2 * M) x r y
        (by push_cast; dsimp [σ₁]; linarith) (by push_cast; dsimp [σ₂]; linarith) hs₁.le hs₂.le
  have hhead : DifferentiableOn ℂ (fun s : ℂ => ∑ j ∈ Finset.range M, term (j + M) s)
      (Metric.ball s₀ δ) :=
    DifferentiableOn.fun_sum fun j _ =>
      (differentiableOn_term_add (j + M) x r y).mono fun s hs => by
        have h1 := (hball hs).1
        have : 0 < s.re + ((j + M : ℕ) : ℝ) := by push_cast; dsimp [σ₁] at h1; linarith
        exact this
  have hsplit : EqOn (fun s : ℂ => ∑' k : ℕ, term (k + M) s)
      (fun s : ℂ => (∑ j ∈ Finset.range M, term (j + M) s) + ∑' k : ℕ, term (k + 2 * M) s)
      (Metric.ball s₀ δ) := fun s hs => by
    obtain ⟨hs₁, hs₂⟩ := hball hs
    have hconv_s : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0))) :=
      hconv.imp_right fun ⟨h1, h2⟩ => ⟨h1, h2.imp_right fun ⟨h3, h4⟩ => ⟨h3, hs₂.trans h4⟩⟩
    have hsum_s : Summable fun k : ℕ => term (k + M) s :=
      summable_pow_div_factorial_mul_hermite_mul_integral_add M x r y
        (by dsimp [σ₁] at hs₁; linarith) hconv_s
    have hk : (fun k : ℕ => term (k + M + M) s) = fun k : ℕ => term (k + 2 * M) s := by
      ext k; rw [show k + M + M = k + 2 * M by omega]
    dsimp only []
    rw [← hsum_s.sum_add_tsum_nat_add M, hk]
  exact ((hhead.add htail).congr hsplit).differentiableAt (Metric.ball_mem_nhds s₀ hδ)

/-- For every `M : ℕ`, `x : ℂ`, `y : ℝ`, and `r : ℂ` with `‖r‖ < 1` (or `‖r‖ ≤ 1` when `0 < x.re`),
the `M`-shifted Laplace–Hermite `tsum` defines a holomorphic function of `s` on the open half-plane
`{s : ℂ | 0 < s.re + M}`. -/
theorem differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add (M : ℕ) (x : ℂ)
    {r : ℂ} (y : ℝ) (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < x.re)) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        ∑' k : ℕ,
          r ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (s + ((k + M : ℕ) : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      {s : ℂ | 0 < s.re + (M : ℝ)} := by
  intro s₀ (hs₀ : 0 < s₀.re + (M : ℝ))
  exact (differentiableAt_tsum_add_of_ball M x r y (δ := (s₀.re + (M : ℝ)) / 2) (half_pos hs₀)
    (by linarith) (hconv.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩)).differentiableWithinAt

/-- At the critical circle `‖r‖ ≤ 1` with `0 ≤ x.re` (including `x = 0`), the `M`-shifted
Laplace–Hermite `tsum` is holomorphic on the open vertical strip
`{s : ℂ | 0 < s.re + M ∧ s.re < 0}`. -/
theorem differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add_of_re_lt_zero (M : ℕ)
    {x r : ℂ} (y : ℝ) (hr : ‖r‖ ≤ 1) (hx : 0 ≤ x.re) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        ∑' k : ℕ,
          r ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (s + ((k + M : ℕ) : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      {s : ℂ | 0 < s.re + (M : ℝ) ∧ s.re < 0} := by
  rintro s₀ ⟨hs₀M : 0 < s₀.re + (M : ℝ), hs₀0 : s₀.re < 0⟩
  let δ : ℝ := min ((s₀.re + (M : ℝ)) / 2) (-s₀.re / 2)
  have hδ : 0 < δ := lt_min (half_pos hs₀M) (by linarith)
  have hσ₁ : 0 < s₀.re - δ + (M : ℝ) := by
    linarith [min_le_left ((s₀.re + (M : ℝ)) / 2) (-s₀.re / 2)]
  have hσ₂ : s₀.re + δ < 0 := by
    linarith [min_le_right ((s₀.re + (M : ℝ)) / 2) (-s₀.re / 2)]
  exact (differentiableAt_tsum_add_of_ball M x r y hδ hσ₁
    (Or.inr ⟨hr, Or.inr ⟨hx, hσ₂⟩⟩)).differentiableWithinAt

/-- Unshifted (`M = 0`) holomorphy of the Laplace–Hermite `tsum` on the open right half-plane
`{s : ℂ | 0 < s.re}` whenever `‖r‖ < 1` or `‖r‖ ≤ 1 ∧ 0 < x.re`. -/
theorem differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral (x : ℂ) {r : ℂ} (y : ℝ)
    (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < x.re)) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        ∑' m : ℕ,
          r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      {s : ℂ | 0 < s.re} := by
  simpa using differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add 0 x y hconv

/-! ### Exact `HasSum` evaluation and rotational specialization -/

/-- Closed-form `HasSum` evaluation of the Laplace–Hermite series: for `0 < s.re`, `x : ℂ`,
`y r : ℝ`, and `|r| < 1` (or `|r| ≤ 1` when `0 < x.re`), the series sums to the rotated and
rescaled Gaussian–Laplace integral at `(x - r y) / √(1 + r²)`. -/
theorem hasSum_pow_div_factorial_mul_hermite_mul_integral {s : ℂ} (hs : 0 < s.re) (x : ℂ) (y : ℝ)
    {r : ℝ} (hr : |r| < 1 ∨ (|r| ≤ 1 ∧ 0 < x.re)) :
    HasSum
      (fun m : ℕ =>
        (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) *
            cexp (-(v : ℂ) ^ 2 / 2 - ((x - r * y) / Real.sqrt (1 + r ^ 2)) * v)) := by
  let c : ℝ := Real.sqrt (1 + r ^ 2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc_sq : c ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
  let F : ℕ → ℝ → ℂ := fun m u =>
    (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
      (aeval (y : ℂ) (hermite m) * ((r : ℂ) * u) ^ m / (m ! : ℂ))
  let f : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (s - 1) * cexp (-((1 / 2 * c ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ 2 - (x - r * y) * u)
  have hr' : |r| < 1 ∨ (|r| ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0))) :=
    hr.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩
  have hdom : HasSum (fun m : ℕ => ∫ u in Ioi (0 : ℝ), F m u) (∫ u in Ioi (0 : ℝ), f u) := by
    refine hasSum_integral_of_dominated_convergence (majorantTerm s.re x.re |r| y)
      (fun m => Measurable.aestronglyMeasurable (by dsimp only [F]; fun_prop))
      (fun m => ?_) ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      simpa [F, Complex.norm_real, Real.norm_eq_abs] using
        norm_integrand_le_majorantTerm s x (r : ℂ) y m hu
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      exact ((Real.summable_pow_div_Gamma_div_two_add_one (|r| * u / √2)).mul_left _).mul_left _
    · refine IntegrableOn.congr_fun
        ((integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi (L := 0) (abs_nonneg r)
          (by simpa using hs) hr').const_mul (rexp (y ^ 2 / 2))) ?_ measurableSet_Ioi
      intro u _
      unfold majorantTerm
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [tsum_mul_left, tsum_mul_left]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      have hgen := (Polynomial.hasSum_hermite_generating_function (y : ℂ) ((r : ℂ) * u)).mul_left
        ((u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      have hf_eq : (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
          cexp ((y : ℂ) * ((r : ℂ) * u) - ((r : ℂ) * u) ^ 2 / 2) = f u := by
        dsimp only [f]
        rw [mul_assoc, ← Complex.exp_add]
        refine congrArg (fun w => (u : ℂ) ^ (s - 1) * cexp w) ?_
        rw [hc_sq]
        push_cast
        ring
      exact hf_eq ▸ hgen
  have hscale := integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi hc (1 / 2) s (x - r * y)
  have htarget : ∫ u in Ioi (0 : ℝ), f u =
      (c : ℂ) ^ (-s) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - ((x - r * y) / c) * v) := by
    rw [hscale]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [neg_sq_div_two_sub_eq]
  rw [← htarget]
  exact hdom.congr_fun fun m => mul_integral_cpow_add_nat_eq_integral_mul s x (r : ℂ) (y : ℂ) m

private theorem inv_ofReal_cpow_neg {c : ℝ} (hc : 0 < c) (s : ℂ) :
    ((c⁻¹ : ℝ) : ℂ) ^ (-s) = (c : ℂ) ^ s := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcinv0 : ((c⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_pos.mpr hc).ne'
  rw [Complex.cpow_def_of_ne_zero hcinv0, Complex.cpow_def_of_ne_zero hc0,
    ← Complex.ofReal_log (inv_nonneg.mpr hc.le), Real.log_inv, Complex.ofReal_neg,
    Complex.ofReal_log hc.le, neg_mul_neg]

/-- Trigonometric form of the Laplace–Hermite rotational identity (the Laplace core of DLMF
12.13.5): for `0 < s.re`, `x : ℂ`, `y : ℝ`, and `|t| < π / 4` (or `|t| ≤ π / 4` when `0 < x.re`),
setting `r = -tan t` evaluates the series to `(cos t)^s` times the Gaussian–Laplace integral at the
rotated argument `x cos t + y sin t`. -/
theorem hasSum_neg_tan_pow_div_factorial_mul_hermite_mul_integral {s : ℂ} (hs : 0 < s.re) (x : ℂ)
    (y : ℝ) {t : ℝ} (ht : |t| < π / 4 ∨ (|t| ≤ π / 4 ∧ 0 < x.re)) :
    HasSum
      (fun m : ℕ =>
        ((-Real.tan t : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      ((Real.cos t : ℂ) ^ s *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) *
            cexp (-(v : ℂ) ^ 2 / 2 - (x * Real.cos t + y * Real.sin t) * v)) := by
  have ht_le : |t| ≤ π / 4 := ht.elim le_of_lt And.left
  have ht_Ioo : t ∈ Ioo (-(π / 2)) (π / 2) := by
    obtain ⟨h1, h2⟩ := abs_le.mp ht_le
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hpi4_Ioo : π / 4 ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hnpi4_Ioo : -(π / 4) ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht_Ioo
  have htan : |-Real.tan t| < 1 ∨ (|-Real.tan t| ≤ 1 ∧ 0 < x.re) := by
    rw [abs_neg]
    rcases ht with hlt | ⟨hle, hx⟩
    · obtain ⟨h1, h2⟩ := abs_lt.mp hlt
      refine Or.inl (abs_lt.mpr ⟨?_, ?_⟩)
      · have h := Real.strictMonoOn_tan hnpi4_Ioo ht_Ioo h1
        rwa [Real.tan_neg, Real.tan_pi_div_four] at h
      · have h := Real.strictMonoOn_tan ht_Ioo hpi4_Ioo h2
        rwa [Real.tan_pi_div_four] at h
    · obtain ⟨h1, h2⟩ := abs_le.mp hle
      refine Or.inr ⟨abs_le.mpr ⟨?_, ?_⟩, hx⟩
      · have h := Real.strictMonoOn_tan.monotoneOn hnpi4_Ioo ht_Ioo h1
        rwa [Real.tan_neg, Real.tan_pi_div_four] at h
      · have h := Real.strictMonoOn_tan.monotoneOn ht_Ioo hpi4_Ioo h2
        rwa [Real.tan_pi_div_four] at h
  have hsum := hasSum_pow_div_factorial_mul_hermite_mul_integral hs x y htan
  have hsqrt : Real.sqrt (1 + (-Real.tan t) ^ 2) = (Real.cos t)⁻¹ := by
    rw [neg_sq, ← inv_inv (Real.sqrt (1 + Real.tan t ^ 2)), Real.inv_sqrt_one_add_tan_sq hcos]
  have harg : (x - ((-Real.tan t : ℝ) : ℂ) * (y : ℂ)) / ((Real.cos t)⁻¹ : ℝ) =
      x * Real.cos t + y * Real.sin t := by
    have hcos0 : (Real.cos t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_inv]
    field_simp
    ring
  rw [hsqrt, inv_ofReal_cpow_neg hcos s, harg] at hsum
  exact hsum

/-! ### Radial limit as `r → 1⁻` and conditional endpoint evaluation via Abel's theorem -/

/-- Unrestricted radial limit as `r → 1⁻` for the Laplace–Hermite series: for every `0 < s.re`,
`x : ℂ`, and `y : ℝ` (with no restriction on `x.re`), the interior sum converges as `r → 1⁻` to
`(√2)^{-s}` times the Gaussian–Laplace integral at `(x - y) / √2`. -/
theorem tendsto_tsum_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one {s : ℂ} (hs : 0 < s.re)
    (x : ℂ) (y : ℝ) :
    Tendsto
      (fun r : ℝ =>
        ∑' m : ℕ,
          (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      (𝓝[<] 1)
      (𝓝 ((Real.sqrt 2 : ℂ) ^ (-s) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - ((x - y) / Real.sqrt 2) * v))) := by
  let I : ℂ → ℂ := fun z =>
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - z * v)
  have hI_cont : Continuous I := by
    have hdiff : Differentiable ℂ I := by
      simpa only [I, neg_sq_div_two_sub_eq] using
        differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi
          (b := 1 / 2) (by norm_num) hs
    exact hdiff.continuous
  let g : ℝ → ℂ := fun r =>
    (Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) * I ((x - r * y) / Real.sqrt (1 + r ^ 2))
  have hcpow_cont : Continuous fun r : ℝ => (Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) := by
    refine Continuous.cpow
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop)))
      continuous_const fun r =>
      Complex.ofReal_mem_slitPlane.mpr (Real.sqrt_pos.mpr (by positivity))
  have harg_cont : Continuous fun r : ℝ => (x - r * y) / (Real.sqrt (1 + r ^ 2) : ℂ) := by
    refine Continuous.div (by fun_prop)
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop))) fun r =>
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hg_cont : Continuous g := hcpow_cont.mul (hI_cont.comp harg_cont)
  have hg1 : g 1 = (Real.sqrt 2 : ℂ) ^ (-s) * I ((x - y) / Real.sqrt 2) := by
    dsimp [g]
    norm_num
  have htend : Tendsto g (𝓝[<] 1) (𝓝 (g 1)) := (hg_cont.tendsto 1).mono_left nhdsWithin_le_nhds
  rw [hg1] at htend
  refine htend.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
  exact
    (hasSum_pow_div_factorial_mul_hermite_mul_integral hs x y (Or.inl (abs_lt.mpr hr))).tsum_eq.symm

/-- Radial endpoint limit corresponding to `t → (π / 4)⁻` (`-tan t = -r` with `r → 1⁻`): for every
`0 < s.re`, `x : ℂ`, and `y : ℝ`, multiplying the `t = π / 4` summand by `r^m` and letting `r → 1⁻`
converges to `(√2)^{-s}` times the Gaussian–Laplace integral at `(x + y) / √2`. -/
theorem tendsto_tsum_neg_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one {s : ℂ}
    (hs : 0 < s.re) (x : ℂ) (y : ℝ) :
    Tendsto
      (fun r : ℝ =>
        ∑' m : ℕ,
          ((-r : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      (𝓝[<] 1)
      (𝓝 ((Real.sqrt 2 : ℂ) ^ (-s) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - ((x + y) / Real.sqrt 2) * v))) := by
  have h := tendsto_tsum_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one hs x (-y)
  have harg : (x - ((-y : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ) = (x + y) / Real.sqrt 2 := by
    push_cast
    ring
  rw [harg] at h
  refine h.congr fun r => tsum_congr fun m => ?_
  have hpar : aeval ((-y : ℝ) : ℂ) (hermite m) = (-1 : ℂ) ^ m * aeval (y : ℂ) (hermite m) := by
    rw [Complex.ofReal_neg, Polynomial.hermite_aeval_neg]
  have hpow : ((-r : ℝ) : ℂ) ^ m = (-1 : ℂ) ^ m * (r : ℂ) ^ m := by
    rw [Complex.ofReal_neg, neg_eq_neg_one_mul, mul_pow]
  rw [hpar, hpow]
  ring

/-- By Abel's limit theorem and the unrestricted radial limit, whenever the partial sums of the
`t = π / 4` (`r = -1`) Laplace–Hermite series converge to `L` (including conditional convergence at
`x.re ≤ 0`), `L` equals `(√2)^{-s}` times the Gaussian–Laplace integral at `(x + y) / √2`. -/
theorem eq_mul_integral_of_tendsto_sum_neg_one_pow_div_factorial_mul_hermite_mul_integral {s : ℂ}
    (hs : 0 < s.re) {x : ℂ} {y : ℝ} {L : ℂ}
    (hL : Tendsto
      (fun N : ℕ =>
        ∑ m ∈ Finset.range N,
          (-1 : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      atTop (𝓝 L)) :
    L = (Real.sqrt 2 : ℂ) ^ (-s) *
      ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - ((x + y) / Real.sqrt 2) * v) := by
  have habel := tendsto_map'_iff.mp (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL)
  have habel' : Tendsto
      (fun r : ℝ =>
        ∑' m : ℕ,
          ((-r : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      (𝓝[<] 1) (𝓝 L) := by
    refine habel.congr fun r => tsum_congr fun m => ?_
    have hpow : (-1 : ℂ) ^ m * (r : ℂ) ^ m = ((-r : ℝ) : ℂ) ^ m := by
      rw [← mul_pow, neg_one_mul, Complex.ofReal_neg]
    calc (-1 : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)) *
            (r : ℂ) ^ m
        = ((-1 : ℂ) ^ m * (r : ℂ) ^ m) / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
          ring
      _ = ((-r : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
          rw [hpow]
  exact tendsto_nhds_unique habel'
    (tendsto_tsum_neg_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one hs x y)

/-- Whenever the `t = π / 4` (`r = -1`) Laplace–Hermite series is `Summable` for `0 < s.re`, its
sum is `(√2)^{-s}` times the Gaussian–Laplace integral at `(x + y) / √2`. -/
theorem hasSum_neg_one_pow_div_factorial_mul_hermite_mul_integral_of_summable {s : ℂ}
    (hs : 0 < s.re) {x : ℂ} {y : ℝ}
    (hsum : Summable fun m : ℕ =>
      (-1 : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)) :
    HasSum
      (fun m : ℕ =>
        (-1 : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      ((Real.sqrt 2 : ℂ) ^ (-s) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - ((x + y) / Real.sqrt 2) * v)) := by
  have heq := eq_mul_integral_of_tendsto_sum_neg_one_pow_div_factorial_mul_hermite_mul_integral hs
    hsum.hasSum.tendsto_sum_nat
  exact heq ▸ hsum.hasSum

end TauCeti
