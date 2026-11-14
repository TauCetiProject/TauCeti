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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Erf.Series
import TauCeti.Analysis.SpecialFunctions.Hermite.Bound
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.RingTheory.Polynomial.Hermite.GeneratingFunction

/-!
# The Laplace–Hermite rotational series and its endpoint limits

This file establishes convergence, Mellin-parameter holomorphy, exact summation, and radial
endpoint limits for the Laplace–Hermite series

  `∑_{m ≥ 0} r^m / m! * He_m(y) * ∫_{u > 0} u^{s + m - 1} exp(-u² / 2 - x u) du`

for Mellin exponent `s : ℂ`, Laplace parameter `x : ℂ`, real Hermite argument `y : ℝ`, and
expansion ratio `r : ℂ` (for absolute convergence and holomorphy in `s`) or `r : ℝ` (for closed-form
summation and radial/Abel endpoint limits). This series encodes the Laplace-integral core of the
rotational addition formula for parabolic cylinder functions (DLMF 12.13.5) via the Laplace
representation of `U(s - 1 / 2, x)` (DLMF 12.5.1) and the Hermite polynomial specialization
`D_m(y) = exp(-y² / 4) He_m(y)`.

## Mathematical overview

1. **Half-Gamma majorant and shifted tails:** For `y : ℝ` and `w : ℂ`, the Gaussian Fourier moment
   estimate `TauCeti.norm_aeval_hermite_mul_pow_div_factorial_le` (derived from
   `TauCeti.abs_aeval_hermite_mul_exp_div_factorial_le`) gives
   `‖He_m(y) w^m / m!‖ ≤ exp(y² / 2) * ((‖w‖ / √2)^m / Γ(m / 2 + 1))`.
   Bounding `(u : ℝ)^{k + M} ≤ u^M` on `(0, 1]` and applying the polynomial-free bound
   `Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp` cancels `‖r‖² u² / 2` against
   `exp(-u² / 2)` without introducing polynomial growth in `u`. Consequently, for every `M : ℕ`,
   `s, x, r : ℂ` with `0 < s.re + M`, and `y : ℝ`, the `M`-shifted tail converges absolutely
   whenever `‖r‖ < 1`, whenever `‖r‖ ≤ 1` and `0 < x.re`, and at the critical case `‖r‖ ≤ 1`,
   `0 ≤ x.re`, `s.re < 0`.
2. **Holomorphy in `s`:** Uniform domination on small disks by pairs of real exponents yields
   complex differentiability of the `M`-shifted `tsum` on `{s : ℂ | 0 < s.re + M}` whenever
   `‖r‖ < 1` or `‖r‖ ≤ 1 ∧ 0 < x.re`, and on `{s : ℂ | 0 < s.re + M ∧ s.re < 0}` at the critical
   case `‖r‖ ≤ 1 ∧ 0 ≤ x.re`, enabling analytic continuation in `s` across vertical strips.
3. **Closed form and rotational specialization:** Interchanging summation and integration via the
   exponential generating function of `Polynomial.hermite` and rescaling `v = √(1 + r²) u` sums the
   series for `0 < s.re`, `x : ℂ`, `y, r : ℝ`, and `|r| < 1 ∨ (|r| ≤ 1 ∧ 0 < x.re)` to
   `(√(1 + r²))^{-s} ∫_{v > 0} v^{s - 1} exp(-v² / 2 - ((x - r y) / √(1 + r²)) v) dv`.
   Setting `r = -tan t` (`|t| < π / 4`, or `|t| ≤ π / 4` when `0 < x.re`) yields the rotated
   Gaussian–Laplace integral at `x cos t + y sin t` with prefactor `(cos t)^s`.
4. **Radial and Abel limits on `|r| ≤ 1`:** Because the closed form holds on `|r * t| < 1` for
   `t ∈ (0, 1)` and all `x : ℂ` whenever `|r| ≤ 1` and is continuous at `t = 1`, the radial limit
   as `t → 1⁻` exists for every `x : ℂ`, `y : ℝ`, `|r| ≤ 1`, and `0 < s.re` without sign
   restrictions on `x.re`. Combining this with Abel's limit theorem
   (`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`) shows that whenever the series at any
   `|r| ≤ 1` (including the endpoints `r = ∓1`, i.e. `t = ±π / 4`) converges, its sum equals the
   rotated integral at `(x - r y) / √(1 + r²)`.

## Main results

* `TauCeti.mul_integral_cpow_add_nat_eq_integral_mul`: pulls `r^m / m! * He_m(y)` inside the
  shifted half-line Gaussian–Laplace integral.
* `TauCeti.integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi`: integrability on `(0, ∞)` of the
  `M`-shifted half-Gamma Laplace majorant across all three convergence regimes.
* `TauCeti.summable_integral_norm_cpow_mul_cexp_mul_hermite_add`,
  `TauCeti.summable_pow_div_factorial_mul_hermite_mul_integral_add`,
  `TauCeti.summable_pow_div_factorial_mul_hermite_mul_integral`: absolute summability of `M`-shifted
  and unshifted Laplace–Hermite series.
* `TauCeti.differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add`,
  `TauCeti.differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral`: holomorphy of the
  `M`-shifted and unshifted Laplace–Hermite `tsum` in the Mellin parameter `s`.
* `TauCeti.differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add_re_neg_of_re_nonneg`
  (strip holomorphy on `{s : ℂ | 0 < s.re + M ∧ s.re < 0}` when `‖r‖ ≤ 1` and `0 ≤ x.re`).
* `TauCeti.hasSum_pow_div_factorial_mul_hermite_mul_integral`,
  `TauCeti.hasSum_neg_tan_pow_div_factorial_mul_hermite_mul_integral`: closed-form `HasSum`
  evaluation and trigonometric rotational specialization (`r = -tan t`).
* `TauCeti.tendsto_tsum_mul_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one`: unrestricted
  radial limit as `t → 1⁻` for any `|r| ≤ 1`.
* `TauCeti.eq_mul_integral_of_tendsto_sum_pow_div_factorial_mul_hermite_mul_integral`,
  `TauCeti.hasSum_pow_div_factorial_mul_hermite_mul_integral_of_summable`: conditional and
  summable evaluation on `|r| ≤ 1` via Abel's limit theorem.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5(i)](https://dlmf.nist.gov/12.5.i) and
  [§12.13(ii)](https://dlmf.nist.gov/12.13.ii).
-/

public section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped Nat Topology

namespace TauCeti

/-! ### Integral-pullout identity -/

private theorem neg_sq_div_two_sub_eq (u : ℝ) (z : ℂ) :
    -(u : ℂ) ^ 2 / 2 - z * u = -(1 / 2 : ℂ) * (u : ℂ) ^ 2 - z * u := by
  ring

/-- Pulling `r^m / m! * He_m(y)` inside the shifted half-line Gaussian–Laplace integral turns
`u^{s + m - 1}` into `u^{s - 1} * (He_m(y) (r u)^m / m!)` for all `s x r y : ℂ` and `m : ℕ`. -/
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

/-! ### Integrability of the `M`-shifted half-Gamma Laplace majorant -/

/-- For `0 < σ + M`, the `M`-shifted half-Gamma Laplace majorant
`u ↦ u^{σ - 1} exp(-u² / 2 - x u) ∑_{k ≥ 0} (q u / √2)^{k + M} / Γ((k + M) / 2 + 1)` is integrable
on `(0, ∞)` whenever `|q| < 1`, or `|q| ≤ 1` and `0 < x`, or `|q| ≤ 1`, `0 ≤ x`, and `σ < 0`. -/
theorem integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi {σ x q : ℝ} {M : ℕ}
    (hσ : 0 < σ + (M : ℝ)) (hconv : |q| < 1 ∨ (|q| ≤ 1 ∧ (0 < x ∨ (0 ≤ x ∧ σ < 0)))) :
    IntegrableOn
      (fun u : ℝ =>
        u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) *
          ∑' k : ℕ, (q * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1))
      (Ioi 0) := by
  let S : ℝ → ℝ := fun u =>
    ∑' k : ℕ, (q * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)
  let S_abs : ℝ → ℝ := fun u =>
    ∑' k : ℕ, (|q| * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)
  have hmeas : Measurable fun u : ℝ => u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * S u :=
    (by fun_prop : Measurable fun u : ℝ => u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u)).mul
      ((Real.continuous_tsum_pow_add_div_Gamma_div_two_add_one M).measurable.comp (by fun_prop))
  have hS_norm : ∀ {u : ℝ}, 0 < u → ‖S u‖ ≤ S_abs u := fun {u} hu => by
    have hterm_norm :
        (fun k : ℕ => ‖(q * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)‖) =
          fun k : ℕ => (|q| * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := by
      ext k
      rw [norm_div, norm_pow, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hu,
        abs_of_pos (Real.sqrt_pos.mpr zero_lt_two),
        Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le]
    have hsum_norm :
        Summable fun k : ℕ => ‖(q * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)‖ := by
      rw [hterm_norm]
      exact (summable_nat_add_iff M).2 (Real.summable_pow_div_Gamma_div_two_add_one (|q| * u / √2))
    simpa only [S, S_abs, hterm_norm] using norm_tsum_le_tsum_norm hsum_norm
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · let C₀ : ℝ := 2 * rexp (q ^ 2 / 2)
    have hmaj : IntegrableOn
        (fun u : ℝ => C₀ * (u ^ (σ + (M : ℝ) - 1) * rexp (-(1 / 2) * u ^ 2 - x * u)))
        (Ioc 0 1) :=
      ((integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2)
        (s := σ + (M : ℝ) - 1) (by linarith) x).mono_set Ioc_subset_Ioi_self).const_mul C₀
    refine hmaj.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u ⟨hu0, hu1⟩
    have hS_le : S_abs u ≤ C₀ * u ^ M := by
      have hterm : ∀ k : ℕ,
          (|q| * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) ≤
            u ^ M * ((|q| / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) := fun k => by
        have hpow : (|q| * u / √2) ^ (k + M) ≤ u ^ M * (|q| / √2) ^ (k + M) := by
          rw [mul_div_right_comm, mul_pow, pow_add u k M, mul_comm (u ^ k)]
          calc (|q| / √2) ^ (k + M) * (u ^ M * u ^ k)
              ≤ (|q| / √2) ^ (k + M) * (u ^ M * 1) := by
                gcongr
                exact pow_le_one₀ hu0.le hu1
            _ = u ^ M * (|q| / √2) ^ (k + M) := by ring
        calc (|q| * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)
            ≤ (u ^ M * (|q| / √2) ^ (k + M)) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
              div_le_div_of_nonneg_right hpow (Real.Gamma_pos_of_pos (by positivity)).le
          _ = u ^ M * ((|q| / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) :=
              mul_div_assoc _ _ _
      have hsum₁ : Summable fun k : ℕ =>
          (|q| * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
        (summable_nat_add_iff M).2 (Real.summable_pow_div_Gamma_div_two_add_one (|q| * u / √2))
      have hsum₂ : Summable fun k : ℕ =>
          u ^ M * ((|q| / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) :=
        ((summable_nat_add_iff M).2
          (Real.summable_pow_div_Gamma_div_two_add_one (|q| / √2))).mul_left (u ^ M)
      have hsq : (|q| / √2) ^ 2 = q ^ 2 / 2 := by
        rw [div_pow, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      calc S_abs u
          ≤ ∑' k : ℕ, u ^ M * ((|q| / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) :=
            hsum₁.tsum_le_tsum hterm hsum₂
        _ = u ^ M * ∑' k : ℕ, (|q| / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
            tsum_mul_left
        _ ≤ u ^ M * (2 * rexp ((|q| / √2) ^ 2)) := by
            gcongr
            exact (Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (|q| / √2) M).le
        _ = C₀ * u ^ M := by dsimp only [C₀]; rw [hsq]; ring
    have hrpow : u ^ (σ - 1) * u ^ M = u ^ (σ + (M : ℝ) - 1) := by
      rw [← Real.rpow_natCast u M, ← Real.rpow_add hu0]
      congr 1
      ring
    rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    calc u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * ‖S u‖
        ≤ u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * (C₀ * u ^ M) :=
          mul_le_mul_of_nonneg_left ((hS_norm hu0).trans hS_le) (by positivity)
      _ = C₀ * ((u ^ (σ - 1) * u ^ M) * rexp (-u ^ 2 / 2 - x * u)) := by ring
      _ = C₀ * (u ^ (σ + (M : ℝ) - 1) * rexp (-(1 / 2) * u ^ 2 - x * u)) := by
          rw [hrpow]
          congr 3
          ring
  · have htail : IntegrableOn
        (fun u : ℝ => u ^ (σ - 1) * rexp (-((1 - q ^ 2) / 2) * u ^ 2 - x * u)) (Ioi 1) := by
      rcases hconv with hq1 | ⟨hq1, hx⟩
      · have hq_sq : q ^ 2 < 1 := by
          rw [← sq_abs]
          exact (sq_lt_one_iff₀ (abs_nonneg q)).mpr hq1
        exact integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos zero_lt_one (by linarith)
          (σ - 1) x
      · have hq_sq : q ^ 2 ≤ 1 := by
          rw [← sq_abs]
          nlinarith [abs_nonneg q]
        exact integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_nonneg zero_lt_one (by linarith)
          (hx.imp_right fun ⟨hx0, _⟩ => ⟨hx0, by linarith⟩)
    refine (htail.const_mul 2).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 1 < u)
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hS_le : S_abs u ≤ 2 * rexp (q ^ 2 / 2 * u ^ 2) := by
      have h1 := (Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp
        (|q| * u / √2) M).le
      have hsq : (|q| * u / √2) ^ 2 = q ^ 2 / 2 * u ^ 2 := by
        rw [div_pow, mul_pow, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rwa [hsq] at h1
    rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    calc u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * ‖S u‖
        ≤ u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) * (2 * rexp (q ^ 2 / 2 * u ^ 2)) :=
          mul_le_mul_of_nonneg_left ((hS_norm hu0).trans hS_le) (by positivity)
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
    rw [neg_sq_div_two_sub_eq, norm_cpow_mul_cexp_neg_mul_sq_sub_mul (1 / 2) s x hu]
    congr 2
    norm_num
    ring
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

private theorem summable_integral_majorantTerm_add {σ x q : ℝ} (y : ℝ) (M : ℕ) (hq : 0 ≤ q)
    (hσ : 0 < σ + (M : ℝ)) (hconv : |q| < 1 ∨ (|q| ≤ 1 ∧ (0 < x ∨ (0 ≤ x ∧ σ < 0)))) :
    Summable fun k : ℕ => ∫ u in Ioi (0 : ℝ), majorantTerm σ x q y (k + M) u := by
  let S : ℝ → ℝ := fun u =>
    rexp (y ^ 2 / 2) *
      (u ^ (σ - 1) * rexp (-u ^ 2 / 2 - x * u) *
        ∑' k : ℕ, (q * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1))
  have hhas : HasSum (fun k : ℕ => ∫ u in Ioi (0 : ℝ), majorantTerm σ x q y (k + M) u)
      (∫ u in Ioi (0 : ℝ), S u) := by
    refine hasSum_integral_of_dominated_convergence
      (fun k u => majorantTerm σ x q y (k + M) u)
      (fun k => Measurable.aestronglyMeasurable (by unfold majorantTerm; fun_prop))
      (fun k => ?_) ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      exact le_of_eq (Real.norm_of_nonneg (by
        unfold majorantTerm
        exact mul_nonneg (by positivity)
          (mul_nonneg (by positivity)
            (div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le))))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      exact (((summable_nat_add_iff M).2
        (Real.summable_pow_div_Gamma_div_two_add_one (q * u / √2))).mul_left _).mul_left _
    · refine IntegrableOn.congr_fun
        ((integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi hσ hconv).const_mul
          (rexp (y ^ 2 / 2))) ?_ measurableSet_Ioi
      intro u _
      unfold majorantTerm
      dsimp only []
      rw [tsum_mul_left, tsum_mul_left]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      exact (((((summable_nat_add_iff M).2
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
  have hconv' : |‖r‖| < 1 ∨ (|‖r‖| ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0))) := by
    rwa [abs_of_nonneg (norm_nonneg r)]
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
    (summable_integral_majorantTerm_add y M (norm_nonneg r) hs hconv')
  have hint_norm : IntegrableOn
      (fun u : ℝ =>
        ‖(u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
          (aeval (y : ℂ) (hermite (k + M)) * (r * u) ^ (k + M) / ((k + M)! : ℂ))‖)
      (Ioi 0) := by
    refine (integrableOn_majorantTerm (σ := s.re) (m := k + M)
      (by push_cast; linarith) x.re ‖r‖ y).mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_integrand_le_majorantTerm s x r y (k + M) hu
  exact setIntegral_mono_on hint_norm
    (integrableOn_majorantTerm (by push_cast; linarith) x.re ‖r‖ y) measurableSet_Ioi
    fun u hu => norm_integrand_le_majorantTerm s x r y (k + M) hu

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
        (b := (1 / 2 : ℂ)) (by norm_num) x
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
  have hrpow := Real.rpow_le_add_rpow_of_mem_Icc hu (p := s.re - 1) (p₁ := σ₁ - 1) (p₂ := σ₂ - 1)
    ⟨by linarith, by linarith⟩
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
  let σ₁ : ℝ := s₀.re - δ
  let σ₂ : ℝ := s₀.re + δ
  have hconv₂ : |‖r‖| < 1 ∨ (|‖r‖| ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ σ₂ < 0))) := by
    rwa [abs_of_nonneg (norm_nonneg r)]
  have hconv₁ : |‖r‖| < 1 ∨ (|‖r‖| ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ σ₁ < 0))) :=
    hconv₂.imp_right fun ⟨h1, h2⟩ =>
      ⟨h1, h2.imp_right fun ⟨h3, _⟩ => ⟨h3, by dsimp [σ₁]; linarith⟩⟩
  have hball : ∀ {s : ℂ}, s ∈ Metric.ball s₀ δ → σ₁ < s.re ∧ s.re < σ₂ := fun {s} hs => by
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hre := lt_of_le_of_lt (Complex.abs_re_le_norm (s - s₀)) hs
    rw [Complex.sub_re] at hre
    exact ⟨by dsimp [σ₁]; linarith [(abs_lt.mp hre).1],
      by dsimp [σ₂]; linarith [(abs_lt.mp hre).2]⟩
  have hu_sum : Summable fun k : ℕ =>
      (∫ u in Ioi (0 : ℝ), majorantTerm σ₁ x.re ‖r‖ y (k + M) u) +
        ∫ u in Ioi (0 : ℝ), majorantTerm σ₂ x.re ‖r‖ y (k + M) u :=
    (summable_integral_majorantTerm_add y M (norm_nonneg r) (by dsimp [σ₁]; linarith) hconv₁).add
      (summable_integral_majorantTerm_add y M (norm_nonneg r) (by dsimp [σ₂]; linarith) hconv₂)
  have hdiff : DifferentiableOn ℂ
      (fun s : ℂ =>
        ∑' k : ℕ,
          r ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (s + ((k + M : ℕ) : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      (Metric.ball s₀ δ) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu_sum
      (fun k => (differentiableOn_term_add (k + M) x r y).mono fun s hs => ?_)
      Metric.isOpen_ball (fun k s hs => ?_)
    · have h1 := (hball hs).1
      have : 0 < s.re + ((k + M : ℕ) : ℝ) := by push_cast; dsimp [σ₁] at h1; linarith
      exact this
    · obtain ⟨hs₁, hs₂⟩ := hball hs
      exact norm_term_le_integral_majorantTerm_add (k + M) x r y
        (by push_cast; dsimp [σ₁]; linarith) (by push_cast; dsimp [σ₂]; linarith) hs₁.le hs₂.le
  exact hdiff.differentiableAt (Metric.ball_mem_nhds s₀ hδ)

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

/-- For `‖r‖ ≤ 1` and `0 ≤ x.re` (including `x = 0`), the `M`-shifted Laplace–Hermite `tsum` is
holomorphic on the open vertical strip `{s : ℂ | 0 < s.re + M ∧ s.re < 0}`. -/
theorem differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add_re_neg_of_re_nonneg
    (M : ℕ) {x r : ℂ} (y : ℝ) (hr : ‖r‖ ≤ 1) (hx : 0 ≤ x.re) :
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
    (u : ℂ) ^ (s - 1) * cexp (-((1 / 2 : ℂ) * (c : ℂ) ^ 2) * (u : ℂ) ^ 2 - (x - r * y) * u)
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
        ((integrableOn_rpow_mul_exp_mul_tsum_pow_div_Gamma_Ioi (q := |r|) (M := 0)
          (by simpa using hs) (by rwa [abs_abs])).const_mul
          (rexp (y ^ 2 / 2))) ?_ measurableSet_Ioi
      intro u _
      unfold majorantTerm
      simp only [Nat.add_zero]
      rw [tsum_mul_left, tsum_mul_left]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      have hgen := (Polynomial.hasSum_hermite_generating_function (y : ℂ) ((r : ℂ) * u)).mul_left
        ((u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      have hf_eq : (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) *
          cexp ((y : ℂ) * ((r : ℂ) * u) - ((r : ℂ) * u) ^ 2 / 2) = f u := by
        dsimp only [f]
        rw [mul_assoc, ← Complex.exp_add]
        refine congrArg (fun w => (u : ℂ) ^ (s - 1) * cexp w) ?_
        have hc_sq' : (c : ℂ) ^ 2 = ((1 + r ^ 2 : ℝ) : ℂ) := by exact_mod_cast hc_sq
        rw [hc_sq']
        push_cast
        ring
      exact hf_eq ▸ hgen
  have hscale := integral_cpow_mul_cexp_neg_mul_sq_mul_sq_sub_mul_Ioi_eq_cpow_mul_integral hc
    (1 / 2) s (x - r * y)
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
  rw [hsqrt, harg, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hcos.le, Complex.cpow_neg,
    inv_inv] at hsum
  exact hsum

/-! ### Radial limit as `t → 1⁻` and conditional endpoint evaluation via Abel's theorem -/

/-- Unrestricted radial limit as `t → 1⁻` for the Laplace–Hermite series: for every `0 < s.re`,
`x : ℂ`, `y : ℝ`, and `|r| ≤ 1` (with no restriction on `x.re`), the damped series with ratio
`r * t` converges as `t → 1⁻` to `(√(1 + r²))^{-s}` times the Gaussian–Laplace integral at
`(x - r y) / √(1 + r²)`. -/
theorem tendsto_tsum_mul_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one {s : ℂ}
    (hs : 0 < s.re) (x : ℂ) (y : ℝ) {r : ℝ} (hr : |r| ≤ 1) :
    Tendsto
      (fun t : ℝ =>
        ∑' m : ℕ,
          ((r * t : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      (𝓝[<] 1)
      (𝓝 ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) *
            cexp (-(v : ℂ) ^ 2 / 2 - ((x - r * y) / Real.sqrt (1 + r ^ 2)) * v))) := by
  let I : ℂ → ℂ := fun z =>
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - z * v)
  have hI_cont : Continuous I := by
    have hdiff : Differentiable ℂ I := by
      simpa only [I, neg_sq_div_two_sub_eq] using
        differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi
          (b := (1 / 2 : ℂ)) (by norm_num) hs
    exact hdiff.continuous
  let g : ℝ → ℂ := fun t =>
    (Real.sqrt (1 + (r * t) ^ 2) : ℂ) ^ (-s) *
      I ((x - ((r * t : ℝ) : ℂ) * y) / Real.sqrt (1 + (r * t) ^ 2))
  have hcpow_cont : Continuous fun t : ℝ => (Real.sqrt (1 + (r * t) ^ 2) : ℂ) ^ (-s) := by
    refine Continuous.cpow
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop)))
      continuous_const fun t =>
      Complex.ofReal_mem_slitPlane.mpr (Real.sqrt_pos.mpr (by positivity))
  have harg_cont :
      Continuous fun t : ℝ =>
        (x - ((r * t : ℝ) : ℂ) * y) / (Real.sqrt (1 + (r * t) ^ 2) : ℂ) := by
    refine Continuous.div (by fun_prop)
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop))) fun t =>
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hg_cont : Continuous g := hcpow_cont.mul (hI_cont.comp harg_cont)
  have hg1 : g 1 = (Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) *
      I ((x - r * y) / Real.sqrt (1 + r ^ 2)) := by
    dsimp [g]
    simp
  have htend : Tendsto g (𝓝[<] 1) (𝓝 (g 1)) := (hg_cont.tendsto 1).mono_left nhdsWithin_le_nhds
  rw [hg1] at htend
  refine htend.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ⟨ht0, ht1⟩
  have hrt : |r * t| < 1 := by
    rw [abs_mul, abs_of_pos ht0]
    exact lt_of_le_of_lt (mul_le_of_le_one_left ht0.le hr) ht1
  exact (hasSum_pow_div_factorial_mul_hermite_mul_integral hs x y (Or.inl hrt)).tsum_eq.symm

/-- For `0 < s.re`, `x : ℂ`, `y : ℝ`, and `|r| ≤ 1`, whenever the partial sums of the
Laplace–Hermite series converge to `L` (including conditional convergence on `|r| = 1` with
`x.re ≤ 0`), `L` equals `(√(1 + r²))^{-s}` times the Gaussian–Laplace integral at
`(x - r y) / √(1 + r²)`. -/
theorem eq_mul_integral_of_tendsto_sum_pow_div_factorial_mul_hermite_mul_integral {s : ℂ}
    (hs : 0 < s.re) {x : ℂ} {y r : ℝ} (hr : |r| ≤ 1) {L : ℂ}
    (hL : Tendsto
      (fun N : ℕ =>
        ∑ m ∈ Finset.range N,
          (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      atTop (𝓝 L)) :
    L = (Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) *
      ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (s - 1) *
          cexp (-(v : ℂ) ^ 2 / 2 - ((x - r * y) / Real.sqrt (1 + r ^ 2)) * v) := by
  have habel := tendsto_map'_iff.mp (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL)
  have habel' : Tendsto
      (fun t : ℝ =>
        ∑' m : ℕ,
          ((r * t : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      (𝓝[<] 1) (𝓝 L) := by
    refine habel.congr fun t => tsum_congr fun m => ?_
    have hpow : (r : ℂ) ^ m * (t : ℂ) ^ m = ((r * t : ℝ) : ℂ) ^ m := by
      rw [← mul_pow, Complex.ofReal_mul]
    calc (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)) *
            (t : ℂ) ^ m
        = ((r : ℂ) ^ m * (t : ℂ) ^ m) / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
          ring
      _ = ((r * t : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
          rw [hpow]
  exact tendsto_nhds_unique habel'
    (tendsto_tsum_mul_pow_div_factorial_mul_hermite_mul_integral_nhdsLT_one hs x y hr)

/-- Whenever the Laplace–Hermite series is `Summable` for `0 < s.re` and `|r| ≤ 1`, its sum is
`(√(1 + r²))^{-s}` times the Gaussian–Laplace integral at `(x - r y) / √(1 + r²)`. -/
theorem hasSum_pow_div_factorial_mul_hermite_mul_integral_of_summable {s : ℂ}
    (hs : 0 < s.re) {x : ℂ} {y r : ℝ} (hr : |r| ≤ 1)
    (hsum : Summable fun m : ℕ =>
      (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)) :
    HasSum
      (fun m : ℕ =>
        (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
      ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (s - 1) *
            cexp (-(v : ℂ) ^ 2 / 2 - ((x - r * y) / Real.sqrt (1 + r ^ 2)) * v)) := by
  have heq := eq_mul_integral_of_tendsto_sum_pow_div_factorial_mul_hermite_mul_integral hs hr
    hsum.hasSum.tendsto_sum_nat
  exact heq ▸ hsum.hasSum

end TauCeti
