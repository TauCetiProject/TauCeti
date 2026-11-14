/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Erf.Series
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.MellinLaplace
import TauCeti.Analysis.SpecialFunctions.Hermite.Bound
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.RingTheory.Polynomial.Hermite.GeneratingFunction

/-!
# Hermite–Mellin–Gaussian–Laplace series and rotational rescaling

Pairing the exponential generating function of the probabilists' Hermite polynomials
`∑_{m ≥ 0} He_m(y) (-r u)^m / m! = exp (-y r u - r² u² / 2)` with the half-line
Mellin–Gaussian–Laplace kernel `u ^ (b - 1) exp (-u² / 2 - z u)` and interchanging sum and integral
yields the series-integral identity

  `∑_{m ≥ 0} (-r)^m / m! · He_m(y) ∫₀^∞ u^{b + m - 1} exp (-u² / 2 - z u) du`
    `= (1 + r²)^{-b / 2} ∫₀^∞ v^{b - 1} exp (-v² / 2 - (z + r y) / √(1 + r²) · v) dv`

for `Re b > 0` and real `r` with `|r| < 1` (or `|r| ≤ 1` and `Re z > 0`). Setting `r = tan t` for
`|t| < π / 4` (or `|t| ≤ π / 4` and `Re z > 0`) turns `(1 + tan² t)^{-b / 2}` into `(cos t)^b` and
`(z + y tan t) / √(1 + tan² t)` into the rotated argument `z cos t + y sin t`, while multiplying by
`(b)_m / Γ(b + m) = 1 / Γ(b)` supplies the Gamma-normalized Laplace kernel of Tricomi's parabolic
cylinder function `U(b - 1 / 2, ·)` (DLMF 12.5.1 and 12.13.5).

Two analytic ingredients make this valid up to the boundary `|r| = 1` (`|t| = π / 4`) and across
all complex parameter half-planes `0 < Re b + M`:

1. Combining the Gaussian moment bound `|He_m(y)| / m! ≤ exp(y² / 2) 2^{-m / 2} / Γ(m / 2 + 1)`
   with the polynomial-free half-Gamma series majorant `< 2 exp(x²)` (DLMF 7.6.3) bounds every
   `M`-shifted tail of the Hermite generating series on `(1, ∞)` by `< 2 exp(y² / 2 + ‖r‖² u² / 2)`
   with *no* polynomial factor in `u`. At `‖r‖ = 1` this cancels `exp(-u² / 2)` exactly, leaving
   `u^{Re b - 1} exp(-Re z · u)` on `(1, ∞)`, which is integrable whenever `Re z > 0`, or
   `Re z ≥ 0` and `Re b < 0`. On `(0, 1]`, the vanishing-order bound `O(u^M)` makes the `M`-shifted
   tail integrable whenever `0 < Re b + M`.
2. For `Re b > 0` and *arbitrary* `z : ℂ` (including `Re z ≤ 0`, where the boundary series at
   `r = 1` need not converge), continuity of the closed-form right-hand side in `r` yields the
   endpoint evaluation as an Abel limit as `r → 1⁻`. Meanwhile, on any half-plane `0 < Re b + M`,
   the `M`-shifted tail is locally uniformly summable on balls and hence holomorphic in `b`.

## Main results

* `TauCeti.norm_aeval_hermite_mul_pow_div_factorial_le`,
  `TauCeti.tsum_norm_aeval_hermite_mul_pow_div_factorial_add_lt`,
  `TauCeti.tsum_norm_aeval_hermite_mul_pow_div_factorial_add_le`: termwise and `M`-shifted tail
  Gaussian majorants for the Hermite generating series.
* `TauCeti.summable_hermite_add_mul_integral_rpow_exp_Ioi`,
  `TauCeti.summable_norm_hermite_add_mul_integral_cpow_cexp_Ioi`,
  `TauCeti.summable_norm_ascPochhammer_hermite_add_mul_inv_Gamma_integral_cpow_cexp_Ioi`:
  absolute convergence of `M`-shifted Hermite–Laplace series tails on `0 < Re b + M` for `‖r‖ < 1`,
  at the boundary `‖r‖ ≤ 1` when `0 < Re z` or `0 ≤ Re z ∧ Re b < 0`, and unconditionally at
  terminating parameters `b = -n`.
* `TauCeti.hasSum_hermite_mul_integral_cpow_cexp_Ioi_eq_integral`,
  `TauCeti.hasSum_hermite_mul_integral_cpow_cexp_Ioi`,
  `TauCeti.hasSum_ascPochhammer_hermite_mul_inv_Gamma_integral_cpow_cexp_Ioi`,
  `TauCeti.hasSum_ascPochhammer_hermite_tan_mul_inv_Gamma_integral_cpow_cexp_Ioi`: closed-form
  `HasSum` evaluations for complex `r`, real `r`, Pochhammer–Gamma normalization, and rotational
  angle `r = tan t`.
* `TauCeti.tendsto_tsum_hermite_mul_integral_cpow_cexp_Ioi_nhdsLT_one`,
  `TauCeti.tendsto_tsum_ascPochhammer_hermite_mul_inv_Gamma_integral_cpow_cexp_Ioi_nhdsLT_one`:
  Abel limit as `r → 1⁻` for `0 < b.re` and arbitrary `z : ℂ`, `y : ℝ`.
* `TauCeti.differentiableOn_tsum_hermite_add_mul_integral_cpow_cexp_Ioi`,
  `TauCeti.differentiableOn_tsum_ascPochhammer_hermite_add_mul_inv_Gamma_integral_cpow_cexp_Ioi`:
  holomorphy in `b` of the `M`-shifted tails on `{b : ℂ | 0 < b.re + M}` whenever
  `‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)`.

## References

* *NIST Digital Library of Mathematical Functions*, [§7.6](https://dlmf.nist.gov/7.6),
  [§12.5](https://dlmf.nist.gov/12.5), [§12.13](https://dlmf.nist.gov/12.13), and
  [§18.12](https://dlmf.nist.gov/18.12).
-/

public section

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology Real

namespace TauCeti

/-! ### Gaussian and vanishing-order bounds for the Hermite generating series -/

/-- Each term of the probabilists' Hermite exponential generating series at real `y` and complex
`w` is bounded in norm by `exp(y² / 2) (‖w‖ / √2)^m / Γ(m / 2 + 1)`. -/
theorem norm_aeval_hermite_mul_pow_div_factorial_le (m : ℕ) (y : ℝ) (w : ℂ) :
    ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * w ^ m / m.factorial‖ ≤
      Real.exp (y ^ 2 / 2) * ((‖w‖ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
  have heval : Polynomial.aeval (y : ℂ) (Polynomial.hermite m) =
      ((Polynomial.aeval y (Polynomial.hermite m) : ℝ) : ℂ) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y _
  have hb := abs_aeval_hermite_mul_exp_div_factorial_le m y
  have hsqrt : (2 : ℝ) ^ (-(m : ℝ) / 2) * √2 ^ m = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
      ← Real.rpow_add zero_lt_two]
    have hexp : -(m : ℝ) / 2 + 1 / 2 * (m : ℝ) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hpow : (2 : ℝ) ^ (-(m : ℝ) / 2) * ‖w‖ ^ m = (‖w‖ / √2) ^ m := by
    rw [div_pow, eq_div_iff (by positivity)]
    calc (2 : ℝ) ^ (-(m : ℝ) / 2) * ‖w‖ ^ m * √2 ^ m
        = ((2 : ℝ) ^ (-(m : ℝ) / 2) * √2 ^ m) * ‖w‖ ^ m := by ring
      _ = ‖w‖ ^ m := by rw [hsqrt, one_mul]
  have hexp_cancel : Real.exp (-(y ^ 2) / 2) * Real.exp (y ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    have h0 : -(y ^ 2) / 2 + y ^ 2 / 2 = 0 := by ring
    rw [h0, Real.exp_zero]
  rw [norm_div, norm_mul, norm_pow, heval, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast]
  have hmul := mul_le_mul_of_nonneg_right hb
    (by positivity : 0 ≤ Real.exp (y ^ 2 / 2) * ‖w‖ ^ m)
  calc |Polynomial.aeval y (Polynomial.hermite m)| * ‖w‖ ^ m / (m.factorial : ℝ)
      = (|Polynomial.aeval y (Polynomial.hermite m)| * Real.exp (-(y ^ 2) / 2) /
            (m.factorial : ℝ)) *
          (Real.exp (y ^ 2 / 2) * ‖w‖ ^ m) := by
          calc |Polynomial.aeval y (Polynomial.hermite m)| * ‖w‖ ^ m / (m.factorial : ℝ)
              = |Polynomial.aeval y (Polynomial.hermite m)| *
                  (Real.exp (-(y ^ 2) / 2) * Real.exp (y ^ 2 / 2)) * ‖w‖ ^ m /
                    (m.factorial : ℝ) := by
                  rw [hexp_cancel, mul_one]
            _ = (|Polynomial.aeval y (Polynomial.hermite m)| * Real.exp (-(y ^ 2) / 2) /
                  (m.factorial : ℝ)) * (Real.exp (y ^ 2 / 2) * ‖w‖ ^ m) := by ring
    _ ≤ ((2 : ℝ) ^ (-(m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1)) *
          (Real.exp (y ^ 2 / 2) * ‖w‖ ^ m) := hmul
    _ = Real.exp (y ^ 2 / 2) *
          (((2 : ℝ) ^ (-(m : ℝ) / 2) * ‖w‖ ^ m) / Real.Gamma ((m : ℝ) / 2 + 1)) := by ring
    _ = Real.exp (y ^ 2 / 2) * ((‖w‖ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by rw [hpow]

/-- The Hermite exponential generating series is absolutely summable for every `y : ℝ` and
`w : ℂ`. -/
theorem summable_norm_aeval_hermite_mul_pow_div_factorial (y : ℝ) (w : ℂ) :
    Summable fun m : ℕ =>
      ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * w ^ m / m.factorial‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => norm_aeval_hermite_mul_pow_div_factorial_le m y w)
    ((Real.summable_pow_div_Gamma_div_two_add_one (‖w‖ / √2)).mul_left (Real.exp (y ^ 2 / 2)))

/-- Polynomial-free Gaussian majorant for every `M`-shifted tail of the Hermite generating series:
`∑_{k ≥ 0} ‖He_{k + M}(y) w^{k + M} / (k + M)!‖ < 2 exp(y² / 2 + ‖w‖² / 2)`. -/
theorem tsum_norm_aeval_hermite_mul_pow_div_factorial_add_lt (y : ℝ) (w : ℂ) (M : ℕ) :
    (∑' k : ℕ,
        ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
          (k + M).factorial‖) <
      2 * Real.exp (y ^ 2 / 2 + ‖w‖ ^ 2 / 2) := by
  have hsum1 : Summable fun k : ℕ =>
      ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
        (k + M).factorial‖ :=
    (summable_nat_add_iff M).2 (summable_norm_aeval_hermite_mul_pow_div_factorial y w)
  have hsum2 : Summable fun k : ℕ =>
      Real.exp (y ^ 2 / 2) *
        ((‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) :=
    ((summable_nat_add_iff M).2
      (Real.summable_pow_div_Gamma_div_two_add_one (‖w‖ / √2))).mul_left (Real.exp (y ^ 2 / 2))
  have hle := hsum1.tsum_le_tsum
    (fun k => norm_aeval_hermite_mul_pow_div_factorial_le (k + M) y w) hsum2
  have hlt := Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (‖w‖ / √2) M
  have hsq : (‖w‖ / √2) ^ 2 = ‖w‖ ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two]
  calc (∑' k : ℕ,
          ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
            (k + M).factorial‖)
      ≤ ∑' k : ℕ, Real.exp (y ^ 2 / 2) *
          ((‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) := hle
    _ = Real.exp (y ^ 2 / 2) *
          ∑' k : ℕ, (‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := tsum_mul_left
    _ < Real.exp (y ^ 2 / 2) * (2 * Real.exp ((‖w‖ / √2) ^ 2)) :=
          mul_lt_mul_of_pos_left hlt (Real.exp_pos _)
    _ = 2 * Real.exp (y ^ 2 / 2 + ‖w‖ ^ 2 / 2) := by
          rw [hsq, Real.exp_add]
          ring

/-- Vanishing-order Gaussian majorant for every `M`-shifted tail of the Hermite generating series:
`∑_{k ≥ 0} ‖He_{k + M}(y) w^{k + M} / (k + M)!‖ ≤ 2 e exp(y² / 2) (‖w‖ / √2)^M exp(‖w‖² / 2)`. -/
theorem tsum_norm_aeval_hermite_mul_pow_div_factorial_add_le (y : ℝ) (w : ℂ) (M : ℕ) :
    (∑' k : ℕ,
        ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
          (k + M).factorial‖) ≤
      2 * Real.exp 1 * Real.exp (y ^ 2 / 2) * (‖w‖ / √2) ^ M * Real.exp (‖w‖ ^ 2 / 2) := by
  have hsum1 : Summable fun k : ℕ =>
      ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
        (k + M).factorial‖ :=
    (summable_nat_add_iff M).2 (summable_norm_aeval_hermite_mul_pow_div_factorial y w)
  have hsum2 : Summable fun k : ℕ =>
      Real.exp (y ^ 2 / 2) *
        ((‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) :=
    ((summable_nat_add_iff M).2
      (Real.summable_pow_div_Gamma_div_two_add_one (‖w‖ / √2))).mul_left (Real.exp (y ^ 2 / 2))
  have hle := hsum1.tsum_le_tsum
    (fun k => norm_aeval_hermite_mul_pow_div_factorial_le (k + M) y w) hsum2
  have htail := Real.tsum_pow_add_div_Gamma_div_two_add_one_le_mul_exp (‖w‖ / √2) M
  have habs : |‖w‖ / √2| = ‖w‖ / √2 := abs_of_nonneg (by positivity)
  have hsq : (‖w‖ / √2) ^ 2 = ‖w‖ ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two]
  rw [habs, hsq] at htail
  calc (∑' k : ℕ,
          ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
            (k + M).factorial‖)
      ≤ ∑' k : ℕ, Real.exp (y ^ 2 / 2) *
          ((‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) := hle
    _ = Real.exp (y ^ 2 / 2) *
          ∑' k : ℕ, (‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := tsum_mul_left
    _ ≤ Real.exp (y ^ 2 / 2) *
          (2 * Real.exp 1 * (‖w‖ / √2) ^ M * Real.exp (‖w‖ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left htail (Real.exp_nonneg _)
    _ = 2 * Real.exp 1 * Real.exp (y ^ 2 / 2) * (‖w‖ / √2) ^ M * Real.exp (‖w‖ ^ 2 / 2) := by
          ring

/-! ### Dominated majorants and shifted-tail summability across parameter half-planes -/

/-- Pointwise nonnegative half-Gamma majorant for the `m`-th Hermite–Mellin–Gaussian–Laplace
integrand on `(0, ∞)`. -/
private def hermiteLaplaceMajorant (y ρ σ c : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (y ^ 2 / 2) * ((ρ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) *
    (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u))

private theorem hermiteLaplaceMajorant_nonneg {y ρ σ c : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) {u : ℝ}
    (hu : 0 < u) :
    0 ≤ hermiteLaplaceMajorant y ρ σ c m u := by
  unfold hermiteLaplaceMajorant
  exact mul_nonneg
    (mul_nonneg (Real.exp_nonneg _)
      (div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le))
    (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _))

private theorem norm_hermite_cpow_cexp_le_majorant (b z r : ℂ) (y : ℝ) (m : ℕ) {u : ℝ}
    (hu : 0 < u) :
    ‖(-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
        ((u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))‖ ≤
      hermiteLaplaceMajorant y ‖r‖ b.re z.re m u := by
  have hre_exp : (-(u : ℂ) ^ 2 / 2 - z * u).re = -u ^ 2 / 2 - z.re * u := by
    simp [← Complex.ofReal_pow]
  have hcpow : ‖(u : ℂ) ^ (b + m - 1)‖ = u ^ m * u ^ (b.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    have hre : (b + m - 1).re = (m : ℝ) + (b.re - 1) := by simp; ring
    rw [hre, Real.rpow_add hu, Real.rpow_natCast]
  have hterm : ‖(-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m)‖ * u ^ m =
      ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * (-r * u) ^ m / m.factorial‖ := by
    simp only [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hu.le, mul_pow]
    ring
  have hw : ‖-r * (u : ℂ)‖ = ‖r‖ * u := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu.le]
  have hb := norm_aeval_hermite_mul_pow_div_factorial_le m y (-r * u)
  rw [hw] at hb
  rw [norm_mul _ ((u : ℂ) ^ (b + m - 1) * _), norm_mul ((u : ℂ) ^ (b + m - 1)), hcpow,
    Complex.norm_exp, hre_exp]
  calc ‖(-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m)‖ *
          (u ^ m * u ^ (b.re - 1) * Real.exp (-u ^ 2 / 2 - z.re * u))
      = (‖(-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m)‖ * u ^ m) *
          (u ^ (b.re - 1) * Real.exp (-u ^ 2 / 2 - z.re * u)) := by ring
    _ = ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * (-r * u) ^ m / m.factorial‖ *
          (u ^ (b.re - 1) * Real.exp (-u ^ 2 / 2 - z.re * u)) := by rw [hterm]
    _ ≤ (Real.exp (y ^ 2 / 2) * ((‖r‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) *
          (u ^ (b.re - 1) * Real.exp (-u ^ 2 / 2 - z.re * u)) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
    _ = hermiteLaplaceMajorant y ‖r‖ b.re z.re m u := rfl

private theorem summable_hermiteLaplaceMajorant_add (y ρ σ c : ℝ) (M : ℕ) (u : ℝ) :
    Summable fun k : ℕ => hermiteLaplaceMajorant y ρ σ c (k + M) u := by
  unfold hermiteLaplaceMajorant
  exact (((summable_nat_add_iff M).2
    (Real.summable_pow_div_Gamma_div_two_add_one (ρ * u / √2))).mul_left
      (Real.exp (y ^ 2 / 2))).mul_right (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u))

private theorem measurable_tsum_hermiteLaplaceMajorant_add (y ρ σ c : ℝ) (M : ℕ) :
    Measurable fun u : ℝ => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u := by
  have hlim : ∀ u : ℝ, Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, hermiteLaplaceMajorant y ρ σ c (k + M) u)
      atTop (𝓝 (∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u)) :=
    fun u => (summable_hermiteLaplaceMajorant_add y ρ σ c M u).hasSum.tendsto_sum_nat
  exact measurable_of_tendsto_metrizable
    (fun N => by unfold hermiteLaplaceMajorant; fun_prop) (tendsto_pi_nhds.mpr hlim)

/-- Near the origin `(0, 1]`, the `O(u^M)` tail bound raises `u ^ (σ - 1)` to `u ^ (σ + M - 1)`,
so the summed `M`-shifted majorant is integrable whenever `0 < σ + M`. -/
private theorem integrableOn_tsum_hermiteLaplaceMajorant_Ioc {y ρ σ c : ℝ} {M : ℕ} (hρ : 0 ≤ ρ)
    (hσM : 0 < σ + M) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u) (Ioc 0 1) := by
  have hdom : IntegrableOn
      (fun u : ℝ => (2 * Real.exp 1 * Real.exp (y ^ 2 / 2 + ρ ^ 2 / 2) * (ρ / √2) ^ M) *
        (u ^ (σ + M - 1) * Real.exp (-u ^ 2 / 2 - c * u))) (Ioc 0 1) :=
    IntegrableOn.mono_set
      ((integrableOn_rpow_mul_exp_neg_sq_div_two_sub_mul_Ioi
        (by linarith : -1 < σ + (M : ℝ) - 1) c).const_mul _)
      Ioc_subset_Ioi_self
  refine Integrable.mono' hdom
    (measurable_tsum_hermiteLaplaceMajorant_add y ρ σ c M).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u ⟨hu0, hu1⟩
  have hg_nonneg : 0 ≤ ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u :=
    tsum_nonneg fun k => hermiteLaplaceMajorant_nonneg hρ (k + M) hu0
  rw [Real.norm_eq_abs, abs_of_nonneg hg_nonneg]
  simp only [hermiteLaplaceMajorant, tsum_mul_right, tsum_mul_left]
  have htail := Real.tsum_pow_add_div_Gamma_div_two_add_one_le_mul_exp (ρ * u / √2) M
  have habs : |ρ * u / √2| = (ρ / √2) * u := by rw [abs_of_nonneg (by positivity)]; ring
  have hsq : (ρ * u / √2) ^ 2 ≤ ρ ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two, mul_pow]
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ρ]
  rw [habs] at htail
  have htail' : (∑' k : ℕ, (ρ * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) ≤
      2 * Real.exp 1 * (ρ / √2) ^ M * u ^ M * Real.exp (ρ ^ 2 / 2) :=
    calc (∑' k : ℕ, (ρ * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1))
        ≤ 2 * Real.exp 1 * ((ρ / √2) * u) ^ M * Real.exp ((ρ * u / √2) ^ 2) := htail
      _ ≤ 2 * Real.exp 1 * ((ρ / √2) * u) ^ M * Real.exp (ρ ^ 2 / 2) := by gcongr
      _ = 2 * Real.exp 1 * (ρ / √2) ^ M * u ^ M * Real.exp (ρ ^ 2 / 2) := by rw [mul_pow]; ring
  have hrpow : u ^ M * u ^ (σ - 1) = u ^ (σ + M - 1) := by
    rw [← Real.rpow_natCast u M, ← Real.rpow_add hu0]; congr 1; ring
  calc Real.exp (y ^ 2 / 2) *
          (∑' k : ℕ, (ρ * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) *
          (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u))
      ≤ Real.exp (y ^ 2 / 2) *
          (2 * Real.exp 1 * (ρ / √2) ^ M * u ^ M * Real.exp (ρ ^ 2 / 2)) *
          (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u)) := by gcongr
    _ = (2 * Real.exp 1 * (Real.exp (y ^ 2 / 2) * Real.exp (ρ ^ 2 / 2)) * (ρ / √2) ^ M) *
          ((u ^ M * u ^ (σ - 1)) * Real.exp (-u ^ 2 / 2 - c * u)) := by ring
    _ = (2 * Real.exp 1 * Real.exp (y ^ 2 / 2 + ρ ^ 2 / 2) * (ρ / √2) ^ M) *
          (u ^ (σ + M - 1) * Real.exp (-u ^ 2 / 2 - c * u)) := by rw [← Real.exp_add, hrpow]

/-- On `(1, ∞)`, the polynomial-free `< 2 exp(ρ² u² / 2)` bound leaves Gaussian decay when `ρ < 1`
and `u ^ (σ - 1) * exp(-c * u)` when `ρ ≤ 1`. -/
private theorem integrableOn_tsum_hermiteLaplaceMajorant_Ioi_one (y : ℝ) {ρ σ c : ℝ} (M : ℕ)
    (hρ : 0 ≤ ρ) (hr : ρ < 1 ∨ (ρ ≤ 1 ∧ (0 < c ∨ (0 ≤ c ∧ σ < 0)))) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u) (Ioi 1) := by
  let g : ℝ → ℝ := fun u => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u
  have hg_meas : Measurable g := measurable_tsum_hermiteLaplaceMajorant_add y ρ σ c M
  have hg_nonneg : ∀ {u : ℝ}, 1 < u → 0 ≤ g u := fun {u} hu1 =>
    tsum_nonneg fun k => hermiteLaplaceMajorant_nonneg hρ (k + M) (zero_lt_one.trans hu1)
  have hupper : ∀ {u : ℝ}, 1 < u →
      g u ≤ 2 * Real.exp (y ^ 2 / 2) *
        (u ^ (σ - 1) * Real.exp (-((1 - ρ ^ 2) / 2) * u ^ 2 - c * u)) := fun {u} _ => by
    simp only [g, hermiteLaplaceMajorant, tsum_mul_right, tsum_mul_left]
    have hlt := (Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (ρ * u / √2) M).le
    have hsq : (ρ * u / √2) ^ 2 = ρ ^ 2 * u ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt zero_le_two, mul_pow]
    rw [hsq] at hlt
    calc Real.exp (y ^ 2 / 2) *
            (∑' k : ℕ, (ρ * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1)) *
            (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u))
        ≤ Real.exp (y ^ 2 / 2) * (2 * Real.exp (ρ ^ 2 * u ^ 2 / 2)) *
            (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u)) := by gcongr
      _ = 2 * Real.exp (y ^ 2 / 2) *
            (u ^ (σ - 1) * (Real.exp (ρ ^ 2 * u ^ 2 / 2) * Real.exp (-u ^ 2 / 2 - c * u))) := by
            ring
      _ = 2 * Real.exp (y ^ 2 / 2) *
            (u ^ (σ - 1) * Real.exp (-((1 - ρ ^ 2) / 2) * u ^ 2 - c * u)) := by
            rw [← Real.exp_add]; congr 3; ring
  rcases hr with hρ1 | ⟨hρ1, htail_cond⟩
  · set s' := max (σ - 1) 0
    have hdom : IntegrableOn
        (fun u : ℝ => 2 * Real.exp (y ^ 2 / 2) *
          (u ^ s' * Real.exp (-((1 - ρ ^ 2) / 2) * u ^ 2 - c * u))) (Ioi 1) :=
      IntegrableOn.mono_set
        ((integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi (by nlinarith : 0 < (1 - ρ ^ 2) / 2)
          (lt_of_lt_of_le (by norm_num) (le_max_right (σ - 1) 0)) c).const_mul _)
        (Ioi_subset_Ioi zero_le_one)
    refine Integrable.mono' hdom hg_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu1 : 1 < u)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg hu1)]
    refine (hupper hu1).trans ?_
    have hrpow : u ^ (σ - 1) ≤ u ^ s' :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (le_max_left (σ - 1) 0)
    gcongr
  · have hcond : 0 < c ∨ (0 ≤ c ∧ σ - 1 < -1) :=
      htail_cond.imp_right fun h => ⟨h.1, by linarith [h.2]⟩
    have hdom : IntegrableOn
        (fun u : ℝ => 2 * Real.exp (y ^ 2 / 2) * (u ^ (σ - 1) * Real.exp (-c * u))) (Ioi 1) :=
      (integrableOn_rpow_mul_exp_neg_mul_Ioi_of_pos one_pos hcond).const_mul _
    refine Integrable.mono' hdom hg_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu1 : 1 < u)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg hu1)]
    refine (hupper hu1).trans ?_
    have hexp : -((1 - ρ ^ 2) / 2) * u ^ 2 - c * u ≤ -c * u := by
      have h1 : 0 ≤ (1 - ρ ^ 2) / 2 := by nlinarith
      nlinarith [sq_nonneg u]
    gcongr

/-- The summed `M`-shifted majorant is integrable on `(0, ∞)` whenever `0 < σ + M` and either
`ρ < 1`, or `ρ ≤ 1` with `0 < c ∨ (0 ≤ c ∧ σ < 0)`. -/
private theorem integrableOn_tsum_hermiteLaplaceMajorant_Ioi {y ρ σ c : ℝ} {M : ℕ} (hρ : 0 ≤ ρ)
    (hσM : 0 < σ + M) (hr : ρ < 1 ∨ (ρ ≤ 1 ∧ (0 < c ∨ (0 ≤ c ∧ σ < 0)))) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact (integrableOn_tsum_hermiteLaplaceMajorant_Ioc hρ hσM).union
    (integrableOn_tsum_hermiteLaplaceMajorant_Ioi_one y M hρ hr)

private theorem integrableOn_hermiteLaplaceMajorant_Ioi (y ρ : ℝ) {σ : ℝ} (c : ℝ) {m : ℕ}
    (hσm : 0 < σ + m) :
    IntegrableOn (fun u => hermiteLaplaceMajorant y ρ σ c m u) (Ioi 0) := by
  unfold hermiteLaplaceMajorant
  have hconst := (integrableOn_rpow_mul_exp_neg_sq_div_two_sub_mul_Ioi
    (by linarith : -1 < σ + (m : ℝ) - 1) c).const_mul
    (Real.exp (y ^ 2 / 2) * ((ρ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)))
  refine IntegrableOn.congr_fun hconst (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
  have hrpow : u ^ (σ + (m : ℝ) - 1) = u ^ m * u ^ (σ - 1) := by
    rw [← Real.rpow_natCast u m, ← Real.rpow_add hu]; congr 1; ring
  have hpow : (ρ / √2) ^ m * u ^ m = (ρ * u / √2) ^ m := by rw [← mul_pow]; congr 1; ring
  rw [hrpow]
  calc Real.exp (y ^ 2 / 2) * ((ρ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) *
          (u ^ m * u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u))
      = Real.exp (y ^ 2 / 2) * (((ρ / √2) ^ m * u ^ m) / Real.Gamma ((m : ℝ) / 2 + 1)) *
          (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u)) := by ring
    _ = Real.exp (y ^ 2 / 2) * ((ρ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) *
          (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u)) := by rw [hpow]

/-- For `0 ≤ ρ`, `0 < σ + M`, and either `ρ < 1` or `ρ ≤ 1` with `0 < c ∨ (0 ≤ c ∧ σ < 0)`, the
real `M`-shifted Hermite–Mellin–Gaussian–Laplace majorant series
`∑_{k ≥ 0} |He_{k + M}(y)| ρ^{k + M} / (k + M)! · ∫₀^∞ u^{σ + k + M - 1} exp(-u² / 2 - c u) du`
is summable. -/
theorem summable_hermite_add_mul_integral_rpow_exp_Ioi (y : ℝ) {ρ σ c : ℝ} {M : ℕ} (hρ : 0 ≤ ρ)
    (hσM : 0 < σ + M) (hr : ρ < 1 ∨ (ρ ≤ 1 ∧ (0 < c ∨ (0 ≤ c ∧ σ < 0)))) :
    Summable fun k : ℕ =>
      |Polynomial.aeval y (Polynomial.hermite (k + M))| * ρ ^ (k + M) / (k + M).factorial *
        ∫ u in Ioi (0 : ℝ), u ^ (σ + ↑(k + M) - 1) * Real.exp (-u ^ 2 / 2 - c * u) := by
  have hB_sum : Summable fun k : ℕ =>
      ∫ u in Ioi (0 : ℝ), hermiteLaplaceMajorant y ρ σ c (k + M) u := by
    refine (hasSum_integral_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun k u => hermiteLaplaceMajorant y ρ σ c (k + M) u)
      (f := fun u => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u)
      (bound := fun k u => hermiteLaplaceMajorant y ρ σ c (k + M) u)
      (fun k => Measurable.aestronglyMeasurable (by unfold hermiteLaplaceMajorant; fun_prop))
      (fun k => ?_) ?_
      (integrableOn_tsum_hermiteLaplaceMajorant_Ioi hρ hσM hr) ?_).summable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      rw [Real.norm_eq_abs, abs_of_nonneg (hermiteLaplaceMajorant_nonneg hρ (k + M) hu)]
    · exact Eventually.of_forall fun u => summable_hermiteLaplaceMajorant_add y ρ σ c M u
    · exact Eventually.of_forall fun u =>
        (summable_hermiteLaplaceMajorant_add y ρ σ c M u).hasSum
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hB_sum
  · exact mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Ioi fun u (hu : 0 < u) => by positivity)
  · rw [← integral_const_mul]
    have hint_B := integrableOn_hermiteLaplaceMajorant_Ioi y ρ c
      (by push_cast; linarith : 0 < σ + ↑(k + M))
    have hint_L : IntegrableOn
        (fun u : ℝ =>
          (|Polynomial.aeval y (Polynomial.hermite (k + M))| * ρ ^ (k + M) / (k + M).factorial) *
            (u ^ (σ + ↑(k + M) - 1) * Real.exp (-u ^ 2 / 2 - c * u))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_sq_div_two_sub_mul_Ioi
        (by push_cast; linarith : -1 < σ + ↑(k + M) - 1) c).const_mul _
    refine setIntegral_mono_on hint_L hint_B measurableSet_Ioi fun u (hu : 0 < u) => ?_
    have hm := norm_hermite_cpow_cexp_le_majorant (σ : ℂ) (c : ℂ) (ρ : ℂ) y (k + M) hu
    have heval : Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) =
        ((Polynomial.aeval y (Polynomial.hermite (k + M)) : ℝ) : ℂ) :=
      Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y _
    have hρ_norm : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_of_nonneg hρ]
    rw [hρ_norm, Complex.ofReal_re, Complex.ofReal_re] at hm
    refine le_trans ?_ hm
    rw [norm_mul _ ((u : ℂ) ^ _ * _), norm_cpow_mul_cexp_neg_sq_div_two_sub_mul _ _ hu]
    simp only [norm_mul, norm_div, norm_pow, norm_neg, hρ_norm, Complex.norm_natCast, heval,
      Complex.norm_real, Real.norm_eq_abs, Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
    exact le_of_eq (by ring)

/-- Norm-summability of the complex `M`-shifted Hermite–Mellin–Gaussian–Laplace tail on
`0 < b.re + M`, valid for `‖r‖ < 1` (arbitrary `z : ℂ`) and at the boundary `‖r‖ ≤ 1` when
`0 < z.re` or `0 ≤ z.re ∧ b.re < 0`. -/
theorem summable_norm_hermite_add_mul_integral_cpow_cexp_Ioi {b z r : ℂ} (y : ℝ) {M : ℕ}
    (hbM : 0 < b.re + M)
    (hr : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < z.re ∨ (0 ≤ z.re ∧ b.re < 0)))) :
    Summable fun k : ℕ =>
      ‖(-r) ^ (k + M) / (k + M).factorial *
        Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_hermite_add_mul_integral_rpow_exp_Ioi y (norm_nonneg r) hbM hr)
  have heval : Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) =
      ((Polynomial.aeval y (Polynomial.hermite (k + M)) : ℝ) : ℂ) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y _
  rw [norm_mul, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast, heval,
    Complex.norm_real, Real.norm_eq_abs]
  have hcoef : ‖r‖ ^ (k + M) / ↑(k + M).factorial *
      |Polynomial.aeval y (Polynomial.hermite (k + M))| =
      |Polynomial.aeval y (Polynomial.hermite (k + M))| * ‖r‖ ^ (k + M) / ↑(k + M).factorial := by
    ring
  rw [hcoef]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
  simpa using norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (b + ↑(k + M)) z hu

/-- Norm-summability of the Pochhammer–Gamma–normalized `M`-shifted tail on `0 < b.re + M`,
covering the interior disk `‖r‖ < 1`, the boundary conditions `0 < z.re` and
`0 ≤ z.re ∧ b.re < 0` on `‖r‖ ≤ 1`, and terminating parameters `b = -n` (`n : ℕ`) for arbitrary
`z r : ℂ`. -/
theorem summable_norm_ascPochhammer_hermite_add_mul_inv_Gamma_integral_cpow_cexp_Ioi
    {b z r : ℂ} (y : ℝ) {M : ℕ} (hbM : 0 < b.re + M)
    (hr : (∃ n : ℕ, b = -n) ∨ ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < z.re ∨ (0 ≤ z.re ∧ b.re < 0)))) :
    Summable fun k : ℕ =>
      ‖(-r) ^ (k + M) / (k + M).factorial * (ascPochhammer ℂ (k + M)).eval b *
        Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * (Complex.Gamma (b + ↑(k + M)))⁻¹ *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)‖ := by
  have hfactor : ∀ k : ℕ,
      (-r) ^ (k + M) / (k + M).factorial * (ascPochhammer ℂ (k + M)).eval b *
          Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
          (Complex.Gamma (b + ↑(k + M)))⁻¹ *
          (∫ u in Ioi (0 : ℝ),
            (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) =
        (Complex.Gamma b)⁻¹ *
          ((-r) ^ (k + M) / (k + M).factorial *
            Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) := fun k => by
    have hG := Complex.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast b (k + M)
    calc (-r) ^ (k + M) / (k + M).factorial * (ascPochhammer ℂ (k + M)).eval b *
            Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
            (Complex.Gamma (b + ↑(k + M)))⁻¹ *
            (∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
        = ((ascPochhammer ℂ (k + M)).eval b * (Complex.Gamma (b + ↑(k + M)))⁻¹) *
            ((-r) ^ (k + M) / (k + M).factorial *
              Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
              ∫ u in Ioi (0 : ℝ),
                (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) := by ring
      _ = (Complex.Gamma b)⁻¹ *
            ((-r) ^ (k + M) / (k + M).factorial *
              Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
              ∫ u in Ioi (0 : ℝ),
                (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) := by
            rw [← hG]
  simp_rw [hfactor, norm_mul (Complex.Gamma b)⁻¹]
  rcases hr with ⟨n, rfl⟩ | hr'
  · have hzero : (Complex.Gamma (-(n : ℂ)))⁻¹ = 0 := by
      rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    simp [hzero]
  · exact (summable_norm_hermite_add_mul_integral_cpow_cexp_Ioi y hbM hr').mul_left _

/-! ### Closed-form evaluation on `0 < Re b`, rotational `tan t` form, and Abel limit -/

/-- Series-integral identity for the Hermite–Mellin–Gaussian–Laplace series at complex `r`: for
`0 < b.re`, `z r : ℂ`, and `y : ℝ` with `‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)`,
`∑_{m ≥ 0} (-r)^m / m! · He_m(y) ∫₀^∞ u^{b + m - 1} exp(-u² / 2 - z u) du` converges to
`∫₀^∞ u^{b - 1} exp(-(1 + r²) u² / 2 - (z + r y) u) du`. -/
theorem hasSum_hermite_mul_integral_cpow_cexp_Ioi_eq_integral {b z r : ℂ} (hb : 0 < b.re) (y : ℝ)
    (hr : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)) :
    HasSum
      (fun m : ℕ =>
        (-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (b - 1) * Complex.exp (-((1 + r ^ 2) * (u : ℂ) ^ 2) / 2 - (z + r * y) * u)) := by
  let F : ℕ → ℝ → ℂ := fun m u =>
    (-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
      ((u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
  have hr' : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < z.re ∨ (0 ≤ z.re ∧ b.re < 0))) :=
    hr.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩
  have hint0 : IntegrableOn
      (fun u : ℝ => ∑' m : ℕ, hermiteLaplaceMajorant y ‖r‖ b.re z.re m u) (Ioi 0) := by
    simpa only [add_zero] using integrableOn_tsum_hermiteLaplaceMajorant_Ioi (M := 0)
      (norm_nonneg r) (by simpa using hb) hr'
  have hdom := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F)
    (f := fun u : ℝ =>
      (u : ℂ) ^ (b - 1) * Complex.exp (-((1 + r ^ 2) * (u : ℂ) ^ 2) / 2 - (z + r * y) * u))
    (bound := fun m u => hermiteLaplaceMajorant y ‖r‖ b.re z.re m u)
    (fun m => Measurable.aestronglyMeasurable (by unfold F; fun_prop))
    (fun m => ?_)
    (Eventually.of_forall fun u => by
      simpa only [add_zero] using summable_hermiteLaplaceMajorant_add y ‖r‖ b.re z.re 0 u)
    hint0
    ?_
  · refine hdom.congr_fun fun m => ?_
    simp only [F, integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    exact norm_hermite_cpow_cexp_le_majorant b z r y m hu
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hgen := (Polynomial.hasSum_hermite_generating_function (y : ℂ) (-r * u)).mul_right
      ((u : ℂ) ^ (b - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
    have hsum_eq :
        Complex.exp ((y : ℂ) * (-r * u) - (-r * u) ^ 2 / 2) *
            ((u : ℂ) ^ (b - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) =
          (u : ℂ) ^ (b - 1) *
            Complex.exp (-((1 + r ^ 2) * (u : ℂ) ^ 2) / 2 - (z + r * y) * u) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    rw [hsum_eq] at hgen
    refine hgen.congr_fun fun m => ?_
    have hpow : (u : ℂ) ^ (b + m - 1) = (u : ℂ) ^ m * (u : ℂ) ^ (b - 1) := by
      rw [← Complex.cpow_natCast (u : ℂ) m, ← Complex.cpow_add _ _ hu0]
      congr 1
      ring
    simp only [F, mul_pow]
    calc (-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
            ((u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
        = (-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
            (((u : ℂ) ^ m * (u : ℂ) ^ (b - 1)) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) := by
            rw [hpow]
      _ = Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * ((-r) ^ m * (u : ℂ) ^ m) / m.factorial *
            ((u : ℂ) ^ (b - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) := by ring

/-- Rescaled closed-form `HasSum` for real `r`: for `0 < b.re`, `z : ℂ`, and `y r : ℝ` with
`|r| < 1 ∨ (|r| ≤ 1 ∧ 0 < z.re)`,
`∑_{m ≥ 0} (-r)^m / m! · He_m(y) ∫₀^∞ u^{b + m - 1} exp(-u² / 2 - z u) du` sums to
`(1 + r²)^{-b / 2} ∫₀^∞ v^{b - 1} exp(-v² / 2 - (z + r y) / √(1 + r²) · v) dv`. -/
theorem hasSum_hermite_mul_integral_cpow_cexp_Ioi {b z : ℂ} (hb : 0 < b.re) (y : ℝ) {r : ℝ}
    (hr : |r| < 1 ∨ (|r| ≤ 1 ∧ 0 < z.re)) :
    HasSum
      (fun m : ℕ =>
        (-(r : ℂ)) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      (((1 + r ^ 2 : ℝ) : ℂ) ^ (-b / 2) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) *
            Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + r * y) / √(1 + r ^ 2)) * v)) := by
  have hrC : ‖(r : ℂ)‖ < 1 ∨ (‖(r : ℂ)‖ ≤ 1 ∧ 0 < z.re) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hr
  have h1r : 0 < 1 + r ^ 2 := by positivity
  have hc : 0 < √(1 + r ^ 2) := Real.sqrt_pos.mpr h1r
  have hscale := integral_cpow_mul_cexp_neg_mul_sq_div_two_sub_mul_Ioi hc b (z + r * y)
  have hcpow : (√(1 + r ^ 2) : ℂ) ^ (-b) = ((1 + r ^ 2 : ℝ) : ℂ) ^ (-b / 2) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h1r.ne'),
      ← Complex.ofReal_log hc.le, ← Complex.ofReal_log h1r.le, Real.log_sqrt h1r.le]
    push_cast
    congr 1
    ring
  have hint_eq :
      (∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (b - 1) *
            Complex.exp (-((1 + (r : ℂ) ^ 2) * (u : ℂ) ^ 2) / 2 - (z + (r : ℂ) * y) * u)) =
        (∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (b - 1) *
            Complex.exp (-((√(1 + r ^ 2) : ℂ) * u) ^ 2 / 2 - (z + (r : ℂ) * y) * u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hsq : ((√(1 + r ^ 2) : ℂ) * u) ^ 2 = (1 + (r : ℂ) ^ 2) * (u : ℂ) ^ 2 := by
      rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt h1r.le]
      push_cast
      ring
    rw [hsq]
  rw [← hcpow, ← hscale, ← hint_eq]
  exact hasSum_hermite_mul_integral_cpow_cexp_Ioi_eq_integral hb y hrC

/-- Pochhammer–Gamma–normalized `HasSum` for real `r`: the factor `(b)_m * (Γ(b + m))⁻¹` cancels to
`(Γ b)⁻¹` term-by-term. -/
theorem hasSum_ascPochhammer_hermite_mul_inv_Gamma_integral_cpow_cexp_Ioi {b z : ℂ}
    (hb : 0 < b.re) (y : ℝ) {r : ℝ} (hr : |r| < 1 ∨ (|r| ≤ 1 ∧ 0 < z.re)) :
    HasSum
      (fun m : ℕ =>
        (-(r : ℂ)) ^ m / m.factorial * (ascPochhammer ℂ m).eval b *
          Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * (Complex.Gamma (b + m))⁻¹ *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      (((1 + r ^ 2 : ℝ) : ℂ) ^ (-b / 2) * (Complex.Gamma b)⁻¹ *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) *
            Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + r * y) / √(1 + r ^ 2)) * v)) := by
  have h := (hasSum_hermite_mul_integral_cpow_cexp_Ioi hb y hr).mul_left (Complex.Gamma b)⁻¹
  have hrhs : (Complex.Gamma b)⁻¹ *
      (((1 + r ^ 2 : ℝ) : ℂ) ^ (-b / 2) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) *
            Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + r * y) / √(1 + r ^ 2)) * v)) =
      ((1 + r ^ 2 : ℝ) : ℂ) ^ (-b / 2) * (Complex.Gamma b)⁻¹ *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) *
            Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + r * y) / √(1 + r ^ 2)) * v) := by ring
  rw [hrhs] at h
  refine h.congr_fun fun m => ?_
  rw [Complex.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast b m]
  ring

/-- Rotational `r = tan t` form (the Laplace-kernel identity underlying DLMF 12.13.5): for
`0 < b.re`, `z : ℂ`, `y : ℝ`, and `|t| < π / 4 ∨ (|t| ≤ π / 4 ∧ 0 < z.re)`,
`∑_{m ≥ 0} (-tan t)^m / m! · (b)_m He_m(y) / Γ(b + m) ∫₀^∞ u^{b + m - 1} exp(-u² / 2 - z u) du`
equals `(cos t)^b / Γ(b) ∫₀^∞ v^{b - 1} exp(-v² / 2 - (z cos t + y sin t) v) dv`. -/
theorem hasSum_ascPochhammer_hermite_tan_mul_inv_Gamma_integral_cpow_cexp_Ioi {b z : ℂ}
    (hb : 0 < b.re) (y : ℝ) {t : ℝ}
    (ht : |t| < Real.pi / 4 ∨ (|t| ≤ Real.pi / 4 ∧ 0 < z.re)) :
    HasSum
      (fun m : ℕ =>
        (-(Real.tan t : ℂ)) ^ m / m.factorial * (ascPochhammer ℂ m).eval b *
          Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * (Complex.Gamma (b + m))⁻¹ *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      ((Real.cos t : ℂ) ^ b * (Complex.Gamma b)⁻¹ *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) *
            Complex.exp (-(v : ℂ) ^ 2 / 2 - (z * Real.cos t + y * Real.sin t) * v)) := by
  have ht_le : |t| ≤ Real.pi / 4 := ht.elim le_of_lt And.left
  have ht_Ioo : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hbounds := abs_le.mp ht_le
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hpi4_Ioo : Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hnpi4_Ioo : -(Real.pi / 4) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht_Ioo
  have htan_cond : |Real.tan t| < 1 ∨ (|Real.tan t| ≤ 1 ∧ 0 < z.re) := by
    rcases ht with ht_lt | ⟨ht_le', hz⟩
    · obtain ⟨h1, h2⟩ := abs_lt.mp ht_lt
      exact Or.inl (abs_lt.mpr ⟨by simpa using Real.strictMonoOn_tan hnpi4_Ioo ht_Ioo h1,
        by simpa using Real.strictMonoOn_tan ht_Ioo hpi4_Ioo h2⟩)
    · obtain ⟨h1, h2⟩ := abs_le.mp ht_le'
      exact Or.inr ⟨abs_le.mpr
        ⟨by simpa using Real.strictMonoOn_tan.monotoneOn hnpi4_Ioo ht_Ioo h1,
          by simpa using Real.strictMonoOn_tan.monotoneOn ht_Ioo hpi4_Ioo h2⟩, hz⟩
  have hmain := hasSum_ascPochhammer_hermite_mul_inv_Gamma_integral_cpow_cexp_Ioi hb y htan_cond
  have h1t : 0 < 1 + Real.tan t ^ 2 := by positivity
  have hcpow : ((1 + Real.tan t ^ 2 : ℝ) : ℂ) ^ (-b / 2) = (Real.cos t : ℂ) ^ b := by
    have hsec : 1 + Real.tan t ^ 2 = (Real.cos t ^ 2)⁻¹ := by
      rw [← inv_inv (1 + Real.tan t ^ 2), Real.inv_one_add_tan_sq hcos.ne']
    have hlog : Real.log (1 + Real.tan t ^ 2) = -2 * Real.log (Real.cos t) := by
      rw [hsec, Real.log_inv, Real.log_pow]
      ring
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h1t.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hcos.ne'),
      ← Complex.ofReal_log h1t.le, ← Complex.ofReal_log hcos.le, hlog]
    push_cast
    congr 1
    ring
  have harg : (z + (Real.tan t : ℂ) * y) / √(1 + Real.tan t ^ 2) =
      z * Real.cos t + y * Real.sin t := by
    have hinv : (√(1 + Real.tan t ^ 2))⁻¹ = Real.cos t := Real.inv_sqrt_one_add_tan_sq hcos
    have hsin : Real.tan t / √(1 + Real.tan t ^ 2) = Real.sin t :=
      Real.tan_div_sqrt_one_add_tan_sq hcos
    calc (z + (Real.tan t : ℂ) * y) / √(1 + Real.tan t ^ 2)
        = z * ((√(1 + Real.tan t ^ 2))⁻¹ : ℝ) +
            (y : ℂ) * ((Real.tan t / √(1 + Real.tan t ^ 2) : ℝ) : ℂ) := by
            push_cast
            ring
      _ = z * Real.cos t + y * Real.sin t := by rw [hinv, hsin]
  rwa [hcpow, harg] at hmain

/-- **Abel limit at the boundary `r → 1⁻`.** For `0 < b.re`, *every* `z : ℂ` (even `Re z ≤ 0`,
where the `r = 1` series need not converge), and every `y : ℝ`, the interior `tsum` converges along
`𝓝[<] (1 : ℝ)` to `(2 : ℂ) ^ (-b / 2) ∫₀^∞ v^{b - 1} exp(-v² / 2 - (z + y) / √2 · v) dv`. -/
theorem tendsto_tsum_hermite_mul_integral_cpow_cexp_Ioi_nhdsLT_one {b : ℂ} (hb : 0 < b.re) (z : ℂ)
    (y : ℝ) :
    Tendsto
      (fun r : ℝ =>
        ∑' m : ℕ,
          (-(r : ℂ)) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((2 : ℂ) ^ (-b / 2) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + y) / √2) * v))) := by
  let g : ℝ → ℂ := fun r =>
    ((1 + r ^ 2 : ℝ) : ℂ) ^ (-b / 2) *
      ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (b - 1) *
          Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + r * y) / √(1 + r ^ 2)) * v)
  have hg_cont : ContinuousAt g 1 := by
    have hbase : ContinuousAt (fun r : ℝ => ((1 + r ^ 2 : ℝ) : ℂ)) 1 := by fun_prop
    have hslit : ((1 + (1 : ℝ) ^ 2 : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    have hpow : ContinuousAt (fun r : ℝ => ((1 + r ^ 2 : ℝ) : ℂ) ^ (-b / 2)) 1 :=
      hbase.cpow continuousAt_const hslit
    have harg : ContinuousAt
        (fun r : ℝ => (z + (r : ℂ) * y) / (√(1 + r ^ 2) : ℂ)) 1 := by
      refine ContinuousAt.div (by fun_prop) (Complex.continuous_ofReal.continuousAt.comp ?_) ?_
      · exact Real.continuous_sqrt.continuousAt.comp (by fun_prop)
      · exact Complex.ofReal_ne_zero.mpr (by positivity)
    have hint : Continuous fun w : ℂ =>
        ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - w * v) :=
      (differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_right hb).continuous
    exact hpow.mul (hint.continuousAt.comp harg)
  have hg1 : g 1 = (2 : ℂ) ^ (-b / 2) *
      ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + y) / √2) * v) := by
    simp only [g, one_pow, Complex.ofReal_one, one_mul]
    norm_num
  have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
    inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))) self_mem_nhdsWithin
  refine (hg1 ▸ hg_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hmem] with r ⟨hr1, hr2⟩
  exact (hasSum_hermite_mul_integral_cpow_cexp_Ioi hb y (Or.inl (abs_lt.mpr ⟨hr1, hr2⟩))).tsum_eq
    |>.symm

/-- Pochhammer–Gamma–normalized Abel limit as `r → 1⁻`, valid for `0 < b.re` and all `z : ℂ`,
`y : ℝ`. -/
theorem tendsto_tsum_ascPochhammer_hermite_mul_inv_Gamma_integral_cpow_cexp_Ioi_nhdsLT_one
    {b : ℂ} (hb : 0 < b.re) (z : ℂ) (y : ℝ) :
    Tendsto
      (fun r : ℝ =>
        ∑' m : ℕ,
          (-(r : ℂ)) ^ m / m.factorial * (ascPochhammer ℂ m).eval b *
            Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * (Complex.Gamma (b + m))⁻¹ *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((2 : ℂ) ^ (-b / 2) * (Complex.Gamma b)⁻¹ *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + y) / √2) * v))) := by
  have h := (tendsto_tsum_hermite_mul_integral_cpow_cexp_Ioi_nhdsLT_one hb z y).const_mul
    (Complex.Gamma b)⁻¹
  have hrhs : (Complex.Gamma b)⁻¹ *
      ((2 : ℂ) ^ (-b / 2) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + y) / √2) * v)) =
      (2 : ℂ) ^ (-b / 2) * (Complex.Gamma b)⁻¹ *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - ((z + y) / √2) * v) := by ring
  rw [hrhs] at h
  refine h.congr fun r => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [Complex.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast b m]
  ring

/-! ### Holomorphy in `b` of `M`-shifted tails on `{b : ℂ | 0 < b.re + M}` -/

/-- For every shift `M : ℕ`, `z r : ℂ`, and `y : ℝ` with `‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)`, the
`M`-shifted Hermite–Mellin–Gaussian–Laplace tail is holomorphic in `b` on the half-plane
`{b : ℂ | 0 < b.re + M}`. -/
theorem differentiableOn_tsum_hermite_add_mul_integral_cpow_cexp_Ioi (M : ℕ) {z r : ℂ}
    (y : ℝ) (hr : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)) :
    DifferentiableOn ℂ
      (fun b : ℂ =>
        ∑' k : ℕ,
          (-r) ^ (k + M) / (k + M).factorial *
            Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      {b : ℂ | 0 < b.re + M} := by
  intro b₀ (hb₀ : 0 < b₀.re + M)
  set δ := (b₀.re + M) / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  set σ₁ := b₀.re - δ with hσ₁_def
  set σ₂ := b₀.re + δ with hσ₂_def
  have hσ₁M : 0 < σ₁ + M := by linarith [hδ_def, hσ₁_def]
  have hσ₂M : 0 < σ₂ + M := by linarith [hδ_def, hσ₂_def]
  have hr' : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < z.re ∨ (0 ≤ z.re ∧ σ₁ < 0))) :=
    hr.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩
  have hr'' : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < z.re ∨ (0 ≤ z.re ∧ σ₂ < 0))) :=
    hr.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩
  have hsum1 := summable_hermite_add_mul_integral_rpow_exp_Ioi y (norm_nonneg r) hσ₁M hr'
  have hsum2 := summable_hermite_add_mul_integral_rpow_exp_Ioi y (norm_nonneg r) hσ₂M hr''
  let F : ℕ → ℂ → ℂ := fun k b =>
    (-r) ^ (k + M) / (k + M).factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
      ∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)
  have hF_diff : ∀ k : ℕ, DifferentiableOn ℂ (F k) (Metric.ball b₀ δ) := fun k => by
    have hshift : DifferentiableOn ℂ (fun b : ℂ => b + ↑(k + M)) (Metric.ball b₀ δ) := by fun_prop
    have hmaps : MapsTo (fun b : ℂ => b + ↑(k + M)) (Metric.ball b₀ δ) {w : ℂ | 0 < w.re} := by
      intro b hb
      rw [Metric.mem_ball, dist_eq_norm] at hb
      have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (b - b₀)) hb)
      rw [Complex.sub_re] at hre
      simp only [Set.mem_ofPred, Complex.add_re, Complex.natCast_re, Nat.cast_add]
      linarith [hδ_def, hre.1]
    exact ((differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_left z).comp
      hshift hmaps).const_mul _
  have hF_bound : ∀ (k : ℕ) (b : ℂ), b ∈ Metric.ball b₀ δ →
      ‖F k b‖ ≤
        (|Polynomial.aeval y (Polynomial.hermite (k + M))| * ‖r‖ ^ (k + M) / (k + M).factorial *
          ∫ u in Ioi (0 : ℝ), u ^ (σ₁ + ↑(k + M) - 1) * Real.exp (-u ^ 2 / 2 - z.re * u)) +
        (|Polynomial.aeval y (Polynomial.hermite (k + M))| * ‖r‖ ^ (k + M) / (k + M).factorial *
          ∫ u in Ioi (0 : ℝ), u ^ (σ₂ + ↑(k + M) - 1) * Real.exp (-u ^ 2 / 2 - z.re * u)) := by
    intro k b hb
    rw [Metric.mem_ball, dist_eq_norm] at hb
    have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (b - b₀)) hb)
    rw [Complex.sub_re] at hre
    have hb_lo : σ₁ < b.re := by linarith [hσ₁_def, hre.1]
    have hb_hi : b.re < σ₂ := by linarith [hσ₂_def, hre.2]
    have heval : Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) =
        ((Polynomial.aeval y (Polynomial.hermite (k + M)) : ℝ) : ℂ) :=
      Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y _
    have hcoef : ‖r‖ ^ (k + M) / ↑(k + M).factorial *
        |Polynomial.aeval y (Polynomial.hermite (k + M))| =
      |Polynomial.aeval y (Polynomial.hermite (k + M))| * ‖r‖ ^ (k + M) / ↑(k + M).factorial := by
      ring
    simp only [F, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast, heval,
      Complex.norm_real, Real.norm_eq_abs]
    rw [← mul_add, hcoef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact norm_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_le_add
      (b := b + ↑(k + M)) (σ₁ := σ₁ + ↑(k + M)) (σ₂ := σ₂ + ↑(k + M))
      (by push_cast; linarith [hσ₁M])
      (by simp only [Complex.add_re, Complex.natCast_re]; linarith [hb_lo])
      (by simp only [Complex.add_re, Complex.natCast_re]; linarith [hb_hi]) z
  have hball_diff := Complex.differentiableOn_tsum_of_summable_norm (hsum1.add hsum2) hF_diff
    Metric.isOpen_ball hF_bound
  exact (hball_diff.differentiableAt (Metric.ball_mem_nhds b₀ hδ)).differentiableWithinAt

/-- Holomorphy in `b` of the Pochhammer–Gamma–normalized `M`-shifted tail on
`{b : ℂ | 0 < b.re + M}` for `‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)`. -/
theorem differentiableOn_tsum_ascPochhammer_hermite_add_mul_inv_Gamma_integral_cpow_cexp_Ioi
    (M : ℕ) {z r : ℂ} (y : ℝ) (hr : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)) :
    DifferentiableOn ℂ
      (fun b : ℂ =>
        ∑' k : ℕ,
          (-r) ^ (k + M) / (k + M).factorial * (ascPochhammer ℂ (k + M)).eval b *
            Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
            (Complex.Gamma (b + ↑(k + M)))⁻¹ *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))
      {b : ℂ | 0 < b.re + M} := by
  have hfun :
      (fun b : ℂ =>
        ∑' k : ℕ,
          (-r) ^ (k + M) / (k + M).factorial * (ascPochhammer ℂ (k + M)).eval b *
            Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
            (Complex.Gamma (b + ↑(k + M)))⁻¹ *
            ∫ u in Ioi (0 : ℝ),
              (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)) =
      fun b : ℂ =>
        (Complex.Gamma b)⁻¹ *
          ∑' k : ℕ,
            (-r) ^ (k + M) / (k + M).factorial *
              Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
              ∫ u in Ioi (0 : ℝ),
                (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u) := by
    ext b
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [Complex.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast b (k + M)]
    ring
  rw [hfun]
  exact Complex.differentiable_one_div_Gamma.differentiableOn.mul
    (differentiableOn_tsum_hermite_add_mul_integral_cpow_cexp_Ioi M y hr)

end TauCeti
