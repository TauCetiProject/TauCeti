/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
# Hermite–Laplace series and rotational rescaling for parabolic cylinder kernels

Pairing the exponential generating function of the probabilists' Hermite polynomials
`∑_{m ≥ 0} He_m(y) (-r u)^m / m! = exp (-y r u - r² u² / 2)` with the half-line
Mellin–Gaussian–Laplace kernel `u ^ (b - 1) exp (-u² / 2 - z u)` and interchanging sum and integral
yields the series-integral identity

  `∑_{m ≥ 0} (-r)^m / m! · He_m(y) ∫₀^∞ u^{b + m - 1} exp (-u² / 2 - z u) du`
    `= (1 + r²)^{-b / 2} ∫₀^∞ v^{b - 1} exp (-v² / 2 - (z + r y) / √(1 + r²) · v) dv`

for `Re b > 0` and real `r` with `|r| < 1` (or `|r| ≤ 1` and `Re z > 0`). Setting `r = tan t` for
`|t| < π / 4` (or `|t| ≤ π / 4` and `Re z > 0`) turns `(1 + tan² t)^{-b / 2}` into `(cos t)^b` and
`(z + y tan t) / √(1 + tan² t)` into the rotated argument `z cos t + y sin t`, while multiplying by
`(b)_m / Γ(b + m) = 1 / Γ(b)` supplies the Gamma-normalized Laplace kernel of Weber's parabolic
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

* `TauCeti.summable_hermite_mul_integral_rpow_exp_Ioi`,
  `TauCeti.summable_norm_hermite_mul_integral_cpow_cexp_Ioi`,
  `TauCeti.summable_norm_ascPochhammer_hermite_mul_inv_Gamma_integral_cpow_cexp_Ioi`:
  absolute convergence of the Hermite–Laplace series for `‖r‖ < 1`, at the boundary `‖r‖ ≤ 1` when
  `0 < Re z` or `0 ≤ Re z ∧ Re b < 0`, and unconditionally at terminating parameters `b = -n`.
* `TauCeti.hasSum_hermite_mul_integral_cpow_cexp_Ioi_complex`,
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

/-! ### Dominated majorants and series summability -/

private theorem norm_neg_pow_div_factorial_mul_aeval_hermite (r : ℂ) (y : ℝ) (m : ℕ) :
    ‖(-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m)‖ =
      |Polynomial.aeval y (Polynomial.hermite m)| * ‖r‖ ^ m / m.factorial := by
  have heval : Polynomial.aeval (y : ℂ) (Polynomial.hermite m) =
      ((Polynomial.aeval y (Polynomial.hermite m) : ℝ) : ℂ) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y _
  rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast, heval,
    Complex.norm_real, Real.norm_eq_abs]
  ring

private theorem ascPochhammer_hermite_mul_inv_Gamma_eq (b r : ℂ) (y : ℝ) (m : ℕ) (I : ℂ) :
    (-r) ^ m / m.factorial * (ascPochhammer ℂ m).eval b *
        Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * (Complex.Gamma (b + m))⁻¹ * I =
      (Complex.Gamma b)⁻¹ *
        ((-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * I) := by
  rw [Complex.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast b m]
  ring

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

private theorem hermite_rpow_exp_le_majorant (y : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (σ c : ℝ) (m : ℕ)
    {u : ℝ} (hu : 0 < u) :
    (|Polynomial.aeval y (Polynomial.hermite m)| * ρ ^ m / m.factorial) *
        (u ^ (σ + m - 1) * Real.exp (-u ^ 2 / 2 - c * u)) ≤
      hermiteLaplaceMajorant y ρ σ c m u := by
  have hrpow : u ^ (σ + m - 1) = u ^ m * u ^ (σ - 1) := by
    rw [← Real.rpow_natCast u m, ← Real.rpow_add hu]
    congr 1
    ring
  have hcoef : |Polynomial.aeval y (Polynomial.hermite m)| * (ρ * u) ^ m / m.factorial ≤
      Real.exp (y ^ 2 / 2) * ((ρ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
    have hb := norm_aeval_hermite_mul_pow_div_factorial_le m y ((ρ * u : ℝ) : ℂ)
    have hw : ‖((ρ * u : ℝ) : ℂ)‖ = ρ * u := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlhs : ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * ((ρ * u : ℝ) : ℂ) ^ m /
        m.factorial‖ = |Polynomial.aeval y (Polynomial.hermite m)| * (ρ * u) ^ m / m.factorial := by
      have h := norm_neg_pow_div_factorial_mul_aeval_hermite (-((ρ * u : ℝ) : ℂ)) y m
      rw [neg_neg, norm_neg, hw] at h
      simpa only [mul_comm, div_mul_eq_mul_div] using h
    rwa [hlhs, hw] at hb
  calc (|Polynomial.aeval y (Polynomial.hermite m)| * ρ ^ m / m.factorial) *
          (u ^ (σ + m - 1) * Real.exp (-u ^ 2 / 2 - c * u))
      = (|Polynomial.aeval y (Polynomial.hermite m)| * (ρ * u) ^ m / m.factorial) *
          (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u)) := by rw [hrpow, mul_pow]; ring
    _ ≤ (Real.exp (y ^ 2 / 2) * ((ρ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) *
          (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u)) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = hermiteLaplaceMajorant y ρ σ c m u := rfl

private theorem norm_hermite_cpow_cexp_le_majorant (b z r : ℂ) (y : ℝ) (m : ℕ) {u : ℝ}
    (hu : 0 < u) :
    ‖(-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
        ((u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u))‖ ≤
      hermiteLaplaceMajorant y ‖r‖ b.re z.re m u := by
  rw [norm_mul, norm_neg_pow_div_factorial_mul_aeval_hermite,
    norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (b + m) z hu]
  simpa only [Complex.add_re, Complex.natCast_re] using
    hermite_rpow_exp_le_majorant y (norm_nonneg r) b.re z.re m hu

private theorem summable_hermiteLaplaceMajorant_add (y ρ σ c : ℝ) (M : ℕ) (u : ℝ) :
    Summable fun k : ℕ => hermiteLaplaceMajorant y ρ σ c (k + M) u := by
  unfold hermiteLaplaceMajorant
  exact (((summable_nat_add_iff M).2
    (Real.summable_pow_div_Gamma_div_two_add_one (ρ * u / √2))).mul_left
      (Real.exp (y ^ 2 / 2))).mul_right (u ^ (σ - 1) * Real.exp (-u ^ 2 / 2 - c * u))

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
    (Measurable.tsum fun k => by unfold hermiteLaplaceMajorant; fun_prop).aestronglyMeasurable ?_
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

private theorem tsum_hermiteLaplaceMajorant_add_le (y ρ σ c : ℝ) (M : ℕ) {u : ℝ} (hu : 0 < u) :
    (∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u) ≤
      2 * Real.exp (y ^ 2 / 2) *
        (u ^ (σ - 1) * Real.exp (-((1 - ρ ^ 2) / 2) * u ^ 2 - c * u)) := by
  have : 0 ≤ u ^ (σ - 1) := Real.rpow_nonneg hu.le _
  simp only [hermiteLaplaceMajorant, tsum_mul_right, tsum_mul_left]
  have hlt := (Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (ρ * u / √2) M).le
  rw [div_pow, Real.sq_sqrt zero_le_two, mul_pow] at hlt
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

/-- On `(1, ∞)`, the polynomial-free `< 2 exp(ρ² u² / 2)` bound leaves Gaussian decay when `ρ < 1`
and `u ^ (σ - 1) * exp(-c * u)` when `ρ ≤ 1`. -/
private theorem integrableOn_tsum_hermiteLaplaceMajorant_Ioi_one (y : ℝ) {ρ σ c : ℝ} (M : ℕ)
    (hρ : 0 ≤ ρ) (hr : ρ < 1 ∨ (ρ ≤ 1 ∧ (0 < c ∨ (0 ≤ c ∧ σ < 0)))) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u) (Ioi 1) := by
  let g : ℝ → ℝ := fun u => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u
  have hg_meas : Measurable g :=
    Measurable.tsum fun k => by unfold hermiteLaplaceMajorant; fun_prop
  have hg_nonneg : ∀ {u : ℝ}, 1 < u → 0 ≤ g u := fun {u} hu1 =>
    tsum_nonneg fun k => hermiteLaplaceMajorant_nonneg hρ (k + M) (zero_lt_one.trans hu1)
  -- Split between residual Gaussian decay (`ρ < 1`) and pure exponential/power decay (`ρ ≤ 1`).
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
    refine (tsum_hermiteLaplaceMajorant_add_le y ρ σ c M (zero_lt_one.trans hu1)).trans ?_
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
    have : 0 ≤ u ^ (σ - 1) := Real.rpow_nonneg (zero_lt_one.trans hu1).le _
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg hu1)]
    refine (tsum_hermiteLaplaceMajorant_add_le y ρ σ c M (zero_lt_one.trans hu1)).trans ?_
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

/-- For `0 ≤ ρ` and either `ρ < 1` or `ρ ≤ 1` with `0 < c ∨ (0 ≤ c ∧ σ < 0)`, the real
Hermite–Mellin–Gaussian–Laplace majorant series
`∑_{m ≥ 0} |He_m(y)| ρ^m / m! · ∫₀^∞ u^{σ + m - 1} exp(-u² / 2 - c u) du` is summable. -/
theorem summable_hermite_mul_integral_rpow_exp_Ioi (y : ℝ) {ρ σ c : ℝ} (hρ : 0 ≤ ρ)
    (hr : ρ < 1 ∨ (ρ ≤ 1 ∧ (0 < c ∨ (0 ≤ c ∧ σ < 0)))) :
    Summable fun m : ℕ =>
      |Polynomial.aeval y (Polynomial.hermite m)| * ρ ^ m / m.factorial *
        ∫ u in Ioi (0 : ℝ), u ^ (σ + m - 1) * Real.exp (-u ^ 2 / 2 - c * u) := by
  -- Shift past any non-integrable initial indices so `0 < σ + M`.
  obtain ⟨M, hM⟩ := exists_nat_gt (-σ)
  have hσM : 0 < σ + M := by linarith
  rw [← summable_nat_add_iff M]
  have hB_sum : Summable fun k : ℕ =>
      ∫ u in Ioi (0 : ℝ), hermiteLaplaceMajorant y ρ σ c (k + M) u := by
    refine (hasSum_integral_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun k u => hermiteLaplaceMajorant y ρ σ c (k + M) u)
      (f := fun u => ∑' k : ℕ, hermiteLaplaceMajorant y ρ σ c (k + M) u)
      (bound := fun k u => hermiteLaplaceMajorant y ρ σ c (k + M) u)
      (fun k => Measurable.aestronglyMeasurable (by unfold hermiteLaplaceMajorant; fun_prop))
      (fun k => ?_)
      (Eventually.of_forall fun u => summable_hermiteLaplaceMajorant_add y ρ σ c M u)
      (integrableOn_tsum_hermiteLaplaceMajorant_Ioi hρ hσM hr)
      (Eventually.of_forall fun u =>
        (summable_hermiteLaplaceMajorant_add y ρ σ c M u).hasSum)).summable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    rw [Real.norm_eq_abs, abs_of_nonneg (hermiteLaplaceMajorant_nonneg hρ (k + M) hu)]
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
    exact setIntegral_mono_on hint_L hint_B measurableSet_Ioi fun u (hu : 0 < u) =>
      hermite_rpow_exp_le_majorant y hρ σ c (k + M) hu

/-- Norm-summability of the complex Hermite–Mellin–Gaussian–Laplace series, valid for `‖r‖ < 1`
(arbitrary `b z : ℂ`) and at the boundary `‖r‖ ≤ 1` when `0 < z.re` or `0 ≤ z.re ∧ b.re < 0`. -/
theorem summable_norm_hermite_mul_integral_cpow_cexp_Ioi {b z r : ℂ} (y : ℝ)
    (hr : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < z.re ∨ (0 ≤ z.re ∧ b.re < 0)))) :
    Summable fun m : ℕ =>
      ‖(-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_hermite_mul_integral_rpow_exp_Ioi y (norm_nonneg r) hr)
  rw [norm_mul, norm_neg_pow_div_factorial_mul_aeval_hermite]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
  simpa using norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (b + m) z hu

/-- Norm-summability of the Pochhammer–Gamma–normalized Hermite–Laplace series, covering the
interior disk `‖r‖ < 1`, the boundary conditions `0 < z.re` and `0 ≤ z.re ∧ b.re < 0` on `‖r‖ ≤ 1`,
and terminating parameters `b = -n` (`n : ℕ`) for arbitrary `z r : ℂ`. -/
theorem summable_norm_ascPochhammer_hermite_mul_inv_Gamma_integral_cpow_cexp_Ioi {b z r : ℂ}
    (y : ℝ)
    (hr : (∃ n : ℕ, b = -n) ∨ ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < z.re ∨ (0 ≤ z.re ∧ b.re < 0)))) :
    Summable fun m : ℕ =>
      ‖(-r) ^ m / m.factorial * (ascPochhammer ℂ m).eval b *
        Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * (Complex.Gamma (b + m))⁻¹ *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)‖ := by
  simp_rw [ascPochhammer_hermite_mul_inv_Gamma_eq, norm_mul (Complex.Gamma b)⁻¹]
  rcases hr with ⟨n, rfl⟩ | hr'
  · simp [Complex.Gamma_neg_nat_eq_zero]
  · exact (summable_norm_hermite_mul_integral_cpow_cexp_Ioi y hr').mul_left _

/-! ### Closed-form evaluation on `0 < Re b`, rotational `tan t` form, and Abel limit -/

private theorem hasSum_hermite_mul_cpow_cexp (b z r : ℂ) (y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasSum
      (fun m : ℕ =>
        (-r) ^ m / m.factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite m) *
          ((u : ℂ) ^ (b + m - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)))
      ((u : ℂ) ^ (b - 1) *
        Complex.exp (-((1 + r ^ 2) * (u : ℂ) ^ 2) / 2 - (z + r * y) * u)) := by
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
  rw [mul_pow, hpow]
  ring

/-- Series-integral identity for the Hermite–Mellin–Gaussian–Laplace series at complex `r`: for
`0 < b.re`, `z r : ℂ`, and `y : ℝ` with `‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < z.re)`,
`∑_{m ≥ 0} (-r)^m / m! · He_m(y) ∫₀^∞ u^{b + m - 1} exp(-u² / 2 - z u) du` converges to
`∫₀^∞ u^{b - 1} exp(-(1 + r²) u² / 2 - (z + r y) u) du`. -/
theorem hasSum_hermite_mul_integral_cpow_cexp_Ioi_complex {b z r : ℂ} (hb : 0 < b.re) (y : ℝ)
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
  · exact hdom.congr_fun fun m => by simp only [F, integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    exact norm_hermite_cpow_cexp_le_majorant b z r y m hu
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    exact hasSum_hermite_mul_cpow_cexp b z r y hu

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
  have hscale := integral_cpow_mul_cexp_neg_mul_sq_div_two_sub_mul_Ioi_eq_cpow_neg_mul_integral
    hc b (z + r * y)
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
  exact hasSum_hermite_mul_integral_cpow_cexp_Ioi_complex hb y hrC

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
  simp_rw [ascPochhammer_hermite_mul_inv_Gamma_eq]
  simpa only [mul_left_comm (Complex.Gamma b)⁻¹, mul_assoc] using
    (hasSum_hermite_mul_integral_cpow_cexp_Ioi hb y hr).mul_left (Complex.Gamma b)⁻¹

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
  -- Map `|t| < π / 4` (or `|t| ≤ π / 4`) to `|tan t| < 1` (or `|tan t| ≤ 1`) on `(-π / 2, π / 2)`.
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
  -- Simplify `1 + tan² t = sec² t` in both the prefactor and the rotated argument.
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
  simp_rw [ascPochhammer_hermite_mul_inv_Gamma_eq, tsum_mul_left]
  simpa only [mul_left_comm (Complex.Gamma b)⁻¹, mul_assoc] using
    (tendsto_tsum_hermite_mul_integral_cpow_cexp_Ioi_nhdsLT_one hb z y).const_mul
      (Complex.Gamma b)⁻¹

/-! ### Holomorphy in `b` of `M`-shifted tails on `{b : ℂ | 0 < b.re + M}` -/

private theorem re_mem_Ioo_of_mem_ball {b b₀ : ℂ} {δ : ℝ} (hb : b ∈ Metric.ball b₀ δ) :
    b₀.re - δ < b.re ∧ b.re < b₀.re + δ := by
  rw [Metric.mem_ball, dist_eq_norm] at hb
  have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (b - b₀)) hb)
  rw [Complex.sub_re] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

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
  -- Dominate on `Metric.ball b₀ δ` by the sum of real endpoint series at `σ₁` and `σ₂`.
  have hsum1 := (summable_nat_add_iff M).2 (summable_hermite_mul_integral_rpow_exp_Ioi y
    (norm_nonneg r) (σ := σ₁) (hr.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩))
  have hsum2 := (summable_nat_add_iff M).2 (summable_hermite_mul_integral_rpow_exp_Ioi y
    (norm_nonneg r) (σ := σ₂) (hr.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩))
  let F : ℕ → ℂ → ℂ := fun k b =>
    (-r) ^ (k + M) / (k + M).factorial * Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) *
      ∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (b + ↑(k + M) - 1) * Complex.exp (-(u : ℂ) ^ 2 / 2 - z * u)
  have hF_diff : ∀ k : ℕ, DifferentiableOn ℂ (F k) (Metric.ball b₀ δ) := fun k => by
    have hshift : DifferentiableOn ℂ (fun b : ℂ => b + ↑(k + M)) (Metric.ball b₀ δ) := by fun_prop
    have hmaps : MapsTo (fun b : ℂ => b + ↑(k + M)) (Metric.ball b₀ δ) {w : ℂ | 0 < w.re} := by
      intro b hb
      simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.natCast_re, Nat.cast_add]
      linarith [hδ_def, (re_mem_Ioo_of_mem_ball hb).1]
    exact ((differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_left z).comp
      hshift hmaps).const_mul _
  have hF_bound : ∀ (k : ℕ) (b : ℂ), b ∈ Metric.ball b₀ δ →
      ‖F k b‖ ≤
        (|Polynomial.aeval y (Polynomial.hermite (k + M))| * ‖r‖ ^ (k + M) / (k + M).factorial *
          ∫ u in Ioi (0 : ℝ), u ^ (σ₁ + ↑(k + M) - 1) * Real.exp (-u ^ 2 / 2 - z.re * u)) +
        (|Polynomial.aeval y (Polynomial.hermite (k + M))| * ‖r‖ ^ (k + M) / (k + M).factorial *
          ∫ u in Ioi (0 : ℝ), u ^ (σ₂ + ↑(k + M) - 1) * Real.exp (-u ^ 2 / 2 - z.re * u)) := by
    intro k b hb
    obtain ⟨hb_lo, hb_hi⟩ := re_mem_Ioo_of_mem_ball hb
    dsimp only [F]
    rw [norm_mul, norm_neg_pow_div_factorial_mul_aeval_hermite, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact norm_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_le_add
      (b := b + ↑(k + M)) (σ₁ := σ₁ + ↑(k + M)) (σ₂ := σ₂ + ↑(k + M))
      (by push_cast; linarith [hδ_def, hσ₁_def])
      (by simp only [Complex.add_re, Complex.natCast_re]; linarith [hσ₁_def, hb_lo])
      (by simp only [Complex.add_re, Complex.natCast_re]; linarith [hσ₂_def, hb_hi]) z
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
  simp_rw [ascPochhammer_hermite_mul_inv_Gamma_eq, tsum_mul_left]
  exact Complex.differentiable_one_div_Gamma.differentiableOn.mul
    (differentiableOn_tsum_hermite_add_mul_integral_cpow_cexp_Ioi M y hr)

end TauCeti
