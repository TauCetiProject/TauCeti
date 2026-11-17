/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Asymptotics.Bleistein.ChangeOfVariables

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Calculus.DerivativeTest

/-!
# Bleistein's uniform remainder bound and asymptotic expansion

We formalize the comparison integrals, uniform remainder bound, and uniform asymptotic expansion
of Bleistein's method for Laplace-type integrals with coalescing critical points when the
transformed upper limit is infinite (`κ = ∞`, NIST DLMF §2.3(v), 2.3.31–2.3.33).

For `λ > 0`, `s, N ∈ ℕ`, and `y ∈ ℝ`, the parabolic-cylinder-type coefficient functions `F_s(y)`
and positive comparison functions `G_N(y)` are defined by

* `bleisteinF lam s y = ∫ τ in Ioi 0, Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)`
* `bleisteinG lam N y = ∫ τ in Ioi 0, Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)`.

When a transformed amplitude `f : ℝ → E` with values in a real Banach space `E` satisfies a
Taylor-like bound `‖f w - ∑ s ∈ range N, (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N` on `(0, ∞)`,
rescaling `w = τ / √x` yields the explicit uniform remainder bound (`norm_bleistein_remainder_le`)
for every `x > 0`. Combining this estimate with `integral_bleistein_eq` and
`integrableOn_bleistein_iff` from `TauCeti.Analysis.Asymptotics.Bleistein.ChangeOfVariables`
gives absolute convergence and the uniform expansion (DLMF 2.3.32) of the original integral
`I(α, x) = ∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t`.

## Main definitions

* `TauCeti.bleisteinF`: the coefficient integrals `F_s(y)` (DLMF 2.3.33).
* `TauCeti.bleisteinG`: the positive comparison integrals `G_N(y)` governing the remainder.

## Main results

* `TauCeti.integrableOn_bleisteinF_integrand`, `TauCeti.integrableOn_bleisteinG_integrand`:
  integrability on `(0, ∞)` for `0 < lam` and all `y : ℝ`.
* `TauCeti.bleisteinG_nonneg`, `TauCeti.bleisteinG_pos`, `TauCeti.abs_bleisteinF_le_bleisteinG`:
  positivity and comparison inequalities.
* `TauCeti.continuous_bleisteinF`, `TauCeti.continuous_bleisteinG`: continuity in `y`.
* `TauCeti.bleisteinG_zero`, `TauCeti.bleisteinG_two_mul`, `TauCeti.bleisteinF_zero_zero`,
  `TauCeti.bleisteinG_zero_zero`, `TauCeti.bleisteinF_one_one`: special values in terms of
  `Real.Gamma` and elementary evaluations.
* `TauCeti.integrableOn_bleistein_transformed`, `TauCeti.norm_bleistein_remainder_le`:
  integrability and explicit uniform remainder bound in the Bleistein `w`-variable (DLMF 2.3.32).
* `TauCeti.integrableOn_bleistein_of_amplitude_bound`,
  `TauCeti.norm_exp_smul_integral_bleistein_sub_le`, and specializations to `(0, k)` and `(0, ∞)`:
  absolute convergence and uniform asymptotic expansion of `I(α, x)` (DLMF 2.3.32).

## References

* NIST *Digital Library of Mathematical Functions*, §2.3(v), formulas 2.3.31–2.3.33,
  <https://dlmf.nist.gov/2.3#v>.
* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. 19 (1966), 353–370.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 9, §9.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti

/-! ### Definitions of `bleisteinF` and `bleisteinG` -/

/-- The coefficient integral `F_s(y)` of Bleistein's uniform expansion (DLMF 2.3.33):
`∫₀^∞ exp(-τ²/2 + y τ) (τ - y)^s τ^{λ - 1} dτ`. -/
noncomputable def bleisteinF (lam : ℝ) (s : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)

/-- Unfolding `TauCeti.bleisteinF`. -/
theorem bleisteinF_def (lam : ℝ) (s : ℕ) (y : ℝ) :
    bleisteinF lam s y =
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1) :=
  (rfl)

/-- The nonnegative comparison integral `G_N(y)` for the Bleistein remainder:
`∫₀^∞ exp(-τ²/2 + y τ) |τ - y|^N τ^{λ - 1} dτ`. -/
noncomputable def bleisteinG (lam : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)

/-- Unfolding `TauCeti.bleisteinG`. -/
theorem bleisteinG_def (lam : ℝ) (N : ℕ) (y : ℝ) :
    bleisteinG lam N y =
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) :=
  (rfl)

/-! ### Dominating Gaussian bounds, integrability, positivity, and continuity -/

/-- Uniform Gaussian dominating function on `(0, ∞)` for `|y| ≤ R`. -/
private noncomputable def bleisteinDomBound (lam : ℝ) (N : ℕ) (R τ : ℝ) : ℝ :=
  Real.exp (R ^ 2) * (1 + R) ^ N *
    ((τ ^ (lam - 1) + τ ^ ((N : ℝ) + lam - 1)) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2))

private theorem integrableOn_bleisteinDomBound {lam R : ℝ} {N : ℕ} (hlam : 0 < lam) :
    IntegrableOn (bleisteinDomBound lam N R) (Ioi 0) := by
  have h1 : IntegrableOn (fun τ : ℝ => τ ^ (lam - 1) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by positivity) (by linarith)
  have h2 : IntegrableOn (fun τ : ℝ => τ ^ ((N : ℝ) + lam - 1) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  refine IntegrableOn.congr_fun ((h1.add h2).const_mul (Real.exp (R ^ 2) * (1 + R) ^ N))
    (fun τ _ => ?_) measurableSet_Ioi
  simp only [bleisteinDomBound, Pi.add_apply]
  ring

private theorem bleisteinG_integrand_le_domBound {lam y R τ : ℝ} {N : ℕ} (hR : |y| ≤ R)
    (hτ : 0 < τ) :
    Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) ≤
      bleisteinDomBound lam N R τ := by
  have hR_nonneg : 0 ≤ R := (abs_nonneg y).trans hR
  have hy_le : y ≤ R := (le_abs_self y).trans hR
  have hexp_arg : -τ ^ 2 / 2 + y * τ ≤ R ^ 2 + -(1 / 4 : ℝ) * τ ^ 2 := by
    have hmul : y * τ ≤ R * τ := mul_le_mul_of_nonneg_right hy_le hτ.le
    have hsq : 0 ≤ (τ / 2 - R) ^ 2 := sq_nonneg (τ / 2 - R)
    linarith
  have hexp_le : Real.exp (-τ ^ 2 / 2 + y * τ) ≤
      Real.exp (R ^ 2) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp_arg
  have habs_le : |τ - y| ≤ τ + R := by
    calc |τ - y| ≤ |τ| + |y| := abs_sub τ y
      _ = τ + |y| := by rw [abs_of_pos hτ]
      _ ≤ τ + R := by linarith
  have hpow_le : |τ - y| ^ N * τ ^ (lam - 1) ≤
      (1 + R) ^ N * (τ ^ (lam - 1) + τ ^ ((N : ℝ) + lam - 1)) := by
    have hr1 : 0 ≤ τ ^ (lam - 1) := Real.rpow_nonneg hτ.le _
    have hr2 : 0 ≤ τ ^ ((N : ℝ) + lam - 1) := Real.rpow_nonneg hτ.le _
    rcases le_or_gt τ 1 with hle1 | hgt1
    · have hpow1 : |τ - y| ^ N ≤ (1 + R) ^ N :=
        pow_le_pow_left₀ (abs_nonneg _) (habs_le.trans (by linarith)) N
      calc |τ - y| ^ N * τ ^ (lam - 1)
          ≤ (1 + R) ^ N * τ ^ (lam - 1) := mul_le_mul_of_nonneg_right hpow1 hr1
        _ ≤ (1 + R) ^ N * (τ ^ (lam - 1) + τ ^ ((N : ℝ) + lam - 1)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hr2) (by positivity)
    · have hpow2 : |τ - y| ^ N ≤ ((1 + R) * τ) ^ N := by
        refine pow_le_pow_left₀ (abs_nonneg _) (habs_le.trans ?_) N
        nlinarith
      have hτN : (τ ^ N : ℝ) * τ ^ (lam - 1) = τ ^ ((N : ℝ) + lam - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hτ]
        ring_nf
      calc |τ - y| ^ N * τ ^ (lam - 1)
          ≤ ((1 + R) * τ) ^ N * τ ^ (lam - 1) := mul_le_mul_of_nonneg_right hpow2 hr1
        _ = (1 + R) ^ N * τ ^ ((N : ℝ) + lam - 1) := by rw [mul_pow, mul_assoc, hτN]
        _ ≤ (1 + R) ^ N * (τ ^ (lam - 1) + τ ^ ((N : ℝ) + lam - 1)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hr1) (by positivity)
  calc Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)
      = Real.exp (-τ ^ 2 / 2 + y * τ) * (|τ - y| ^ N * τ ^ (lam - 1)) := by ring
    _ ≤ (Real.exp (R ^ 2) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2)) *
          ((1 + R) ^ N * (τ ^ (lam - 1) + τ ^ ((N : ℝ) + lam - 1))) :=
        mul_le_mul hexp_le hpow_le (by positivity) (by positivity)
    _ = bleisteinDomBound lam N R τ := by simp only [bleisteinDomBound]; ring

/-- The integrand of `bleisteinG lam N y` is integrable on `(0, ∞)` for `0 < lam` and all `y`. -/
theorem integrableOn_bleisteinG_integrand {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) :
    IntegrableOn (fun τ : ℝ => Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1))
      (Ioi 0) := by
  have hcont : ContinuousOn
      (fun τ : ℝ => Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)) (Ioi 0) :=
    (Continuous.continuousOn (by fun_prop)).mul
      (continuousOn_id.rpow_const fun _ hτ => Or.inl (mem_Ioi.mp hτ).ne')
  refine (integrableOn_bleisteinDomBound hlam (R := |y|) (N := N)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hnonneg : 0 ≤ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg hτ.le _)
  rw [Real.norm_of_nonneg hnonneg]
  exact bleisteinG_integrand_le_domBound le_rfl hτ

/-- The integrand of `bleisteinF lam s y` is integrable on `(0, ∞)` for `0 < lam` and all `y`. -/
theorem integrableOn_bleisteinF_integrand {lam : ℝ} (hlam : 0 < lam) (s : ℕ) (y : ℝ) :
    IntegrableOn (fun τ : ℝ => Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1))
      (Ioi 0) := by
  have hcont : ContinuousOn
      (fun τ : ℝ => Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)) (Ioi 0) :=
    (Continuous.continuousOn (by fun_prop)).mul
      (continuousOn_id.rpow_const fun _ hτ => Or.inl (mem_Ioi.mp hτ).ne')
  refine (integrableOn_bleisteinG_integrand hlam s y).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
    abs_of_pos (Real.rpow_pos_of_pos hτ _)]

/-- `bleisteinG lam N y` is nonnegative for all `lam`, `N`, and `y`. -/
theorem bleisteinG_nonneg (lam : ℝ) (N : ℕ) (y : ℝ) : 0 ≤ bleisteinG lam N y := by
  refine setIntegral_nonneg measurableSet_Ioi fun τ hτ => ?_
  exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
    (Real.rpow_nonneg hτ.le _)

/-- For `0 < lam`, `bleisteinG lam N y` is strictly positive for all `N` and `y`. -/
theorem bleisteinG_pos {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) : 0 < bleisteinG lam N y := by
  rw [bleisteinG_def, integral_pos_iff_support_of_nonneg_ae]
  · let c : ℝ := max 0 y + 1
    have hc_pos : 0 < c := by positivity
    have hsub : Ioo c (c + 1) ⊆ Function.support
        (fun τ : ℝ => Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)) := by
      intro τ hτ
      have hτ_pos : 0 < τ := hc_pos.trans hτ.1
      have hsub_pos : 0 < τ - y := by
        have hy : y ≤ max 0 y := le_max_right 0 y
        linarith [hτ.1]
      rw [Function.mem_support]
      exact mul_ne_zero (mul_ne_zero (Real.exp_pos _).ne'
        (pow_ne_zero N (abs_ne_zero.mpr hsub_pos.ne'))) (Real.rpow_pos_of_pos hτ_pos _).ne'
    have hsub_Ioi : Ioo c (c + 1) ⊆ Ioi 0 := fun τ hτ => hc_pos.trans hτ.1
    have hvol : 0 < volume (Ioo c (c + 1)) := by simp [Real.volume_Ioo]
    refine hvol.trans_le ?_
    rw [Measure.restrict_apply' measurableSet_Ioi]
    exact measure_mono (subset_inter hsub hsub_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg hτ.le _)
  · exact integrableOn_bleisteinG_integrand hlam N y

/-- Pointwise comparison `|bleisteinF lam s y| ≤ bleisteinG lam s y` for `0 < lam`. -/
theorem abs_bleisteinF_le_bleisteinG {lam : ℝ} (hlam : 0 < lam) (s : ℕ) (y : ℝ) :
    |bleisteinF lam s y| ≤ bleisteinG lam s y := by
  rw [bleisteinF_def, bleisteinG_def, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (integrableOn_bleisteinG_integrand hlam s y) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
    abs_of_pos (Real.rpow_pos_of_pos hτ _)]

/-- For `0 < lam`, `bleisteinF lam s` is continuous on `ℝ`. -/
theorem continuous_bleisteinF {lam : ℝ} (hlam : 0 < lam) (s : ℕ) :
    Continuous (bleisteinF lam s) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated (bound := bleisteinDomBound lam s (|y₀| + 1)) ?_ ?_
    (integrableOn_bleisteinDomBound hlam) ?_
  · exact Eventually.of_forall fun y =>
      (integrableOn_bleisteinF_integrand hlam s y).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hy_le : |y| ≤ |y₀| + 1 := by
      have hd : |y - y₀| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hy
      linarith [abs_sub_abs_le_abs_sub y y₀]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
      abs_of_pos (Real.rpow_pos_of_pos hτ _)]
    exact bleisteinG_integrand_le_domBound hy_le hτ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    exact Continuous.continuousAt (by fun_prop)

/-- For `0 < lam`, `bleisteinG lam N` is continuous on `ℝ`. -/
theorem continuous_bleisteinG {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    Continuous (bleisteinG lam N) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated (bound := bleisteinDomBound lam N (|y₀| + 1)) ?_ ?_
    (integrableOn_bleisteinDomBound hlam) ?_
  · exact Eventually.of_forall fun y =>
      (integrableOn_bleisteinG_integrand hlam N y).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hy_le : |y| ≤ |y₀| + 1 := by
      have hd : |y - y₀| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hy
      linarith [abs_sub_abs_le_abs_sub y y₀]
    have hnonneg : 0 ≤ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) :=
      mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
        (Real.rpow_nonneg hτ.le _)
    rw [Real.norm_of_nonneg hnonneg]
    exact bleisteinG_integrand_le_domBound hy_le hτ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    exact Continuous.continuousAt (by fun_prop)

/-! ### Special values and parity checks -/

/-- At `N = 0`, `bleisteinG lam 0 y` coincides with `bleisteinF lam 0 y`. -/
@[simp]
theorem bleisteinG_zero (lam y : ℝ) : bleisteinG lam 0 y = bleisteinF lam 0 y := by
  simp [bleisteinG_def, bleisteinF_def]

/-- Even-index comparison integrals coincide with the coefficient integrals: `G_{2m} = F_{2m}`. -/
theorem bleisteinG_two_mul (lam : ℝ) (m : ℕ) (y : ℝ) :
    bleisteinG lam (2 * m) y = bleisteinF lam (2 * m) y := by
  simp only [bleisteinG_def, bleisteinF_def, pow_mul, sq_abs]

/-- Evaluation at the origin `bleisteinF lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2)` for
`0 < lam`. -/
theorem bleisteinF_zero_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinF lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  have heq : bleisteinF lam 0 0 =
      ∫ τ in Ioi (0 : ℝ), τ ^ (lam - 1) * Real.exp (-(1 / 2 : ℝ) * τ ^ (2 : ℝ)) := by
    rw [bleisteinF_def]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    rw [Real.rpow_two]
    ring_nf
  rw [heq, integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) (by positivity)]
  have h1 : lam - 1 + 1 = lam := by ring
  rw [h1]
  congr 1
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num [Real.rpow_neg_one]
  rw [hhalf, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
  congr 1
  ring

/-- Evaluation at the origin `bleisteinG lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2)` for
`0 < lam`. -/
theorem bleisteinG_zero_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinG lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  rw [bleisteinG_zero, bleisteinF_zero_zero hlam]

/-- For `lam = 1` and `s = 1`, `bleisteinF 1 1 y = 1` for every `y : ℝ`. -/
@[simp]
theorem bleisteinF_one_one (y : ℝ) : bleisteinF 1 1 y = 1 := by
  have hderiv : ∀ τ ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ => -Real.exp (-u ^ 2 / 2 + y * u))
      (Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y)) τ := fun τ _ => by
    have hquad : HasDerivAt (fun u : ℝ => -u ^ 2 / 2 + y * u) (-τ + y) τ := by
      have h1 : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-τ) τ :=
        (((hasDerivAt_pow 2 τ).neg).div_const 2).congr_deriv (by ring)
      have h2 : HasDerivAt (fun u : ℝ => y * u) y τ := by
        simpa using (hasDerivAt_id τ).const_mul y
      exact h1.add h2
    exact (hquad.exp.neg).congr_deriv (by ring)
  have hint : IntegrableOn (fun τ : ℝ => Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y)) (Ioi 0) := by
    refine (integrableOn_bleisteinF_integrand zero_lt_one 1 y).congr_fun (fun τ _ => ?_)
      measurableSet_Ioi
    simp
  have hbot : Tendsto (fun τ : ℝ => -τ ^ 2 / 2 + y * τ) atTop atBot := by
    have hupper : Tendsto (fun τ : ℝ => y ^ 2 + -((1 / 4 : ℝ) * τ ^ 2)) atTop atBot :=
      tendsto_atBot_add_const_left _ (y ^ 2)
        (tendsto_neg_atTop_atBot.comp
          ((tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop (by positivity)))
    refine tendsto_atBot_mono (fun τ => ?_) hupper
    have hsq : 0 ≤ (τ / 2 - y) ^ 2 := sq_nonneg (τ / 2 - y)
    linarith
  have htop : Tendsto (fun u : ℝ => -Real.exp (-u ^ 2 / 2 + y * u)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hbot).neg
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htop
  have hcongr : bleisteinF 1 1 y =
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) := by
    rw [bleisteinF_def]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    simp
  rw [hcongr, hftc]
  simp

/-! ### Rescaling `w = τ / √x` and the uniform remainder bound -/

private theorem bleistein_scale_phase {x a τ : ℝ} (hx : 0 < x) :
    -x * (((Real.sqrt x)⁻¹ * τ) ^ 2 / 2 - a * ((Real.sqrt x)⁻¹ * τ)) =
      -τ ^ 2 / 2 + a * Real.sqrt x * τ := by
  have hs_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  calc -x * (((Real.sqrt x)⁻¹ * τ) ^ 2 / 2 - a * ((Real.sqrt x)⁻¹ * τ))
      = -(x / Real.sqrt x ^ 2) * τ ^ 2 / 2 + a * (x / Real.sqrt x) * τ := by
          field_simp [hs_ne]; ring
    _ = -τ ^ 2 / 2 + a * Real.sqrt x * τ := by
          rw [hsq, div_self hx.ne', Real.div_sqrt]
          ring

private theorem bleistein_scale_sub {x a τ : ℝ} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * τ - a = (Real.sqrt x)⁻¹ * (τ - a * Real.sqrt x) := by
  have hs_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  field_simp [hs_ne]

private theorem bleistein_scale_rpow {lam x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (n : ℕ) :
    (Real.sqrt x)⁻¹ * ((Real.sqrt x)⁻¹) ^ n * ((Real.sqrt x)⁻¹ * τ) ^ (lam - 1) =
      x ^ (-((n : ℝ) + lam) / 2) * τ ^ (lam - 1) := by
  have hb_pos : 0 < (Real.sqrt x)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hx)
  have hb_rpow : (Real.sqrt x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le]
  rw [Real.mul_rpow hb_pos.le hτ.le, ← Real.rpow_natCast _ n, ← mul_assoc]
  congr 1
  calc (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ ^ (n : ℝ) * (Real.sqrt x)⁻¹ ^ (lam - 1)
      = (Real.sqrt x)⁻¹ ^ (1 : ℝ) * (Real.sqrt x)⁻¹ ^ (n : ℝ) * (Real.sqrt x)⁻¹ ^ (lam - 1) := by
          rw [Real.rpow_one]
    _ = (Real.sqrt x)⁻¹ ^ ((n : ℝ) + lam) := by
          rw [← Real.rpow_add hb_pos, ← Real.rpow_add hb_pos]
          ring_nf
    _ = x ^ (-((n : ℝ) + lam) / 2) := by
          rw [hb_rpow, ← Real.rpow_mul hx.le]
          congr 1
          ring

private theorem integrableOn_bleisteinF_scaled {lam a x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (s : ℕ) :
    IntegrableOn (fun w : ℝ => Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1))
      (Ioi 0) := by
  have hb_pos : 0 < (Real.sqrt x)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hx)
  have h0 : (0 : ℝ) = (Real.sqrt x)⁻¹ * 0 := by ring
  rw [h0, ← integrableOn_Ioi_comp_mul_left_iff _ 0 hb_pos]
  refine IntegrableOn.congr_fun ((integrableOn_bleisteinF_integrand hlam s (a * Real.sqrt x))
    |>.const_mul (((Real.sqrt x)⁻¹) ^ s * ((Real.sqrt x)⁻¹) ^ (lam - 1))) (fun τ hτ => ?_)
      measurableSet_Ioi
  rw [bleistein_scale_phase hx, bleistein_scale_sub hx, mul_pow,
    Real.mul_rpow hb_pos.le hτ.le]
  ring

private theorem integral_bleisteinF_scaled {lam a x : ℝ} (hx : 0 < x) (s : ℕ) :
    ∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1) =
      (x ^ (-lam / 2) * x ^ (-(s : ℝ) / 2)) * bleisteinF lam s (a * Real.sqrt x) := by
  have hb_pos : 0 < (Real.sqrt x)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hx)
  have hcomp := integral_comp_mul_left_Ioi'
    (fun w : ℝ => Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) 0 hb_pos
  rw [mul_zero] at hcomp
  rw [← hcomp, smul_eq_mul, ← integral_const_mul]
  have hcongr : ∫ τ in Ioi (0 : ℝ), (Real.sqrt x)⁻¹ *
      (Real.exp (-x * (((Real.sqrt x)⁻¹ * τ) ^ 2 / 2 - a * ((Real.sqrt x)⁻¹ * τ))) *
        ((Real.sqrt x)⁻¹ * τ - a) ^ s * ((Real.sqrt x)⁻¹ * τ) ^ (lam - 1)) =
      ∫ τ in Ioi (0 : ℝ), x ^ (-((s : ℝ) + lam) / 2) *
        (Real.exp (-τ ^ 2 / 2 + a * Real.sqrt x * τ) * (τ - a * Real.sqrt x) ^ s *
          τ ^ (lam - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    rw [bleistein_scale_phase hx, bleistein_scale_sub hx, mul_pow]
    linear_combination Real.exp (-τ ^ 2 / 2 + a * Real.sqrt x * τ) *
      (τ - a * Real.sqrt x) ^ s * bleistein_scale_rpow hx hτ s
  rw [hcongr, integral_const_mul, ← bleisteinF_def, ← Real.rpow_add hx]
  congr 2
  ring

private theorem integrableOn_bleisteinG_scaled {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (a : ℝ) (N : ℕ) :
    IntegrableOn (fun w : ℝ => Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1))
      (Ioi 0) := by
  have hb_pos : 0 < (Real.sqrt x)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hx)
  have h0 : (0 : ℝ) = (Real.sqrt x)⁻¹ * 0 := by ring
  rw [h0, ← integrableOn_Ioi_comp_mul_left_iff _ 0 hb_pos]
  refine IntegrableOn.congr_fun ((integrableOn_bleisteinG_integrand hlam N (a * Real.sqrt x))
    |>.const_mul (((Real.sqrt x)⁻¹) ^ N * ((Real.sqrt x)⁻¹) ^ (lam - 1))) (fun τ hτ => ?_)
      measurableSet_Ioi
  rw [bleistein_scale_phase hx, bleistein_scale_sub hx, abs_mul, abs_of_pos hb_pos, mul_pow,
    Real.mul_rpow hb_pos.le hτ.le]
  ring

private theorem integral_bleisteinG_scaled {lam a x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1) =
      x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
  have hb_pos : 0 < (Real.sqrt x)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hx)
  have hcomp := integral_comp_mul_left_Ioi'
    (fun w : ℝ => Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) 0 hb_pos
  rw [mul_zero] at hcomp
  rw [← hcomp, smul_eq_mul, ← integral_const_mul]
  have hcongr : ∫ τ in Ioi (0 : ℝ), (Real.sqrt x)⁻¹ *
      (Real.exp (-x * (((Real.sqrt x)⁻¹ * τ) ^ 2 / 2 - a * ((Real.sqrt x)⁻¹ * τ))) *
        |(Real.sqrt x)⁻¹ * τ - a| ^ N * ((Real.sqrt x)⁻¹ * τ) ^ (lam - 1)) =
      ∫ τ in Ioi (0 : ℝ), x ^ (-((N : ℝ) + lam) / 2) *
        (Real.exp (-τ ^ 2 / 2 + a * Real.sqrt x * τ) * |τ - a * Real.sqrt x| ^ N *
          τ ^ (lam - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    rw [bleistein_scale_phase hx, bleistein_scale_sub hx, abs_mul, abs_of_pos hb_pos, mul_pow]
    linear_combination Real.exp (-τ ^ 2 / 2 + a * Real.sqrt x * τ) *
      |τ - a * Real.sqrt x| ^ N * bleistein_scale_rpow hx hτ N
  rw [hcongr, integral_const_mul, ← bleisteinG_def]

section RemainderBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integrableOn_bleistein_poly {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (a : ℝ) (N : ℕ) (phi : ℕ → E) :
    IntegrableOn (fun w : ℝ => (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
      ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s) (Ioi 0) := by
  have hsum : IntegrableOn (fun w : ℝ => ∑ s ∈ Finset.range N,
      (Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) • phi s) (Ioi 0) :=
    integrable_finsetSum _ fun s _ => (integrableOn_bleisteinF_scaled hlam hx s).smul_const (phi s)
  refine IntegrableOn.congr_fun hsum (fun w _ => ?_) measurableSet_Ioi
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_smul]
  congr 1
  ring

private theorem integral_bleistein_poly [CompleteSpace E] {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 < x) (a : ℝ) (N : ℕ) (phi : ℕ → E) :
    ∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
      ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s =
      x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
        (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s := by
  have hcongr : ∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
      ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s =
      ∫ w in Ioi (0 : ℝ), ∑ s ∈ Finset.range N,
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) • phi s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul]
    congr 1
    ring
  rw [hcongr, integral_finsetSum _ fun s _ =>
    (integrableOn_bleisteinF_scaled hlam hx s).smul_const (phi s), Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_smul_const, integral_bleisteinF_scaled hx s, smul_smul]
  congr 1
  ring

private theorem integrableOn_bleistein_rem {lam a C x : ℝ} {N : ℕ} {f : ℝ → E} {phi : ℕ → E}
    (hlam : 0 < lam) (hx : 0 < x) (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s‖ ≤ C * |w - a| ^ N) :
    IntegrableOn (fun w : ℝ => (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
      (f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s)) (Ioi 0) := by
  have hK_cont : ContinuousOn
      (fun w : ℝ => Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) (Ioi 0) :=
    (Continuous.continuousOn (by fun_prop)).mul
      (continuousOn_id.rpow_const fun _ hw => Or.inl (mem_Ioi.mp hw).ne')
  have hP_cont : Continuous (fun w : ℝ => ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (fun w : ℝ =>
      (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        (f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s)) (volume.restrict (Ioi 0)) :=
    (hK_cont.aestronglyMeasurable measurableSet_Ioi).smul
      (hfm.sub hP_cont.aestronglyMeasurable)
  refine ((integrableOn_bleisteinG_scaled hlam hx a N).const_mul C).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hK_pos : 0 < Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hw _)
  rw [norm_smul, Real.norm_of_nonneg hK_pos.le]
  calc (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) *
        ‖f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s‖
      ≤ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * (C * |w - a| ^ N) :=
        mul_le_mul_of_nonneg_left (hf w hw) hK_pos.le
    _ = C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by ring

/-- When `f` is a.e. strongly measurable on `(0, ∞)` and satisfies the polynomial remainder bound
`‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N` on `(0, ∞)`, the Bleistein
transformed integrand is integrable on `(0, ∞)` for all `0 < lam` and `0 < x`. -/
theorem integrableOn_bleistein_transformed {lam a C x : ℝ} {N : ℕ} {f : ℝ → E} {phi : ℕ → E}
    (hlam : 0 < lam) (hx : 0 < x) (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s‖ ≤ C * |w - a| ^ N) :
    IntegrableOn (fun w : ℝ => (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w)
      (Ioi 0) := by
  refine IntegrableOn.congr_fun ((integrableOn_bleistein_rem hlam hx hfm hf).add
    (integrableOn_bleistein_poly hlam hx a N phi)) (fun w _ => ?_) measurableSet_Ioi
  rw [Pi.add_apply, ← smul_add, sub_add_cancel]

/-- Uniform remainder bound in the Bleistein `w`-variable (`κ = ∞`, DLMF 2.3.32) for functions
valued in a real Banach space `E`. The data `a`, `phi`, and `C` may depend on an auxiliary
parameter `α`; the estimate holds uniformly in that dependence. -/
theorem norm_bleistein_remainder_le [CompleteSpace E] {lam a C x : ℝ} {N : ℕ} {f : ℝ → E}
    {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s‖ ≤ C * |w - a| ^ N) :
    ‖(∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w) -
        x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
          (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
  have hint_f := integrableOn_bleistein_transformed hlam hx hfm hf
  have hint_P := integrableOn_bleistein_poly hlam hx a N phi
  rw [← integral_bleistein_poly hlam hx a N phi, ← integral_sub hint_f hint_P]
  have hsub_eq : ∫ w in Ioi (0 : ℝ),
      ((Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w -
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
          ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s) =
      ∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        (f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s) :=
    setIntegral_congr_fun measurableSet_Ioi fun w _ => (smul_sub _ _ _).symm
  rw [hsub_eq]
  refine (norm_integral_le_of_norm_le
    ((integrableOn_bleisteinG_scaled hlam hx a N).const_mul C) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hK_pos : 0 < Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) :=
      mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hw _)
    rw [norm_smul, Real.norm_of_nonneg hK_pos.le]
    calc (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) *
          ‖f w - ∑ s ∈ Finset.range N, ((w - a) ^ s) • phi s‖
        ≤ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * (C * |w - a| ^ N) :=
          mul_le_mul_of_nonneg_left (hf w hw) hK_pos.le
      _ = C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by ring
  · rw [integral_const_mul, integral_bleisteinG_scaled hx N, mul_assoc]

/-! ### Uniform expansion of the original Laplace-type integral `I(α, x)` (DLMF 2.3.32) -/

/-- Absolute convergence (Bochner integrability) of the original integral `I(α, x)` (DLMF 2.3.24)
on a measurable set `s ⊆ I ∩ (0, ∞)` mapped onto `(0, ∞)` by `bleisteinW p α`, when the transformed
amplitude satisfies a polynomial remainder bound on `(0, ∞)`. -/
theorem integrableOn_bleistein_of_amplitude_bound {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ}
    {lam α C x : ℝ} {N : ℕ} {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x)
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hs_meas : MeasurableSet s)
    (hs : s ⊆ I ∩ Ioi 0) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0)
    (himg : bleisteinW p α '' s = Ioi 0)
    (hfm : AEStronglyMeasurable (bleisteinAmplitude p q lam α s) (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α s w -
      ∑ j ∈ Finset.range N, ((w - bleisteinA p α) ^ j) • phi j‖ ≤ C * |w - bleisteinA p α| ^ N) :
    IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  rw [← integrableOn_bleistein_iff hI hord h0I hs_meas hs hα hp hpα hp''_pos hp', himg]
  exact integrableOn_bleistein_transformed hlam hx hfm hf

/-- Explicit uniform asymptotic expansion of `Real.exp (x * p 0) • I(α, x)` (DLMF 2.3.32) on a
measurable domain `s ⊆ I ∩ (0, ∞)` with `bleisteinW p α '' s = Ioi 0`. -/
theorem norm_exp_smul_integral_bleistein_sub_le [CompleteSpace E] {p : ℝ → ℝ} {q : ℝ → E}
    {I s : Set ℝ} {lam α C x : ℝ} {N : ℕ} {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x)
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hs_meas : MeasurableSet s)
    (hs : s ⊆ I ∩ Ioi 0) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0)
    (himg : bleisteinW p α '' s = Ioi 0)
    (hfm : AEStronglyMeasurable (bleisteinAmplitude p q lam α s) (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α s w -
      ∑ j ∈ Finset.range N, ((w - bleisteinA p α) ^ j) • phi j‖ ≤ C * |w - bleisteinA p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ j ∈ Finset.range N,
          (bleisteinF lam j (bleisteinA p α * Real.sqrt x) * x ^ (-(j : ℝ) / 2)) • phi j‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinA p α * Real.sqrt x) := by
  have hzero : x * p 0 + -x * p 0 = 0 := by ring
  rw [integral_bleistein_eq hI hord h0I hs_meas hs hα hp hpα hp''_pos hp', himg, smul_smul,
    ← Real.exp_add, hzero, Real.exp_zero, one_smul]
  exact norm_bleistein_remainder_le hlam hx hfm hf

/-- Absolute convergence of `I(α, x)` on a finite interval `(0, k)` when `p t → +∞` as `t → k⁻`,
`q` is continuous on `(0, k)`, and the transformed amplitude satisfies a polynomial remainder
bound. -/
theorem integrableOn_bleistein_Ioo_of_tendsto_atTop {p : ℝ → ℝ} {q : ℝ → E} {I : Set ℝ}
    {lam α k C x : ℝ} {N : ℕ} {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x) (hk : 0 < k)
    (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hlim : Tendsto p (𝓝[<] k) atTop)
    (hq : ContinuousOn q (Ioo 0 k))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioo 0 k) w -
      ∑ j ∈ Finset.range N, ((w - bleisteinA p α) ^ j) • phi j‖ ≤
        C * |w - bleisteinA p α| ^ N) :
    IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioo 0 k) := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hs : Ioo 0 k ⊆ I ∩ Ioi 0 := fun u hu => ⟨hsub ⟨hu.1.le, hu.2⟩, hu.1⟩
  have himg : bleisteinW p α '' Ioo 0 k = Ioi 0 :=
    image_bleisteinW_Ioo_of_tendsto_atTop hk hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_nhdsLT_atTop hk hI hord hsub hα hp.continuousOn hlim)
  have hcont := continuousOn_bleisteinAmplitude (lam := lam) hI hord (hsub ⟨le_rfl, hk⟩)
    isOpen_Ioo hs hα hp hpα hp''_pos hp' hq
  rw [himg] at hcont
  exact integrableOn_bleistein_of_amplitude_bound hlam hx hI hord (hsub ⟨le_rfl, hk⟩)
    measurableSet_Ioo hs hα hp hpα hp''_pos hp' himg (hcont.aestronglyMeasurable measurableSet_Ioi)
    hf

/-- Uniform asymptotic expansion of `Real.exp (x * p 0) • I(α, x)` on a finite interval `(0, k)`
when `p t → +∞` as `t → k⁻` (DLMF 2.3.32). -/
theorem norm_exp_smul_integral_bleistein_Ioo_sub_le [CompleteSpace E] {p : ℝ → ℝ} {q : ℝ → E}
    {I : Set ℝ} {lam α k C x : ℝ} {N : ℕ} {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x)
    (hk : 0 < k) (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hlim : Tendsto p (𝓝[<] k) atTop)
    (hq : ContinuousOn q (Ioo 0 k))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioo 0 k) w -
      ∑ j ∈ Finset.range N, ((w - bleisteinA p α) ^ j) • phi j‖ ≤
        C * |w - bleisteinA p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ j ∈ Finset.range N,
          (bleisteinF lam j (bleisteinA p α * Real.sqrt x) * x ^ (-(j : ℝ) / 2)) • phi j‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinA p α * Real.sqrt x) := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hs : Ioo 0 k ⊆ I ∩ Ioi 0 := fun u hu => ⟨hsub ⟨hu.1.le, hu.2⟩, hu.1⟩
  have himg : bleisteinW p α '' Ioo 0 k = Ioi 0 :=
    image_bleisteinW_Ioo_of_tendsto_atTop hk hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_nhdsLT_atTop hk hI hord hsub hα hp.continuousOn hlim)
  have hcont := continuousOn_bleisteinAmplitude (lam := lam) hI hord (hsub ⟨le_rfl, hk⟩)
    isOpen_Ioo hs hα hp hpα hp''_pos hp' hq
  rw [himg] at hcont
  exact norm_exp_smul_integral_bleistein_sub_le hlam hx hI hord (hsub ⟨le_rfl, hk⟩)
    measurableSet_Ioo hs hα hp hpα hp''_pos hp' himg (hcont.aestronglyMeasurable measurableSet_Ioi)
    hf

/-- Absolute convergence of `I(α, x)` on `(0, ∞)` when `p t → +∞` as `t → +∞`, `q` is continuous on
`(0, ∞)`, and the transformed amplitude satisfies a polynomial remainder bound. -/
theorem integrableOn_bleistein_Ioi_of_tendsto_atTop {p : ℝ → ℝ} {q : ℝ → E} {I : Set ℝ}
    {lam α C x : ℝ} {N : ℕ} {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x) (hI : IsOpen I)
    (hord : OrdConnected I) (hsub : Ici 0 ⊆ I) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I)
    (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hlim : Tendsto p atTop atTop)
    (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioi 0) w -
      ∑ j ∈ Finset.range N, ((w - bleisteinA p α) ^ j) • phi j‖ ≤
        C * |w - bleisteinA p α| ^ N) :
    IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioi 0) := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hs : Ioi 0 ⊆ I ∩ Ioi 0 := fun u hu => ⟨hsub hu.le, hu⟩
  have himg : bleisteinW p α '' Ioi 0 = Ioi 0 :=
    image_bleisteinW_Ioi_of_tendsto_atTop hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_atTop_of_tendsto_atTop (eventually_gt_atTop α) hlim)
  have hcont := continuousOn_bleisteinAmplitude (lam := lam) hI hord (hsub le_rfl) isOpen_Ioi hs hα
    hp hpα hp''_pos hp' hq
  rw [himg] at hcont
  exact integrableOn_bleistein_of_amplitude_bound hlam hx hI hord (hsub le_rfl) measurableSet_Ioi
    hs hα hp hpα hp''_pos hp' himg (hcont.aestronglyMeasurable measurableSet_Ioi) hf

/-- Uniform asymptotic expansion of `Real.exp (x * p 0) • I(α, x)` on `(0, ∞)` when `p t → +∞` as
`t → +∞` (DLMF 2.3.32). -/
theorem norm_exp_smul_integral_bleistein_Ioi_sub_le [CompleteSpace E] {p : ℝ → ℝ} {q : ℝ → E}
    {I : Set ℝ} {lam α C x : ℝ} {N : ℕ} {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x)
    (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ici 0 ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hlim : Tendsto p atTop atTop)
    (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioi 0) w -
      ∑ j ∈ Finset.range N, ((w - bleisteinA p α) ^ j) • phi j‖ ≤
        C * |w - bleisteinA p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ j ∈ Finset.range N,
          (bleisteinF lam j (bleisteinA p α * Real.sqrt x) * x ^ (-(j : ℝ) / 2)) • phi j‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinA p α * Real.sqrt x) := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hs : Ioi 0 ⊆ I ∩ Ioi 0 := fun u hu => ⟨hsub hu.le, hu⟩
  have himg : bleisteinW p α '' Ioi 0 = Ioi 0 :=
    image_bleisteinW_Ioi_of_tendsto_atTop hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_atTop_of_tendsto_atTop (eventually_gt_atTop α) hlim)
  have hcont := continuousOn_bleisteinAmplitude (lam := lam) hI hord (hsub le_rfl) isOpen_Ioi hs hα
    hp hpα hp''_pos hp' hq
  rw [himg] at hcont
  exact norm_exp_smul_integral_bleistein_sub_le hlam hx hI hord (hsub le_rfl) measurableSet_Ioi
    hs hα hp hpα hp''_pos hp' himg (hcont.aestronglyMeasurable measurableSet_Ioi) hf

end RemainderBound

end TauCeti
