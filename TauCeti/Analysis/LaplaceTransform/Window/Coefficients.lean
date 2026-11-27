/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Integral.Exp.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# One-sided bounds for Laplace coefficients on windows

For the Taylor expansion of `t ↦ F(z - t)`, the sum of the norm of a coefficient at `z` and
its real part at `z.re` is controlled by the positive part of the input to the transform. This
lets one use a one-sided estimate on a window and a separate growth bound away from the window,
without bounding the negative part on the window.

The coefficient inequality and its use with windows are stated in Levent Alpöge's
[formalization](https://github.com/leanprover-community/riemann-hypothesis), in
`Deduction.landau_window_ineq` and the proof of `Deduction.landau_window_key`.
-/

public section

open Complex Filter MeasureTheory Set
open scoped Nat Topology

namespace TauCeti

/-- The norm of the damped moment integrand depends on the real part of the rate only. -/
private theorem norm_damped_moment_eq (g : ℝ → ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    ‖Complex.exp (-z * u) • ((u : ℂ) ^ n / n !) • (g u : ℂ)‖ =
      |g u| * (u ^ n * Real.exp (-z.re * u) / n !) := by
  simp only [norm_smul, norm_div, norm_pow, norm_natCast, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, norm_exp, re_mul_ofReal, neg_re]
  ring

/-- At a real centre `σ`, the real part of the signed Taylor coefficient of degree `n` is the
integral of the input against the damped moment weight `u ^ n * exp (-σ * u) / n !`, which is
integrable: the case `t = 1` of `TauCeti.integrable_and_taylor_term_eq_integral`. -/
private theorem integrableOn_and_re_laplace_coeff_eq {g : ℝ → ℝ} {F : ℂ → ℂ} {σ : ℝ}
    (hr : ∀ᶠ w in 𝓝 (σ : ℂ), HasLaplace (fun u ↦ (g u : ℂ)) w (F w)) (n : ℕ) :
    IntegrableOn (fun u ↦ g u * (u ^ n * Real.exp (-σ * u) / n !)) (Ioi 0) ∧
      (((-1) ^ n / n ! : ℂ) • iteratedDeriv n F σ).re =
        ∫ u in Ioi 0, g u * (u ^ n * Real.exp (-σ * u) / n !) := by
  have hw (u : ℝ) : (1 * u) ^ n / (n ! : ℝ) * (Real.exp (-σ * u) * g u) =
      g u * (u ^ n * Real.exp (-σ * u) / n !) := by
    ring
  obtain ⟨hi, heq⟩ := integrable_and_taylor_term_eq_integral hr 1 n
  simp only [hw] at hi heq
  refine ⟨hi, ?_⟩
  rw [← ofReal_re (∫ u in Ioi 0, _), ← heq, ofReal_one, smul_smul, div_eq_inv_mul]

/-- For a real input, the norm of a signed Laplace Taylor coefficient at `z` plus the real part
of the coefficient at `z.re` is at most twice the corresponding moment of the positive part.
Only agreement with the Laplace transform near the two expansion points is needed. -/
theorem norm_add_re_laplace_coeff_le {g : ℝ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hz : ∀ᶠ w in 𝓝 z, HasLaplace (fun u ↦ (g u : ℂ)) w (F w))
    (hr : ∀ᶠ w in 𝓝 (z.re : ℂ), HasLaplace (fun u ↦ (g u : ℂ)) w (F w)) (n : ℕ) :
    ‖((-1) ^ n / n ! : ℂ) • iteratedDeriv n F z‖ +
        (((-1) ^ n / n ! : ℂ) • iteratedDeriv n F z.re).re ≤
      2 * ∫ u in Ioi 0, max (g u) 0 * (u ^ n * Real.exp (-z.re * u) / n !) := by
  have h := hasLaplace_pow_div_factorial_smul_iteratedDeriv hz n
  obtain ⟨hs, hreal⟩ := integrableOn_and_re_laplace_coeff_eq hr n
  have heq : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      ‖Complex.exp (-z * u) • ((u : ℂ) ^ n / n !) • (g u : ℂ)‖ =
        |g u| * (u ^ n * Real.exp (-z.re * u) / n !) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_damped_moment_eq g z hu.le n
  have ha := h.integrable.norm.congr heq
  rw [← h.integral_eq, hreal]
  calc
    _ ≤ (∫ u in Ioi 0, |g u| * (u ^ n * Real.exp (-z.re * u) / n !)) +
        ∫ u in Ioi 0, g u * (u ^ n * Real.exp (-z.re * u) / n !) :=
      add_le_add_left ((norm_integral_le_integral_norm _).trans_eq (integral_congr_ae heq)) _
    _ = _ := by
      rw [← integral_add ha hs, ← integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun u ↦ by
        have heq' : |g u| + g u = 2 * max (g u) 0 := by
          simpa only [posPart_def, two_nsmul, two_mul] using
            abs_add_eq_two_nsmul_posPart (g u)
        simp only [← add_mul, heq', mul_assoc]

/-- Bound the norm of the signed Laplace coefficient at `z` plus the real part of the coefficient
at `z.re` by `2 (z.re - θ)⁻ⁿ` times the integral of the positive part damped at rate `θ` over the
window `(U, V]`, plus `2 C` times a Gamma-weighted tail off the window. The real-part term can be
negative, so this does not bound the coefficient at `z` by itself. The exponential growth bound is
needed only off the window, and only for the positive part. The left endpoint of the window has
measure zero. -/
theorem norm_add_re_laplace_coeff_le_window {g : ℝ → ℝ} {F : ℂ → ℂ} {z : ℂ} {θ A C U V : ℝ}
    (hz : ∀ᶠ w in 𝓝 z, HasLaplace (fun u ↦ (g u : ℂ)) w (F w))
    (hr : ∀ᶠ w in 𝓝 (z.re : ℂ), HasLaplace (fun u ↦ (g u : ℂ)) w (F w))
    (hθ : θ < z.re) (hA : A < z.re) (hU : 0 ≤ U)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi 0 \ Ioc U V), max (g u) 0 ≤ C * Real.exp (A * u)) (n : ℕ) :
    ‖((-1) ^ n / n ! : ℂ) • iteratedDeriv n F z‖ +
        (((-1) ^ n / n ! : ℂ) • iteratedDeriv n F z.re).re ≤
      2 * ((z.re - θ) ^ n)⁻¹ * (∫ u in Ioc U V, max (g u) 0 * Real.exp (-θ * u)) +
        2 * C * ∫ u in Ioi 0 \ Ioc U V, u ^ n * Real.exp (-(z.re - A) * u) / n ! := by
  let w (a u : ℝ) := u ^ n * Real.exp (-a * u) / (n ! : ℝ)
  have hshift (a u : ℝ) : w z.re u = Real.exp (-a * u) * w (z.re - a) u := by
    have he : -z.re * u = -a * u + -(z.re - a) * u := by ring
    simp only [w, he, Real.exp_add]
    ring
  have hsub : Ioc U V ⊆ Ioi (0 : ℝ) := fun _ hu ↦ hU.trans_lt (mem_Ioc.mp hu).1
  have hi : IntegrableOn (fun u ↦ max (g u) 0 * w z.re u) (Ioi 0) :=
    (integrableOn_and_re_laplace_coeff_eq hr n).1.pos_part_mul <|
      (ae_restrict_mem measurableSet_Ioi).mono fun u (hu : 0 < u) ↦ by dsimp [w]; positivity
  -- On the bounded window the input itself is integrable, so any continuous weight is allowed.
  have hgwin : IntegrableOn g (Ioc U V) := by
    have hc := (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_of_le_left hU)).mp
      (intervalIntegrable_of_integrableOn_cexp_neg_mul_smul_Ioi hr.self_of_nhds.integrable
        (le_max_of_le_left hU) (b := max U V))
    exact ((hc.mono_set (Ioc_subset_Ioc hU (le_max_right U V))).re.congr
      (.of_forall fun u ↦ by simp only [RCLike.re_to_complex, ofReal_re]))
  have hwin : IntegrableOn (fun u ↦ max (g u) 0 * Real.exp (-θ * u)) (Ioc U V) :=
    IntegrableOn.mul_continuousOn_of_subset hgwin.pos_part (by fun_prop)
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have ht : IntegrableOn (w (z.re - A)) (Ioi 0) := by
    refine ((integrableOn_pow_mul_exp_neg_mul_Ioi n (sub_pos.mpr hA)).mul_const
      ((n ! : ℝ)⁻¹)).congr (.of_forall fun u ↦ ?_)
    simp only [w, neg_mul, div_eq_mul_inv]
  have hwbound : ∫ u in Ioc U V, max (g u) 0 * w z.re u ≤
      ((z.re - θ) ^ n)⁻¹ * ∫ u in Ioc U V, max (g u) 0 * Real.exp (-θ * u) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hi.mono_set hsub) (hwin.const_mul _) measurableSet_Ioc fun u hu ↦ ?_
    rw [hshift θ u, ← mul_assoc, mul_comm (((z.re - θ) ^ n)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_max_right ..) (Real.exp_nonneg _))
    have hp : 0 < (n ! : ℝ) := by positivity
    simp only [w, div_le_iff₀ hp]
    simpa [div_eq_mul_inv, mul_comm] using
      pow_mul_exp_neg_mul_le (sub_pos.mpr hθ) (hsub hu).le n
  have htbound : ∫ u in Ioi 0 \ Ioc U V, max (g u) 0 * w z.re u ≤
      C * ∫ u in Ioi 0 \ Ioc U V, w (z.re - A) u := by
    rw [← integral_const_mul]
    refine setIntegral_mono_ae_restrict (hi.mono_set sdiff_subset)
      ((ht.mono_set sdiff_subset).const_mul _) ?_
    filter_upwards [hg, ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Ioc)] with u hu hmem
    have h₀ : 0 ≤ u := hmem.1.le
    have hw : 0 ≤ w z.re u := by dsimp [w]; positivity
    refine (mul_le_mul_of_nonneg_right hu hw).trans_eq ?_
    have he : Real.exp (A * u) * Real.exp (-A * u) = 1 := by
      rw [← Real.exp_add, show A * u + -A * u = 0 by ring, Real.exp_zero]
    rw [hshift A u]
    linear_combination C * w (z.re - A) u * he
  refine (norm_add_re_laplace_coeff_le hz hr n).trans ?_
  have hsplit := integral_inter_add_sdiff (t := Ioc U V) measurableSet_Ioc hi
  rw [inter_eq_right.mpr hsub] at hsplit
  simpa only [w, ← hsplit, mul_add, mul_assoc] using
    mul_le_mul_of_nonneg_left (add_le_add hwbound htbound) zero_le_two

end TauCeti
