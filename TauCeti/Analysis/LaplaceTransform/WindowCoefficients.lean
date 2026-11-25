/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
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

/-- At a real rate the damped moment integrand is real. -/
private theorem damped_moment_ofReal (g : ℝ → ℝ) (σ : ℝ) (n : ℕ) (u : ℝ) :
    Complex.exp (-(σ : ℂ) * u) • ((u : ℂ) ^ n / n !) • (g u : ℂ) =
      ((g u * (u ^ n * Real.exp (-σ * u) / n !) : ℝ) : ℂ) := by
  push_cast
  simp only [smul_eq_mul]
  ring

/-- Integrability of the damped real moment at a real rate. -/
private theorem integrableOn_damped_moment {g : ℝ → ℝ} {σ : ℝ} {c : ℂ} {n : ℕ}
    (h : HasLaplace (fun u : ℝ ↦ ((u : ℂ) ^ n / n !) • (g u : ℂ)) σ c) :
    IntegrableOn (fun u ↦ g u * (u ^ n * Real.exp (-σ * u) / n !)) (Ioi 0) := by
  refine h.integrable.re.congr (.of_forall fun u ↦ ?_)
  simp only [damped_moment_ofReal, RCLike.re_to_complex, ofReal_re]

/-- The positive part times the moment weight is integrable when the signed moment is. -/
private theorem integrableOn_max_mul_damped_moment {g : ℝ → ℝ} {σ : ℝ} {n : ℕ}
    (h : IntegrableOn (fun u ↦ g u * (u ^ n * Real.exp (-σ * u) / n !)) (Ioi 0)) :
    IntegrableOn (fun u ↦ max (g u) 0 * (u ^ n * Real.exp (-σ * u) / n !)) (Ioi 0) := by
  refine (h.sup (integrable_zero _ _ _)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have h₀ : 0 ≤ u := hu.le
  have hw : 0 ≤ u ^ n * Real.exp (-σ * u) / (n ! : ℝ) := by positivity
  symm
  exact (max_mul_of_nonneg _ _ hw).trans (by rw [zero_mul]; rfl)

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
  have hreal := hasLaplace_pow_div_factorial_smul_iteratedDeriv hr n
  have heq : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      ‖Complex.exp (-z * u) • ((u : ℂ) ^ n / n !) • (g u : ℂ)‖ =
        |g u| * (u ^ n * Real.exp (-z.re * u) / n !) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_damped_moment_eq g z hu.le n
  have ha := h.integrable.norm.congr heq
  have hs := integrableOn_damped_moment hreal
  rw [← h.integral_eq, ← hreal.integral_eq]
  have hr_eq : ∫ u : ℝ in Ioi 0, Complex.exp (-(z.re : ℂ) * u) •
      ((u : ℂ) ^ n / n !) • (g u : ℂ) =
        ((∫ u in Ioi 0, g u * (u ^ n * Real.exp (-z.re * u) / n !) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall (damped_moment_ofReal g z.re n))
  rw [hr_eq, ofReal_re]
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

/-- The integral of the exponentially weighted positive part of the input on a bounded window
is finite at any real rate if the input has a Laplace transform at one real rate. -/
private theorem integrableOn_max_mul_exp {g : ℝ → ℝ} {σ θ U V : ℝ} {c : ℂ} (hU : 0 ≤ U)
    (h : HasLaplace (fun u ↦ (g u : ℂ)) σ c) :
    IntegrableOn (fun u ↦ max (g u) 0 * Real.exp (-θ * u)) (Ioc U V) := by
  have h₀ : HasLaplace (fun u : ℝ ↦ ((u : ℂ) ^ (0 : ℕ) / (0 : ℕ)!) • (g u : ℂ)) σ c := by
    simpa using h
  have hi := (integrableOn_max_mul_damped_moment (integrableOn_damped_moment h₀)).mono_set
    (fun _ hu ↦ hU.trans_lt (mem_Ioc.mp hu).1 : Ioc U V ⊆ Ioi 0)
  refine (hi.mul_continuousOn_of_subset (g' := fun u ↦ Real.exp ((σ - θ) * u))
    (by fun_prop) measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self).congr_fun
      ?_ measurableSet_Ioc
  intro u _
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, mul_assoc,
    ← Real.exp_add]
  congr 2
  ring

/-- Bound a signed Laplace coefficient by the integral of the damped positive part on a window
and a Gamma-weighted tail. The exponential growth bound is needed only off that window, and
only for the positive part. The window is `(U, V]`; its left endpoint has measure zero. -/
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
    dsimp [w]
    rw [← mul_div_assoc, mul_left_comm, ← Real.exp_add]
    congr 3
    ring
  have hsub : Ioc U V ⊆ Ioi (0 : ℝ) := fun _ hu ↦ hU.trans_lt (mem_Ioc.mp hu).1
  have hi : IntegrableOn (fun u ↦ max (g u) 0 * w z.re u) (Ioi 0) :=
    integrableOn_max_mul_damped_moment
      (integrableOn_damped_moment (hasLaplace_pow_div_factorial_smul_iteratedDeriv hr n))
  have hwin := integrableOn_max_mul_exp (θ := θ) (V := V) hU hr.self_of_nhds
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
    rw [hshift A u, mul_assoc, ← mul_assoc (Real.exp _), ← Real.exp_add]
    simp [neg_mul]
  refine (norm_add_re_laplace_coeff_le hz hr n).trans ?_
  have hsplit := integral_inter_add_sdiff (t := Ioc U V) measurableSet_Ioc hi
  rw [inter_eq_right.mpr hsub] at hsplit
  simpa only [w, ← hsplit, mul_add, mul_assoc] using
    mul_le_mul_of_nonneg_left (add_le_add hwbound htbound) zero_le_two

end TauCeti
