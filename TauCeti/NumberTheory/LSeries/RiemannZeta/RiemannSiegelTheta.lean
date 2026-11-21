/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HardyZ
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# The Riemann–Siegel theta function

The Riemann–Siegel theta function is
`ϑ(T) = ∫₀^T (Re ψ(1/4 + it/2) - log π) / 2 dt`, where `ψ = Γ'/Γ` is `Complex.digamma`. It is the
continuous argument of the archimedean factor `Γℝ(1/2 + iT) = π^(-1/4 - iT/2) Γ(1/4 + iT/2)` of the
completed zeta function on the critical line, normalized by `ϑ(0) = 0`. It enters the zero count of
`ζ` through `N(T) = ϑ(T)/π + 1 + S(T)`, and the Riemann–Siegel formula through Hardy's function
`Z(t) = e^{iϑ(t)} ζ(1/2 + it)`.

This file proves:

* `TauCeti.riemannSiegelTheta_eq_im_logGamma`: `ϑ(T) = Im log Γ(1/4 + iT/2) - (T/2) log π`, with
  the branch `TauCeti.logGamma` of `log Γ` on the slit plane that is real on the positive axis;
* the derivative `ϑ'(T) = (Re ψ(1/4 + iT/2) - log π) / 2` and the oddness `ϑ(-T) = -ϑ(T)`;
* `TauCeti.Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta`:
  `Γℝ(1/2 + it) = |Γℝ(1/2 + it)| e^{iϑ(t)}`, and from it
  `TauCeti.hardyZ_eq_exp_riemannSiegelTheta_mul`: Mathlib's `hardyZ t` is `e^{iϑ(t)} ζ(1/2 + it)`;
* `TauCeti.riemannSiegelTheta_eq_add_im_stirlingRemainder`: the exact Stirling form
  `ϑ(T) = (T/2) log |z| - (arg z)/4 - T/2 - (T/2) log π + Im R(z)` at `z = 1/4 + iT/2`, where `R` is
  the Stirling remainder `TauCeti.stirlingRemainder`;
* `TauCeti.abs_riemannSiegelTheta_sub_le`: the explicit asymptotic
  `|ϑ(T) - ((T/2) log (T/(2πe)) - π/8)| ≤ 1/T` for `T > 0`, and its `O(1/T)` form
  `TauCeti.isBigO_riemannSiegelTheta_sub`.

The integral is the continuous branch: the principal logarithm of `Γ(1/4 + iT/2)` has bounded
imaginary part, while `ϑ(T)` grows like `(T/2) log (T/(2πe))`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (revised by
  D. R. Heath-Brown), §§4.17 and 9.3.
* R. P. Brent, *On asymptotic approximations to the log-Gamma and Riemann-Siegel theta
  functions*, J. Aust. Math. Soc. 107 (2019), 319–337, §1 (the definition of `ϑ` as the continuous
  argument of `Γ(1/4 + iT/2)` minus `(T/2) log π`).
* G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. Roy. Soc. Edinburgh Sect. A 145 (2015), 571–596, for the
  bound on the Stirling remainder used in the asymptotic.
-/

public section

open Complex Filter Asymptotics Set
open scoped Real Topology

namespace TauCeti

/-- The point `1/4 + iT/2` lies in the slit plane: its real part is positive. -/
private theorem quarter_add_mem_slitPlane (T : ℝ) : (1 / 4 + (T : ℂ) / 2 * I) ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by simp))

/-- The integrand of `riemannSiegelTheta` is continuous. -/
private theorem continuous_riemannSiegelTheta_integrand :
    Continuous fun t : ℝ ↦ ((digamma (1 / 4 + (t : ℂ) / 2 * I)).re - Real.log π) / 2 := by
  have hψ : Continuous fun t : ℝ ↦ digamma (1 / 4 + (t : ℂ) / 2 * I) := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ContinuousAt.comp ?_ (by fun_prop)
    -- `ψ = Γ'/Γ` is analytic at `1/4 + it/2`, where `Γ` is analytic and nonzero.
    have hs := ne_neg_natCast_of_re_pos (b := 1 / 4 + (t : ℂ) / 2 * I) (by simp)
    exact ((analyticAt_Gamma hs).deriv.div (analyticAt_Gamma hs) (Gamma_ne_zero hs)).continuousAt
  fun_prop

/-- The Riemann–Siegel theta function `ϑ(T) = ∫₀^T (Re ψ(1/4 + it/2) - log π) / 2 dt`, where `ψ` is
the digamma function. It is the continuous argument of `Γℝ(1/2 + iT)` normalized by `ϑ(0) = 0`
(`TauCeti.Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta`). -/
noncomputable def riemannSiegelTheta (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, ((digamma (1 / 4 + (t : ℂ) / 2 * I)).re - Real.log π) / 2

/-- Unfolding formula for `TauCeti.riemannSiegelTheta`. -/
theorem riemannSiegelTheta_def (T : ℝ) :
    riemannSiegelTheta T =
      ∫ t in (0 : ℝ)..T, ((digamma (1 / 4 + (t : ℂ) / 2 * I)).re - Real.log π) / 2 := (rfl)

/-- The Riemann–Siegel theta function vanishes at `0`. -/
@[simp]
theorem riemannSiegelTheta_zero : riemannSiegelTheta 0 = 0 := by
  rw [riemannSiegelTheta_def, intervalIntegral.integral_same]

/-- `T ↦ Im log Γ(1/4 + iT/2) - (T/2) log π` has derivative `(Re ψ(1/4 + iT/2) - log π) / 2`. -/
private theorem hasDerivAt_im_logGamma_sub (T : ℝ) :
    HasDerivAt (fun T : ℝ ↦ (logGamma (1 / 4 + (T : ℂ) / 2 * I)).im - T / 2 * Real.log π)
      (((digamma (1 / 4 + (T : ℂ) / 2 * I)).re - Real.log π) / 2) T := by
  have hpath : HasDerivAt (fun T : ℝ ↦ (1 / 4 + (T : ℂ) / 2 * I)) (1 / 2 * I) T := by
    simpa using (((hasDerivAt_id (T : ℂ)).comp_ofReal (z := T)).div_const 2).mul_const I
      |>.const_add (1 / 4 : ℂ)
  have hL := (hasDerivAt_logGamma (quarter_add_mem_slitPlane T)).comp T hpath
  have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt T hL).sub
    ((hasDerivAt_id T).div_const 2 |>.mul_const (Real.log π))
  convert him using 1
  · ext; simp
  · simp [mul_im]
    ring

/-- **`ϑ` is the continuous argument of `Γ(1/4 + iT/2)` minus `(T/2) log π`.** With the branch
`TauCeti.logGamma` of `log Γ` on the slit plane, real on the positive axis,
`ϑ(T) = Im log Γ(1/4 + iT/2) - (T/2) log π`. -/
theorem riemannSiegelTheta_eq_im_logGamma (T : ℝ) :
    riemannSiegelTheta T = (logGamma (1 / 4 + (T : ℂ) / 2 * I)).im - T / 2 * Real.log π := by
  rw [riemannSiegelTheta_def, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_im_logGamma_sub t)
    (continuous_riemannSiegelTheta_integrand.intervalIntegrable 0 T)]
  have h0 : (1 / 4 + ((0 : ℝ) : ℂ) / 2 * I) = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [h0, logGamma_ofReal (by norm_num)]
  simp

/-- The derivative of the Riemann–Siegel theta function:
`ϑ'(T) = (Re ψ(1/4 + iT/2) - log π) / 2`. -/
theorem hasDerivAt_riemannSiegelTheta (T : ℝ) :
    HasDerivAt riemannSiegelTheta
      (((digamma (1 / 4 + (T : ℂ) / 2 * I)).re - Real.log π) / 2) T := by
  rw [funext riemannSiegelTheta_eq_im_logGamma]
  exact hasDerivAt_im_logGamma_sub T

/-- The derivative of the Riemann–Siegel theta function, as a value of `deriv`. -/
theorem deriv_riemannSiegelTheta (T : ℝ) :
    deriv riemannSiegelTheta T = ((digamma (1 / 4 + (T : ℂ) / 2 * I)).re - Real.log π) / 2 :=
  (hasDerivAt_riemannSiegelTheta T).deriv

/-- The Riemann–Siegel theta function is differentiable. -/
theorem differentiable_riemannSiegelTheta : Differentiable ℝ riemannSiegelTheta :=
  fun T ↦ (hasDerivAt_riemannSiegelTheta T).differentiableAt

/-- The Riemann–Siegel theta function is continuous. -/
theorem continuous_riemannSiegelTheta : Continuous riemannSiegelTheta :=
  differentiable_riemannSiegelTheta.continuous

/-- The Riemann–Siegel theta function is odd. -/
@[simp]
theorem riemannSiegelTheta_neg (T : ℝ) : riemannSiegelTheta (-T) = -riemannSiegelTheta T := by
  have h : (1 / 4 + ((-T : ℝ) : ℂ) / 2 * I) = (starRingEnd ℂ) (1 / 4 + (T : ℂ) / 2 * I) := by
    apply Complex.ext <;> simp [map_ofNat, neg_div]
  rw [riemannSiegelTheta_eq_im_logGamma, riemannSiegelTheta_eq_im_logGamma, h,
    logGamma_conj (quarter_add_mem_slitPlane T), conj_im]
  ring

/-- **`ϑ(t)` is an argument of `Γℝ(1/2 + it)`:**
`Γℝ(1/2 + it) = |Γℝ(1/2 + it)| e^{iϑ(t)}`. -/
theorem Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta (t : ℝ) :
    Gammaℝ (1 / 2 + t * I) = ‖Gammaℝ (1 / 2 + t * I)‖ * exp (riemannSiegelTheta t * I) := by
  set z : ℂ := 1 / 4 + (t : ℂ) / 2 * I
  have hz : (1 / 2 + t * I) / 2 = z := by simp only [z]; ring
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  -- `Γℝ(1/2 + it) = π^(-z) Γ(z) = exp w` with `w = -z log π + log Γ(z)`.
  set w : ℂ := -(Real.log π : ℂ) * z + logGamma z with hw_def
  have hG : Gammaℝ (1 / 2 + t * I) = exp w := by
    rw [Gammaℝ_def, neg_div, hz, cpow_def_of_ne_zero hπ, ← ofReal_log Real.pi_pos.le,
      ← exp_logGamma (quarter_add_mem_slitPlane t), ← exp_add, hw_def, neg_mul, mul_neg]
  have hw : w.im = riemannSiegelTheta t := by
    rw [riemannSiegelTheta_eq_im_logGamma]
    simp only [w, z, add_im, mul_im, neg_re, neg_im, ofReal_re, ofReal_im]
    simp
    ring
  rw [hG, norm_exp, ← hw, ofReal_exp, ← exp_add]
  congr 1
  apply Complex.ext <;> simp

/-- **Hardy's function through the theta function.** Mathlib's `hardyZ t`, the quotient
`Λ(1/2 + it)/|Γℝ(1/2 + it)|`, is `e^{iϑ(t)} ζ(1/2 + it)`. -/
theorem hardyZ_eq_exp_riemannSiegelTheta_mul (t : ℝ) :
    (hardyZ t : ℂ) = exp (riemannSiegelTheta t * I) * riemannZeta (1 / 2 + t * I) := by
  have hs : (1 / 2 + t * I : ℂ) ≠ 0 := fun h ↦ by simpa using congrArg re h
  rw [ofReal_hardyZ, riemannZeta_def_of_ne_zero hs]
  conv_rhs => rw [Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta]
  field_simp [exp_ne_zero]

/-- **The Stirling form of `ϑ`.** At `z = 1/4 + iT/2`,
`ϑ(T) = (T/2) log |z| - (arg z)/4 - T/2 - (T/2) log π + Im R(z)`, where `R` is the Stirling
remainder `TauCeti.stirlingRemainder`. -/
theorem riemannSiegelTheta_eq_add_im_stirlingRemainder (T : ℝ) :
    riemannSiegelTheta T =
      T / 2 * Real.log ‖(1 / 4 + (T : ℂ) / 2 * I)‖ - (1 / 4 + (T : ℂ) / 2 * I).arg / 4 - T / 2 -
        T / 2 * Real.log π + (stirlingRemainder (1 / 4 + (T : ℂ) / 2 * I)).im := by
  rw [riemannSiegelTheta_eq_im_logGamma, logGamma_eq_add_stirlingRemainder]
  simp only [add_im, sub_im, mul_im, log_re, log_im, ofReal_im]
  simp
  ring

/-- The modulus term: `0 ≤ (T/2) log |1/4 + iT/2| - (T/2) log (T/2) ≤ 1/(16T)` for `T > 0`. -/
private theorem log_norm_quarter_add_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ T / 2 * Real.log ‖(1 / 4 + (T : ℂ) / 2 * I)‖ - T / 2 * Real.log (T / 2) ∧
      T / 2 * Real.log ‖(1 / 4 + (T : ℂ) / 2 * I)‖ - T / 2 * Real.log (T / 2) ≤ 1 / (16 * T) := by
  have hnorm : ‖(1 / 4 + (T : ℂ) / 2 * I)‖ = Real.sqrt ((T / 2) ^ 2 * (1 + 1 / (4 * T ^ 2))) := by
    rw [norm_def, normSq_apply]
    congr 1
    simp
    field_simp
    ring
  have hx : 0 ≤ 1 / (4 * T ^ 2) := by positivity
  rw [hnorm, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity)]
  have hlog0 : 0 ≤ Real.log (1 + 1 / (4 * T ^ 2)) := Real.log_nonneg (by linarith)
  have hlog1 : Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / (4 * T ^ 2) := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (4 * T ^ 2) by positivity)]
  constructor
  · nlinarith
  · have : T / 2 * (Real.log (1 + 1 / (4 * T ^ 2)) / 2) ≤ T / 2 * (1 / (4 * T ^ 2) / 2) := by
      gcongr
    calc T / 2 * (Real.log (T / 2) + Real.log (1 + 1 / (4 * T ^ 2)) / 2) -
          T / 2 * Real.log (T / 2) = T / 2 * (Real.log (1 + 1 / (4 * T ^ 2)) / 2) := by ring
      _ ≤ T / 2 * (1 / (4 * T ^ 2) / 2) := this
      _ = 1 / (16 * T) := by field_simp; ring

/-- The argument term: `arg (1/4 + iT/2) = π/2 - arctan (1/(2T))` for `T > 0`, so
`0 ≤ π/8 - arg (1/4 + iT/2) / 4 ≤ 1/(8T)`. -/
private theorem arg_quarter_add_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ π / 8 - (1 / 4 + (T : ℂ) / 2 * I).arg / 4 ∧
      π / 8 - (1 / 4 + (T : ℂ) / 2 * I).arg / 4 ≤ 1 / (8 * T) := by
  have him : 0 < (1 / 4 + (T : ℂ) / 2 * I).im := by simpa using hT
  rw [arg_eq_pi_div_two_sub_arctan_of_im_pos him]
  have hq : (1 / 4 + (T : ℂ) / 2 * I).re / (1 / 4 + (T : ℂ) / 2 * I).im = 1 / (2 * T) := by
    simp
    field_simp
    norm_num
  rw [hq]
  have h0 : 0 ≤ Real.arctan (1 / (2 * T)) := Real.arctan_nonneg.mpr (by positivity)
  have h1 : Real.arctan (1 / (2 * T)) ≤ 1 / (2 * T) := Real.arctan_le_self (by positivity)
  constructor
  · linarith
  · have : 1 / (2 * T) / 4 = 1 / (8 * T) := by field_simp; ring
    linarith

/-- The remainder term: `|Im R(1/4 + iT/2)| ≤ 1/(2T)` for `T > 0`, from Nemes's slit-plane bound
`|R(z)| ≤ 1/(8 cos² (arg z / 2) |z|)`, with `0 < arg z < π/2` and `|z| ≥ T/2`. -/
private theorem abs_im_stirlingRemainder_quarter_add_le {T : ℝ} (hT : 0 < T) :
    |(stirlingRemainder (1 / 4 + (T : ℂ) / 2 * I)).im| ≤ 1 / (2 * T) := by
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I
  have hre : 0 ≤ z.re := by simp [z]
  have harg0 : 0 ≤ z.arg := arg_nonneg_iff.mpr (by rw [show z.im = T / 2 by simp [z]]; positivity)
  have harg1 : z.arg ≤ π / 2 := arg_le_pi_div_two_iff.mpr (Or.inl hre)
  have hcos : 1 / 2 ≤ Real.cos (z.arg / 2) ^ 2 := by
    rw [Real.cos_sq, show 2 * (z.arg / 2) = z.arg by ring]
    linarith [Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) harg1]
  have hnorm : T / 2 ≤ ‖z‖ := by
    calc T / 2 = |z.im| := by simp [z, abs_of_pos (half_pos hT)]
      _ ≤ ‖z‖ := abs_im_le_norm z
  have hR := norm_stirlingRemainder_le (quarter_add_mem_slitPlane T)
  calc |(stirlingRemainder z).im| ≤ ‖stirlingRemainder z‖ := abs_im_le_norm _
    _ ≤ 1 / (8 * Real.cos (z.arg / 2) ^ 2 * ‖z‖) := hR
    _ ≤ 1 / (8 * (1 / 2) * (T / 2)) := by gcongr
    _ = 1 / (2 * T) := by field_simp; ring

/-- **The asymptotic of `ϑ` with an explicit error.** For `T > 0`,
`|ϑ(T) - ((T/2) log (T/(2πe)) - π/8)| ≤ 1/T`. -/
theorem abs_riemannSiegelTheta_sub_le {T : ℝ} (hT : 0 < T) :
    |riemannSiegelTheta T - (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8)| ≤ 1 / T := by
  obtain ⟨hm0, hm1⟩ := log_norm_quarter_add_bounds hT
  obtain ⟨ha0, ha1⟩ := arg_quarter_add_bounds hT
  have hR := abs_le.mp (abs_im_stirlingRemainder_quarter_add_le hT)
  have hmain : T / 2 * Real.log (T / (2 * π * Real.exp 1)) =
      T / 2 * Real.log (T / 2) - T / 2 - T / 2 * Real.log π := by
    rw [Real.log_div hT.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul two_ne_zero Real.pi_ne_zero, Real.log_exp, Real.log_div hT.ne' two_ne_zero]
    ring
  have h16 : 1 / (16 * T) + 1 / (8 * T) + 1 / (2 * T) = 11 / 16 * (1 / T) := by
    field_simp
    ring
  have hT1 : 0 < 1 / T := one_div_pos.mpr hT
  rw [riemannSiegelTheta_eq_add_im_stirlingRemainder, hmain, abs_le]
  constructor <;> linarith

/-- **The asymptotic of `ϑ`:** `ϑ(T) = (T/2) log (T/(2πe)) - π/8 + O(1/T)` as `T → ∞`. -/
theorem isBigO_riemannSiegelTheta_sub :
    (fun T ↦ riemannSiegelTheta T - (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8))
      =O[atTop] fun T ↦ T⁻¹ := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hT, one_mul, ← one_div]
  exact abs_riemannSiegelTheta_sub_le hT

end TauCeti
