/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.Contour.Argument.Lift

/-!
# The Riemann–Siegel theta function

The Riemann–Siegel theta function is
`ϑ(T) = ∫₀^T (Re ψ(1/4 + it/2) - log π) / 2 dt`, where `ψ = Γ'/Γ` is `Complex.digamma`. It is the
continuous argument of the archimedean factor `Γℝ(1/2 + iT) = π^(-1/4 - iT/2) Γ(1/4 + iT/2)` of the
completed zeta function on the critical line, normalized by `ϑ(0) = 0`. It enters the zero count of
`ζ` through `N(T) = ϑ(T)/π + 1 + S(T)`, valid for `T > 0` that is not the ordinate of a zero (at a
zero ordinate, with `N(T)` counting zeros of height up to and including `T`, one uses the
right-hand limit of `S`), and the Riemann–Siegel formula through Hardy's function
`Z(t) = e^{iϑ(t)} ζ(1/2 + it)`.

This file proves:

* `TauCeti.riemannSiegelTheta_eq_im_logGamma_sub`:
  `ϑ(T) = Im log Γ(1/4 + iT/2) - (T/2) log π`, with the branch `TauCeti.logGamma` of `log Γ` on
  the slit plane that is real on the positive axis;
* the derivative `ϑ'(T) = (Re ψ(1/4 + iT/2) - log π) / 2` and the oddness `ϑ(-T) = -ϑ(T)`;
* `TauCeti.Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta`:
  `Γℝ(1/2 + it) = |Γℝ(1/2 + it)| e^{iϑ(t)}`, and its converse
  `TauCeti.eq_riemannSiegelTheta_of_continuous_normalized_phase`: every continuous real phase
  of `Γℝ(1/2 + it)` vanishing at `0` is `ϑ`.

The integral is the continuous branch: the principal logarithm of `Γ(1/4 + iT/2)` has bounded
imaginary part, while `ϑ(T)` grows like `(T/2) log (T/(2πe))`. Hardy's function is related to `ϑ`
in `TauCeti/NumberTheory/LSeries/RiemannZeta/RiemannSiegelTheta/HardyZ.lean`, and the Stirling
asymptotic of `ϑ` is in
`TauCeti/NumberTheory/LSeries/RiemannZeta/RiemannSiegelTheta/Asymptotics.lean`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (revised by
  D. R. Heath-Brown), §§4.17 and 9.3.
* R. P. Brent, *On asymptotic approximations to the log-Gamma and Riemann-Siegel theta
  functions*, J. Aust. Math. Soc. 107 (2019), 319–337, §1 (the definition of `ϑ` as the continuous
  argument of `Γ(1/4 + iT/2)` minus `(T/2) log π`).
-/

public section

open Complex Set
open scoped Real

namespace TauCeti

/-- The Riemann–Siegel theta function
  `ϑ(T) = ∫₀^T (Re ψ(1/4 + it/2) - log π) / 2 dt`, where `ψ` is
the digamma function. It is the continuous argument of `Γℝ(1/2 + iT)` normalized by `ϑ(0) = 0`
(`TauCeti.Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta`,
`TauCeti.eq_riemannSiegelTheta_of_continuous_normalized_phase`). -/
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

private theorem one_quarter_add_div_two_mul_I (T : ℝ) :
    ((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I = 1 / 4 + (T : ℂ) / 2 * I := by
  push_cast
  ring

/-- `T ↦ Im log Γ(1/4 + iT/2) - (T/2) log π` has derivative `(Re ψ(1/4 + iT/2) - log π) / 2`. -/
private theorem hasDerivAt_im_logGamma_sub (T : ℝ) :
    HasDerivAt (fun T : ℝ ↦ (logGamma (1 / 4 + (T : ℂ) / 2 * I)).im - T / 2 * Real.log π)
      (((digamma (1 / 4 + (T : ℂ) / 2 * I)).re - Real.log π) / 2) T := by
  have hmem : ((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I ∈ slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  have him := ((hasDerivAt_im_logGamma_ofReal_add_mul_I hmem).comp T
    ((hasDerivAt_id T).div_const 2)).sub ((hasDerivAt_id T).div_const 2 |>.mul_const (Real.log π))
  simp only [Function.comp_def, id, one_quarter_add_div_two_mul_I] at him
  convert him using 1
  ring

/-- **`ϑ` is the continuous argument of `Γ(1/4 + iT/2)` minus `(T/2) log π`.** With the branch
`TauCeti.logGamma` of `log Γ` on the slit plane, real on the positive axis,
`ϑ(T) = Im log Γ(1/4 + iT/2) - (T/2) log π`. -/
theorem riemannSiegelTheta_eq_im_logGamma_sub (T : ℝ) :
    riemannSiegelTheta T = (logGamma (1 / 4 + (T : ℂ) / 2 * I)).im - T / 2 * Real.log π := by
  rw [riemannSiegelTheta_def]
  -- Expose `t ↦ t / 2` for the change of variables and the general vertical integral.
  simp_rw [← one_quarter_add_div_two_mul_I]
  rw [intervalIntegral.integral_comp_div (a := 0) (b := T) (c := 2)
    (f := fun t : ℝ => ((digamma (((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)).re - Real.log π) / 2)
    (by norm_num)]
  simp only [zero_div, smul_eq_mul, intervalIntegral.integral_div]
  have hre : Continuous fun t : ℝ => (digamma (((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)).re :=
    Complex.continuous_re.comp (continuous_digamma_ofReal_add_mul_I (by norm_num))
  rw [intervalIntegral.integral_sub
    (hre.intervalIntegrable 0 (T / 2)) intervalIntegrable_const]
  rw [integral_re_digamma_ofReal_add_mul_I (σ := 1 / 4) (by norm_num) (T / 2),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The derivative of the Riemann–Siegel theta function:
`ϑ'(T) = (Re ψ(1/4 + iT/2) - log π) / 2`. -/
theorem hasDerivAt_riemannSiegelTheta (T : ℝ) :
    HasDerivAt riemannSiegelTheta
      (((digamma (1 / 4 + (T : ℂ) / 2 * I)).re - Real.log π) / 2) T := by
  rw [funext riemannSiegelTheta_eq_im_logGamma_sub]
  exact hasDerivAt_im_logGamma_sub T

/-- The derivative of the Riemann–Siegel theta function, as a value of `deriv`. -/
theorem deriv_riemannSiegelTheta (T : ℝ) :
    deriv riemannSiegelTheta T = ((digamma (1 / 4 + (T : ℂ) / 2 * I)).re - Real.log π) / 2 :=
  (hasDerivAt_riemannSiegelTheta T).deriv

/-- The Riemann–Siegel theta function is differentiable. -/
@[fun_prop]
theorem differentiable_riemannSiegelTheta : Differentiable ℝ riemannSiegelTheta :=
  fun T ↦ (hasDerivAt_riemannSiegelTheta T).differentiableAt

/-- The Riemann–Siegel theta function is continuous. -/
@[fun_prop]
theorem continuous_riemannSiegelTheta : Continuous riemannSiegelTheta :=
  differentiable_riemannSiegelTheta.continuous

/-- The Riemann–Siegel theta function is odd. -/
@[simp]
theorem riemannSiegelTheta_neg (T : ℝ) : riemannSiegelTheta (-T) = -riemannSiegelTheta T := by
  have h : (1 / 4 + ((-T : ℝ) : ℂ) / 2 * I) = (starRingEnd ℂ) (1 / 4 + (T : ℂ) / 2 * I) := by
    apply Complex.ext <;> simp [map_ofNat, neg_div]
  rw [riemannSiegelTheta_eq_im_logGamma_sub, riemannSiegelTheta_eq_im_logGamma_sub, h,
    logGamma_conj (Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))), conj_im]
  ring

/-- **`ϑ(t)` is an argument of `Γℝ(1/2 + it)`:**
`Γℝ(1/2 + it) = |Γℝ(1/2 + it)| e^{iϑ(t)}`. -/
theorem Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta (t : ℝ) :
    Gammaℝ (1 / 2 + t * I) = ‖Gammaℝ (1 / 2 + t * I)‖ * exp (riemannSiegelTheta t * I) := by
  set z : ℂ := 1 / 4 + (t : ℂ) / 2 * I
  have hz : (1 / 2 + t * I) / 2 = z := by simp only [z]; ring
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  -- `Γℝ(1/2 + it) = π^(-z) Γ(z) = exp w` with `w = log Γ(z) - z log π`.
  set w : ℂ := logGamma z - z * (Real.log π : ℂ) with hw_def
  have hp_pow : ((π : ℂ) ^ (-z)) = exp (-z * (Real.log π : ℂ)) := by
    rw [cpow_def_of_ne_zero hπ, ← ofReal_log Real.pi_pos.le]
    congr 1
    ring
  have hG : Gammaℝ (1 / 2 + t * I) = exp w := by
    rw [Gammaℝ_def, neg_div, hz, hp_pow,
      ← exp_logGamma (Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [z]))), ← exp_add, hw_def]
    congr 1
    ring
  have hdecomp : exp w = ‖exp w‖ * exp (w.im * I) := by
    rw [norm_exp, ofReal_exp, ← exp_add, re_add_im]
  have hw : w.im = riemannSiegelTheta t := by
    rw [riemannSiegelTheta_eq_im_logGamma_sub]
    simp [w, z]
  calc
    Gammaℝ (1 / 2 + t * I) = exp w := hG
    _ = ‖exp w‖ * exp (w.im * I) := hdecomp
    _ = ‖Gammaℝ (1 / 2 + t * I)‖ * exp (riemannSiegelTheta t * I) := by
      rw [hw, ← hG]

/-- **Uniqueness of the normalized phase.** A continuous real function `f` with
`Γℝ(1/2 + it) = |Γℝ(1/2 + it)| e^{i f(t)}` for all `t` and `f(0) = 0` is the Riemann–Siegel theta
function. -/
theorem eq_riemannSiegelTheta_of_continuous_normalized_phase {f : ℝ → ℝ}
    (hf : Continuous f)
    (hphase : ∀ t : ℝ, Gammaℝ (1 / 2 + t * I) = ‖Gammaℝ (1 / 2 + t * I)‖ * exp (f t * I))
    (h0 : f 0 = 0) : f = riemannSiegelTheta := by
  funext t
  have hsub := Contour.sub_eq_sub_of_eq_norm_mul_exp
    (f := fun t : ℝ => Gammaℝ (1 / 2 + t * I))
    (φ := f) (φ' := riemannSiegelTheta) (x := 0) (y := t)
    isPreconnected_univ (mem_univ 0) (mem_univ t)
    (fun _ _ => Gammaℝ_ne_zero_of_re_pos (by simp))
    hf.continuousOn continuous_riemannSiegelTheta.continuousOn
    (fun p _ => by simpa only [mul_comm I] using hphase p)
    (fun p _ => by
      simpa only [mul_comm I] using
        Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta p)
  simpa [h0, riemannSiegelTheta_zero] using hsub

end TauCeti
