/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Dirac fundamental matrix of a real potential at `z = 0`

For a potential `q = f` that is integrable and real between `0` and `t`, the Dirac coefficient
at the spectral parameter `0` is the diagonal matrix `diag(f, -f)` there, and the fundamental
matrix is `M(t, 0) = diag(e^{F(t)}, e^{-F(t)})` with `F(t) = ∫₀ᵗ f`
(`TauCeti.diracFundamentalMatrix_spectralParam_zero_of_im_eq_zero`). For a real constant
`q = c` this is `M_c(t, 0) = diag(e^{ct}, e^{-ct})`
(`TauCeti.diracFundamentalMatrix_ofReal_const_spectralParam_zero`), which fixes the sign
convention of the system.

The scalar equation `y' = h y`, `y(0) = 1`, with `h` integrable, is solved by `y = exp(∫₀ᵗ h)`
(`TauCeti.propagator_smul_one_apply_one`, a consequence of Liouville's formula). The columns of
the fundamental matrix are then the solutions `e^{F} e₀` and `e^{-F} e₁` of the Dirac integral
equation between `0` and `t`, by uniqueness for the propagator.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- If `e_i` is an eigenvector of the Dirac coefficient at `z = 0` with eigenvalue `c f(s)` for
every `s` between `0` and `t`, then the column `M_q(t, 0) e_i` is `exp(∫₀ᵗ c f) e_i`: the
curve `r ↦ exp(∫₀ʳ c f) e_i` solves the Dirac integral equation between `0` and `t`. -/
private theorem diracFundamentalMatrix_spectralParam_zero_mulVec_single
    (hq : IntegrableOn q (uIcc 0 t)) (i : Fin 2) (c : ℝ)
    (hc : ∀ s ∈ uIcc 0 t,
      diracCoeff q 0 s *ᵥ Pi.single i 1 = ((c * (q s).re : ℝ) : ℂ) • Pi.single i 1) :
    diracFundamentalMatrix q t 0 *ᵥ Pi.single i 1 =
      (Real.exp (∫ s in (0 : ℝ)..t, c * (q s).re) : ℂ) • (Pi.single i 1 : Fin 2 → ℂ) := by
  have hf : IntegrableOn (fun s ↦ c * (q s).re) (uIcc 0 t) := hq.re.const_mul c
  set X : ℝ → Fin 2 → ℂ := fun r ↦
    (Real.exp (∫ s in (0 : ℝ)..r, c * (q s).re) : ℂ) • (Pi.single i 1 : Fin 2 → ℂ)
  have hcont : ContinuousOn X (uIcc 0 t) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := 0)
      hf.intervalIntegrable left_mem_uIcc
    exact (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn this)).smul continuousOn_const
  have hexp (r : ℝ) (hr : r ∈ uIcc 0 t) :
      propagator (fun u ↦ ((c * (q u).re : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) r 0 1 =
        Real.exp (∫ s in (0 : ℝ)..r, c * (q s).re) := by
    rw [Complex.ofReal_exp, ← intervalIntegral.integral_ofReal, Complex.exp_eq_exp_ℂ]
    -- The integral below is taken with the `RCLike ℂ` instances, which unfold to those of `ℂ`.
    exact propagator_smul_one_apply_one hf.ofReal left_mem_uIcc hr
  have hX (r : ℝ) (hr : r ∈ uIcc 0 t) :
      X r = X 0 + ∫ s in (0 : ℝ)..r, diracCoeff q 0 s *ᵥ X s := by
    have hsol := propagator_apply_eq_add_integral
      (P := fun u ↦ ((c * (q u).re : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (hf.ofReal.smul_const _)
      left_mem_uIcc hr 1
    rw [hexp r hr] at hsol
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul] at hsol
    have hint : ∫ s in (0 : ℝ)..r, diracCoeff q 0 s *ᵥ X s =
        (∫ s in (0 : ℝ)..r, ((c * (q s).re : ℝ) : ℂ) *
          propagator (fun u ↦ ((c * (q u).re : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) s 0 1) •
            (Pi.single i 1 : Fin 2 → ℂ) := by
      rw [← intervalIntegral.integral_smul_const]
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      have hs' : s ∈ uIcc 0 t := uIcc_subset_uIcc_left hr hs
      rw [hexp s hs', mulVec_smul, hc s hs', smul_smul, mul_comm]
    simp only [X]
    rw [hint, intervalIntegral.integral_same, Real.exp_zero, Complex.ofReal_one, one_smul, hsol,
      add_smul, one_smul]
  -- Uniqueness for the propagator of the coefficient on `EuclideanSpace ℂ (Fin 2)`.
  have key := eq_propagator_apply (integrableOn_toEuclideanCLM_diracCoeff hq 0)
    left_mem_uIcc right_mem_uIcc (x := fun r ↦ WithLp.toLp 2 (X r))
    ((PiLp.continuous_toLp 2 _).comp_continuousOn hcont) fun r hr ↦ by
      rw [WithLp.ext_iff, WithLp.ofLp_add, PiLp.ofLp_intervalIntegral]
      simpa using hX r hr
  have h0 : X 0 = Pi.single i 1 := by simp [X]
  have := congrArg WithLp.ofLp key
  rw [← toEuclideanCLM_diracFundamentalMatrix, ofLp_toEuclideanCLM, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp, h0] at this
  exact this.symm

/-- **A real potential at `z = 0`.** For a potential `q`, integrable and real between `0` and
`t` (in either order), `M_q(t, 0) = diag(e^{F(t)}, e^{-F(t)})` with `F(t) = ∫₀ᵗ Re q`. -/
theorem diracFundamentalMatrix_spectralParam_zero_of_im_eq_zero (hq : IntegrableOn q (uIcc 0 t))
    (hre : ∀ s ∈ uIcc 0 t, (q s).im = 0) :
    diracFundamentalMatrix q t 0 =
      !![(Real.exp (∫ s in (0 : ℝ)..t, (q s).re) : ℂ), 0;
        0, (Real.exp (-∫ s in (0 : ℝ)..t, (q s).re) : ℂ)] := by
  have h0 := diracFundamentalMatrix_spectralParam_zero_mulVec_single hq 0 1 fun s hs ↦ by
    ext k; fin_cases k <;> simp [diracCoeff_def, hre s hs]
  have h1 := diracFundamentalMatrix_spectralParam_zero_mulVec_single hq 1 (-1) fun s hs ↦ by
    ext k; fin_cases k <;> simp [diracCoeff_def, hre s hs]
  simp only [mulVec_single, one_mul, neg_one_mul, intervalIntegral.integral_neg] at h0 h1
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using congrFun h0 0
  · simpa using congrFun h1 0
  · simpa using congrFun h0 1
  · simpa using congrFun h1 1

/-- **A real constant potential at `z = 0`.** For `q = c` real, the fundamental matrix at the
spectral parameter `0` is `M_c(t, 0) = diag(e^{ct}, e^{-ct})`. The opposite sign convention
`Ω X' = z X + Q_q X` would give `diag(e^{-ct}, e^{ct})`. -/
theorem diracFundamentalMatrix_ofReal_const_spectralParam_zero (c t : ℝ) :
    diracFundamentalMatrix (fun _ ↦ (c : ℂ)) t 0 =
      !![(Real.exp (c * t) : ℂ), 0; 0, (Real.exp (-(c * t)) : ℂ)] := by
  rw [diracFundamentalMatrix_spectralParam_zero_of_im_eq_zero continuousOn_const.integrableOn_uIcc
    fun _ _ ↦ Complex.ofReal_im c]
  simp [mul_comm]

end TauCeti
