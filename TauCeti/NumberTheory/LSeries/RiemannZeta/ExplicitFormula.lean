/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Analysis.Complex.Hadamard.Riesz
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Riesz
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RieszMellin
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The zero side of the first Riesz formula for zeta

The sum over the nontrivial zeros, the correction from the strictly negative even integers,
and the constant `log (2π)` together have Mellin transform `rieszRemainderMellin riemannZeta` on
`Re s > 1`, the expression expected to be the Mellin transform of the first Riesz remainder;
matching it with the prime side is not done here.
The calculation uses Hadamard factorization of the entire completion and the shifted real gamma
factor; the shift omits zero from the gamma correction. This supplies the zero side of a proof
of the explicit formula by Mellin uniqueness.

The normalization of the remainder is that of Levent Alpöge's `Formalism.Gz`. For the zeta
completion and its Hadamard product, see H. Davenport, *Multiplicative Number Theory*, §12.
-/

public section

open Complex DirichletCharacter MeasureTheory Set

namespace TauCeti

open LFunctions

/-- The zero side of the first Riesz formula for zeta, on `y ≥ 1`. The two series are
respectively over the zeros of the entire completion and the strictly negative trivial zeros;
`log (2π)` is the contribution from the origin. -/
noncomputable def riemannZetaRieszZeroSide (y : ℝ) : ℂ :=
  rieszZeroSeries zetaEntireCompletion y + rieszGammaCorrection 2 2 y +
    (Real.log (2 * Real.pi) : ℂ)

/-- The decomposition into the nontrivial-zero series, the gamma correction, and the origin. -/
theorem riemannZetaRieszZeroSide_def (y : ℝ) :
    riemannZetaRieszZeroSide y =
      rieszZeroSeries zetaEntireCompletion y + rieszGammaCorrection 2 2 y +
        (Real.log (2 * Real.pi) : ℂ) := (rfl)

/-- The zero side is continuous on the closed ray, including the endpoint of the Mellin tail. -/
theorem continuousOn_riemannZetaRieszZeroSide : ContinuousOn riemannZetaRieszZeroSide (Ici 1) := by
  simp only [funext riemannZetaRieszZeroSide_def]
  exact ((orderLE_zetaEntireCompletion.continuousOn_rieszZeroSeries
    differentiable_zetaEntireCompletion (by norm_num)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le)).add
    (continuousOn_rieszGammaCorrection (by norm_num) (by norm_num))).add continuousOn_const

/-- The Mellin integral of the zero side converges absolutely for `Re s > 1`. -/
theorem integrableOn_riemannZetaRieszZeroSide_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ riemannZetaRieszZeroSide y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  simp only [riemannZetaRieszZeroSide_def, add_mul]
  exact ((orderLE_zetaEntireCompletion.integrableOn_rieszZeroSeries_mul_cpow
    differentiable_zetaEntireCompletion (by norm_num)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le) hs).add
    (integrableOn_rieszGammaCorrection_mul_cpow (by norm_num) (by norm_num) (by linarith))).add
    ((integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).const_mul _)

/-- The Mellin integral of the zero side splits into the zero series, the gamma correction, and
the Mellin transform `1 / s` of the constant `log (2π)`. -/
theorem integral_riemannZetaRieszZeroSide_mul_cpow_eq_add {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 1, riemannZetaRieszZeroSide y * (y : ℂ) ^ (-s - 1)) =
      (∫ y : ℝ in Ioi 1, rieszZeroSeries zetaEntireCompletion y * (y : ℂ) ^ (-s - 1)) +
        (∫ y : ℝ in Ioi 1, rieszGammaCorrection 2 2 y * (y : ℂ) ^ (-s - 1)) +
          (Real.log (2 * Real.pi) : ℂ) * s⁻¹ := by
  have hZ := orderLE_zetaEntireCompletion.integrableOn_rieszZeroSeries_mul_cpow
    differentiable_zetaEntireCompletion (by norm_num)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le) hs
  have hG := integrableOn_rieszGammaCorrection_mul_cpow (a := 2) (d := 2) (s := s)
    (by norm_num) (by norm_num) (by linarith)
  have hExp : (-s - 1).re < -1 := by simp; linarith
  simp only [riemannZetaRieszZeroSide_def, add_mul]
  rw [integral_add (f := fun y : ℝ ↦ rieszZeroSeries zetaEntireCompletion y * (y : ℂ) ^ (-s - 1) +
      rieszGammaCorrection 2 2 y * (y : ℂ) ^ (-s - 1)) (hZ.add hG)
      ((integrableOn_Ioi_cpow_of_lt hExp zero_lt_one).const_mul _),
    integral_add hZ hG, integral_const_mul, integral_Ioi_cpow_of_lt hExp zero_lt_one]
  simp [div_eq_mul_inv]

/-- For `Re s > 1`, the Hadamard combination `ξ'/ξ(0) + s (ξ'/ξ(1) - ξ'/ξ(0)) - ξ'/ξ(s)` of the
entire completion `ξ` of zeta equals `s γ + (s - 1) (1 - log (2π)) - (ζ'/ζ(s) + 1 / (s - 1))`
minus the gamma combination of `TauCeti.mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℝ`.
This is the factorization `ξ(s) = 2π (s - 1) ζ(s) Γℝ(s + 2)` read at `0`, `1` and `s`. -/
theorem logDeriv_zetaEntireCompletion_rieszCombination {s : ℂ} (hs : 1 < s.re) :
    logDeriv zetaEntireCompletion 0 +
        s * (logDeriv zetaEntireCompletion 1 - logDeriv zetaEntireCompletion 0) -
          logDeriv zetaEntireCompletion s =
      s * (Real.eulerMascheroniConstant : ℂ) + (s - 1) * (1 - (Real.log (2 * Real.pi) : ℂ)) -
          (logDeriv riemannZeta s + (s - 1)⁻¹) -
        (logDeriv Gammaℝ (s + 2) - (1 - s) * logDeriv Gammaℝ 2 - s * logDeriv Gammaℝ (1 + 2)) := by
  have hg (z : ℂ) (hz : -2 < z.re) : Gammaℝ (z + 2) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hξ₀ := logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ (s := 0) (by simp)
    (hg 0 (by norm_num))
  have hξ₁ := logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ (s := 1) (by simp)
    (hg 1 (by norm_num))
  have hξ := logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ
    (zetaEntireCompletion_ne_zero_of_one_le_re hs.le) (hg s (by linarith))
  have hL := logDeriv_riemannZeta_add_inv_sub_one (s := s) (by rintro rfl; simp at hs)
    (riemannZeta_ne_zero_of_one_lt_re hs)
  rw [zero_add, logDeriv_LFunctionTrivChar₁_one_zero] at hξ₀
  rw [logDeriv_LFunctionTrivChar₁_one_one] at hξ₁
  linear_combination (1 - s) * hξ₀ + s * hξ₁ - hξ + hL

/-- The Mellin transform of the zero side is the pole-subtracted Riesz expression for zeta. -/
theorem integral_riemannZetaRieszZeroSide_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 1, riemannZetaRieszZeroSide y * (y : ℂ) ^ (-s - 1)) =
      rieszRemainderMellin riemannZeta s := by
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  have hZ := orderLE_zetaEntireCompletion.mul_integral_rieszZeroSeries_mul_cpow
    differentiable_zetaEntireCompletion (by simp) (by simp)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le) hs
  have hG := mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℝ (a := 2) (s := s) (by norm_num)
    (by linarith)
  rw [rieszRemainderMellin_riemannZeta hs, eq_div_iff (mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁)),
    integral_riemannZetaRieszZeroSide_mul_cpow_eq_add hs]
  linear_combination hZ + hG + logDeriv_zetaEntireCompletion_rieszCombination hs +
    (s - 1) * (Real.log (2 * Real.pi) : ℂ) * mul_inv_cancel₀ hs₀

end TauCeti
