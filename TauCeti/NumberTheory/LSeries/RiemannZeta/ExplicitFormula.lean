/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Analysis.Complex.Hadamard.Riesz
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Riesz
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RieszMellin
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The zero side of the first Riesz formula for zeta

The sum over the nontrivial zeros, the correction from the strictly negative even integers,
and the constant `log (2π)` together have the Mellin transform of the first Riesz remainder.
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

/-- The shifted real gamma factor gives the difference between the logarithmic derivatives of
zeta's entire completion and its pole-removed continuation. This applies at `0` and `1` too. -/
theorem logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ {s : ℂ}
    (hξ : zetaEntireCompletion s ≠ 0) (hΓ : Gammaℝ (s + 2) ≠ 0) :
    logDeriv zetaEntireCompletion s = logDeriv (LFunctionTrivChar₁ 1) s +
      logDeriv Gammaℝ (s + 2) := by
  have hc : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfactor := funext LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ
  have hinv : DifferentiableAt ℂ (Gammaℝ⁻¹) (s + 2) := differentiable_Gammaℝ_inv _
  have hg : DifferentiableAt ℂ Gammaℝ (s + 2) := by
    simpa only [inv_inv] using hinv.inv (inv_ne_zero hΓ)
  have hshift : DifferentiableAt ℂ (fun z : ℂ ↦ z + 2) s := by fun_prop
  have hfun := hg.comp s hshift
  have hl : logDeriv (fun z : ℂ ↦ (Gammaℝ (z + 2))⁻¹) s = -logDeriv Gammaℝ (s + 2) := by
    have hz := logDeriv_fun_zpow hfun (-1 : ℤ)
    rw [logDeriv_comp (x := s) (g := fun z : ℂ ↦ z + 2) hg hshift] at hz
    simpa [Function.comp_def, deriv_add_const] using hz
  have hlog : logDeriv (LFunctionTrivChar₁ 1) s =
      logDeriv zetaEntireCompletion s + -logDeriv Gammaℝ (s + 2) := by
    rw [hfactor]
    simp only [div_eq_mul_inv, logDeriv_mul_const _ _ (inv_ne_zero hc)]
    rw [logDeriv_fun_mul (g := fun z : ℂ ↦ (Gammaℝ (z + 2))⁻¹) s hξ (inv_ne_zero hΓ)
      (differentiable_zetaEntireCompletion s) (hfun.inv hΓ), hl]
  linear_combination -hlog

/-- The principal level-one pole removal agrees with Mathlib's entire regularization of zeta. -/
theorem LFunctionTrivChar₁_one_eq_riemannZeta₁ : LFunctionTrivChar₁ 1 = riemannZeta₁ := by
  funext s
  rcases eq_or_ne s 1 with rfl | hs
  · rw [LFunctionTrivChar₁_one_apply_one, riemannZeta₁_one]
  · rw [LFunctionTrivChar₁_one_apply_of_ne_one hs, riemannZeta_eq_inv_sub_mul hs,
      ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

/-- The Mellin transform of the zero side is the pole-subtracted Riesz expression for zeta. -/
theorem integral_riemannZetaRieszZeroSide_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 1, riemannZetaRieszZeroSide y * (y : ℂ) ^ (-s - 1)) =
      rieszRemainderMellin riemannZeta s := by
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  have hg (z : ℂ) (hz : -2 < z.re) : Gammaℝ (z + 2) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have h0 : logDeriv (LFunctionTrivChar₁ 1) 0 = (Real.log (2 * Real.pi) : ℂ) - 1 := by
    rw [← logDeriv_riemannZeta_add_inv_sub_one zero_ne_one (by simp [riemannZeta_zero])]
    simp only [logDeriv_apply, riemannZeta_zero, deriv_riemannZeta_zero,
      ofReal_log (by positivity : 0 ≤ 2 * Real.pi), ofReal_mul, ofReal_ofNat]
    ring
  have h1 : logDeriv (LFunctionTrivChar₁ 1) 1 = (Real.eulerMascheroniConstant : ℂ) := by
    simp only [LFunctionTrivChar₁_one_eq_riemannZeta₁, logDeriv_apply, riemannZeta₁_one,
      deriv_riemannZeta₁_one, div_one]
  have hξ₀ := logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ (s := 0) (by simp)
    (hg 0 (by norm_num))
  have hξ₁ := logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ (s := 1) (by simp)
    (hg 1 (by norm_num))
  have hξ := logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ
    (zetaEntireCompletion_ne_zero_of_one_le_re hs.le) (hg s (by linarith))
  have hσ : ∀ ρ, zetaEntireCompletion ρ = 0 → ρ.re ≤ 1 :=
    fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le
  have hZ := orderLE_zetaEntireCompletion.integrableOn_rieszZeroSeries_mul_cpow
    differentiable_zetaEntireCompletion (by norm_num) hσ hs
  have hG := integrableOn_rieszGammaCorrection_mul_cpow (a := 2) (d := 2) (s := s)
    (by norm_num) (by norm_num) (by linarith)
  have hExp : (-s - 1).re < -1 := by simp; linarith
  rw [rieszRemainderMellin_riemannZeta hs, eq_div_iff (mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁))]
  conv_lhs => rw [mul_comm]
  simp only [riemannZetaRieszZeroSide_def, add_mul]
  rw [integral_add (f := fun y : ℝ ↦ rieszZeroSeries zetaEntireCompletion y * (y : ℂ) ^ (-s - 1) +
      rieszGammaCorrection 2 2 y * (y : ℂ) ^ (-s - 1)) (hZ.add hG)
      ((integrableOn_Ioi_cpow_of_lt hExp zero_lt_one).const_mul _),
    integral_add hZ hG, integral_const_mul, integral_Ioi_cpow_of_lt hExp zero_lt_one,
    mul_add, mul_add,
    orderLE_zetaEntireCompletion.mul_integral_rieszZeroSeries_mul_cpow
      differentiable_zetaEntireCompletion (by simp) (by simp) hσ hs,
    mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℝ (by norm_num) (by linarith),
    hξ₀, hξ₁, hξ, h0, h1,
    ← logDeriv_riemannZeta_add_inv_sub_one hs₁ (riemannZeta_ne_zero_of_one_lt_re hs)]
  simp only [ofReal_one, ofReal_ofNat, zero_add, one_cpow, neg_div, sub_add_cancel]
  field_simp
  ring

end TauCeti
