/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import TauCeti.Analysis.Contour.Argument.Principle

/-!
# The origin term in the first Riesz explicit formula

The factor `1 / (s * (1 - s))` has a simple pole at zero. Applied to a logarithmic
derivative of the form `m / s + O(1)`, it gives a pole of order at most two whose residue after
multiplication by `y ^ s` is affine in `log y`, with coefficient `m`. This computation handles
an analytic correction to the numerator, including the main-term subtractions used for both
principal and nonprincipal characters. For the Riemann zeta function the origin contributes
`log (2π)`, by `riemannZeta_zero` and Loeffler and Tao's `deriv_riemannZeta_zero`.
-/

public section

open Complex Filter Topology

namespace TauCeti

open Contour

/-- The residue at zero of the first Riesz kernel times `logDeriv f + h` and `y ^ s`.
The normal-form value in the answer is the constant Laurent coefficient of `logDeriv f`.
For a positive real `y`, the logarithm is the ordinary real logarithm, and its coefficient is
exactly the order of `f` at zero. -/
theorem residue_rieszKernel_mul_logDeriv {f h : ℂ → ℂ} {m : ℤ} {y : ℂ}
    (hf : MeromorphicAt f 0) (hm : meromorphicOrderAt f 0 = m)
    (hh : AnalyticAt ℂ h 0) (hy : y ≠ 0) :
    residue (fun s ↦ (logDeriv f s + h s) * y ^ s / (s * (1 - s))) 0 =
      toMeromorphicNFAt (fun s ↦ logDeriv f s - (m : ℂ) / s) 0 0 + h 0 +
        (m : ℂ) * (1 + log y) := by
  obtain ⟨g, hg, hg₀, hsplit⟩ := logDeriv_eventuallyEq_principalPart hf hm
  have hgLog := hg.logDeriv hg₀
  have hreg : (fun s ↦ logDeriv f s - (m : ℂ) / s) =ᶠ[𝓝[≠] 0] logDeriv g := by
    filter_upwards [hsplit] with s hs
    simp only [sub_zero] at hs
    rw [hs, div_eq_mul_inv, add_sub_cancel_left]
  have hvalue : toMeromorphicNFAt (fun s ↦ logDeriv f s - (m : ℂ) / s) 0 0 = logDeriv g 0 := by
    simpa only [toMeromorphicNFAt_eq_self.mpr hgLog.meromorphicNFAt] using
      (toMeromorphicNFAt_eventuallyEq_nhds_congr hreg).eq_of_nhds
  -- Clearing `s²` leaves an analytic numerator whose first derivative gives the residue.
  let G (s : ℂ) := ((m : ℂ) + s * (logDeriv g s + h s)) * y ^ s / (1 - s)
  have han : AnalyticAt ℂ G 0 := by
    have hpow : AnalyticAt ℂ (fun s : ℂ ↦ y ^ s) 0 :=
      (Differentiable.analyticAt (fun s ↦ differentiableAt_id.const_cpow (.inl hy)) 0)
    exact ((analyticAt_const.add (analyticAt_id.mul (hgLog.add hh))).mul hpow).div
      (analyticAt_const.sub analyticAt_id) (by simp)
  have hG : HasDerivAt G (logDeriv g 0 + h 0 + (m : ℂ) * (1 + log y)) 0 := by
    have hp := (hasDerivAt_id (0 : ℂ)).const_cpow (c := y) (.inl hy)
    have hregDeriv := (hgLog.add hh).differentiableAt.hasDerivAt
    have hnum := ((hasDerivAt_id (0 : ℂ)).mul hregDeriv).const_add (m : ℂ)
    have hden := (hasDerivAt_id (0 : ℂ)).const_sub (1 : ℂ)
    convert (hnum.mul hp).div hden (by simp) using 1
    · rfl
    · simp only [id_eq, Pi.add_apply, Pi.mul_apply, zero_mul, add_zero, one_mul, cpow_zero,
        sub_zero, mul_one, one_pow, div_one]
      ring
  have hquot : (fun s ↦ (logDeriv f s + h s) * y ^ s / (s * (1 - s))) =ᶠ[𝓝[≠] 0]
      fun s ↦ G s / (s - 0) ^ (1 + 1 : ℕ) := by
    filter_upwards [hsplit, self_mem_nhdsWithin] with s hs (hs₀ : s ≠ 0)
    simp only [sub_zero] at hs ⊢
    rw [hs]
    by_cases hs₁ : s = 1
    · simp [hs₁, G]
    · dsimp only [G]
      field_simp [sub_ne_zero.mpr (Ne.symm hs₁)]
      ring
  rw [residue_congr_nhdsNE hquot, residue_div_sub_pow_of_analyticAt han 1, hvalue]
  simpa using hG.deriv

/-- In the Riemann zeta case the origin term in the Riesz explicit formula is `log (2π)`.
The coefficient `c` of the linear subtraction (in the remainder transform it is `1 + γ`)
does not affect the origin residue. -/
theorem residue_rieszKernel_riemannZeta {y : ℂ} (hy : y ≠ 0) (c : ℂ) :
    residue (fun s ↦ (logDeriv riemannZeta s + ((s - 1)⁻¹ + 1 - c * s)) * y ^ s /
      (s * (1 - s))) 0 = (Real.log (2 * Real.pi) : ℂ) := by
  have hz := analyticOn_riemannZeta 0 (zero_ne_one : (0 : ℂ) ≠ 1)
  have hz₀ : riemannZeta 0 ≠ 0 := by norm_num [riemannZeta_zero]
  have hm : meromorphicOrderAt riemannZeta 0 = (0 : ℤ) :=
    hz.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hz₀
  have hh : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1)⁻¹ + 1 - c * s) 0 := by
    have hsub : AnalyticAt ℂ (fun s : ℂ ↦ s - 1) 0 := analyticAt_id.sub analyticAt_const
    have hinv := hsub.inv (by simp)
    exact (hinv.add analyticAt_const).sub (analyticAt_const.mul analyticAt_id)
  rw [residue_rieszKernel_mul_logDeriv hz.meromorphicAt hm hh hy]
  simp only [Int.cast_zero, zero_div, sub_zero, zero_mul, add_zero,
    toMeromorphicNFAt_eq_self.mpr (hz.logDeriv hz₀).meromorphicNFAt]
  simp only [logDeriv, Pi.div_apply, riemannZeta_zero, deriv_riemannZeta_zero,
    ofReal_log (by positivity : 0 ≤ 2 * Real.pi), ofReal_mul, ofReal_ofNat]
  ring

end TauCeti
