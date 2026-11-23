/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Moments

/-!
# The space `H^{1,2}(ℝ)`: the `2π` witness

A computation on Gaussians on the real line tests the identification of Mathlib's
Bessel-potential space `H^{1,2}(ℝ)` with the weak-derivative space `W^{1,2}(ℝ)`.

Mathlib's Bessel potential is the multiplier `(1 + ξ²)^{s/2}`, while the derivative has the symbol
`2πi ξ`, so by the Plancherel identity (`SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`)

`‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖u'‖²_{L²}`.

For the Gaussian `g(x) = exp(-b x²)`, `0 < Re b`, the squared `L²` norms of `g` and `g'` are
`√(π / (2 Re b))` and `√(π / (2 Re b)) |b|² / Re b` (`TauCeti.norm_toLp_gaussian_sq`,
`TauCeti.norm_toLp_lineDerivOp_one_gaussian_sq`), so `‖g‖²_{H^{1,2}}` is
`√(π / (2 Re b)) (1 + |b|² / (4π² Re b))`
(`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`), whereas the sum of the squared `L²`
norms of `g` and `g'` is `√(π / (2 Re b)) (1 + |b|² / Re b)`
(`TauCeti.norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq`). The two norms are
equivalent, with constants `1` and `(2π)²` on the derivative term, but not equal.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, Section 1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv Real

namespace TauCeti

/-- **The `L²` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{L²} = ∫ |exp(-b x²)|² dx = √(π / (2 Re b))`. -/
theorem norm_toLp_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖(SchwartzMap.gaussian (V := ℝ) hb).toLp 2‖ ^ 2 = √(π / (2 * b.re)) := by
  have h (x : ℝ) : ‖SchwartzMap.gaussian (V := ℝ) hb x‖ ^ 2 = Real.exp (-(2 * b.re) * x ^ 2) := by
    rw [SchwartzMap.norm_gaussian_apply, Real.norm_eq_abs, sq_abs, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  simp only [SchwartzMap.norm_toLp_sq, h, integral_gaussian]

/-- **The `L²` norm of the derivative of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`,
`0 < Re b`, `‖g'‖²_{L²} = ∫ |∂ₓ exp(-b x²)|² dx = √(π / (2 Re b)) |b|² / Re b`. -/
theorem norm_toLp_lineDerivOp_one_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      √(π / (2 * b.re)) * (‖b‖ ^ 2 / b.re) := by
  rw [SchwartzMap.norm_toLp_sq]
  have h (x : ℝ) : ‖∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ)) x‖ ^ 2 =
      4 * ‖b‖ ^ 2 * (x ^ 2 * Real.exp (-(2 * b.re) * x ^ 2)) := by
    rw [SchwartzMap.lineDerivOp_gaussian, SchwartzMap.smul_apply,
      SchwartzMap.innerMulGaussian_apply, norm_smul, norm_mul, norm_cexp_neg_mul_sq,
      Complex.norm_real]
    simp only [mul_pow, Real.norm_eq_abs, sq_abs, RCLike.inner_apply, conj_trivial,
      sq (Real.exp _), ← Real.exp_add]
    norm_num
    ring_nf
  simp only [h, integral_const_mul, integral_sq_mul_exp_neg_mul_sq]
  have : 0 < b.re := hb
  field_simp
  ring

/-- **The `H^{1,2}` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{H^{1,2}} = ‖g‖²_{L²} + (2π)⁻² ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / (4π² Re b))`.
Mathlib's Bessel potential has the symbol `(1 + ξ²)^{1/2}`, not `(1 + 4π² ξ²)^{1/2}`. -/
theorem norm_toBesselPotentialSpaceCLM_one_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (1 : ℝ) 2 (SchwartzMap.gaussian (V := ℝ) hb)‖ ^ 2 =
      √(π / (2 * b.re)) * (1 + ‖b‖ ^ 2 / (4 * π ^ 2 * b.re)) := by
  simp only [SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq
      (OrthonormalBasis.singleton (Fin 1) ℝ), OrthonormalBasis.singleton_apply,
    Finset.univ_unique, Finset.sum_singleton, ← SchwartzMap.norm_toLp_sq, norm_toLp_gaussian_sq,
    norm_toLp_lineDerivOp_one_gaussian_sq]
  have : 0 < b.re := hb
  field_simp
  ring

/-- **The `W^{1,2}` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{L²} + ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / Re b)`. Compared with
`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`, the derivative term carries the factor
`(2π)²`. -/
theorem norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq {b : ℂ}
    (hb : 0 < b.re) :
    ‖(SchwartzMap.gaussian (V := ℝ) hb).toLp 2‖ ^ 2 +
        ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      √(π / (2 * b.re)) * (1 + ‖b‖ ^ 2 / b.re) := by
  rw [norm_toLp_gaussian_sq, norm_toLp_lineDerivOp_one_gaussian_sq]
  ring

end TauCeti
