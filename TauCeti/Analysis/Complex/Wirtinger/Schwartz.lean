/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Planar Wirtinger derivatives on Schwartz space

The planar operators `∂ = (∂ₛ - i ∂ₜ) / 2` and `bar∂ = (∂ₛ + i ∂ₜ) / 2` preserve Schwartz
space and are continuous and complex linear. On the Fourier side they are multiplication by
`πi conj ξ` and `πi ξ`, respectively. Evaluation agrees with the existing Wirtinger derivatives
applied to the direction `1`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (planar Cauchy–Riemann operators).
-/

public noncomputable section

open scoped FourierTransform SchwartzMap LineDeriv Real ContDiff
open FourierTransform Complex ComplexConjugate

namespace SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- The planar conjugate Wirtinger derivative `(∂ₛ + i ∂ₜ) / 2` on Schwartz space. -/
def conjWirtingerDerivCLM : 𝓢(ℂ, F) →L[ℂ] 𝓢(ℂ, F) :=
  (2 : ℂ)⁻¹ • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) (1 : ℂ) +
    I • LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) I)

/-- The conjugate Wirtinger derivative as the sum of the two directional derivatives. -/
theorem conjWirtingerDerivCLM_eq (u : 𝓢(ℂ, F)) :
    conjWirtingerDerivCLM F u = (2 : ℂ)⁻¹ • (∂_{(1 : ℂ)} u + I • ∂_{I} u) := by
  simp only [conjWirtingerDerivCLM, smul_apply, add_apply,
    LineDeriv.lineDerivOpCLM_apply]

/-- Evaluation agrees with `TauCeti.conjWirtingerDeriv` in direction `1`. -/
@[simp]
theorem conjWirtingerDerivCLM_apply (u : 𝓢(ℂ, F)) (z : ℂ) :
    conjWirtingerDerivCLM F u z = TauCeti.conjWirtingerDeriv (u : ℂ → F) z 1 := by
  simp [conjWirtingerDerivCLM_eq, TauCeti.conjWirtingerDeriv_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

variable (F) in
/-- The planar Wirtinger derivative `(∂ₛ - i ∂ₜ) / 2` on Schwartz space. -/
def wirtingerDerivCLM : 𝓢(ℂ, F) →L[ℂ] 𝓢(ℂ, F) :=
  (2 : ℂ)⁻¹ • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) (1 : ℂ) +
    (-I) • LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) I)

/-- The Wirtinger derivative as the difference of the two directional derivatives. -/
theorem wirtingerDerivCLM_eq (u : 𝓢(ℂ, F)) :
    wirtingerDerivCLM F u = (2 : ℂ)⁻¹ • (∂_{(1 : ℂ)} u + (-I) • ∂_{I} u) := by
  simp only [wirtingerDerivCLM, smul_apply, add_apply,
    LineDeriv.lineDerivOpCLM_apply]

/-- Evaluation agrees with `TauCeti.wirtingerDeriv` in direction `1`. -/
@[simp]
theorem wirtingerDerivCLM_apply (u : 𝓢(ℂ, F)) (z : ℂ) :
    wirtingerDerivCLM F u z = TauCeti.wirtingerDeriv (u : ℂ → F) z 1 := by
  simp [wirtingerDerivCLM_eq, TauCeti.wirtingerDeriv_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, sub_eq_add_neg]

/-- On the Fourier side `bar∂` is multiplication by `πi ξ`. -/
theorem fourier_conjWirtingerDerivCLM_apply (u : 𝓢(ℂ, F)) (ξ : ℂ) :
    𝓕 (conjWirtingerDerivCLM F u) ξ = (π * I * ξ) • 𝓕 u ξ := by
  simp only [conjWirtingerDerivCLM_eq, FourierTransform.fourier_smul,
    FourierTransform.fourier_add, smul_apply, add_apply,
    SchwartzMap.fourier_lineDerivOp_apply, smul_smul, ← add_smul]
  congr 1
  conv_rhs => rw [← re_add_im ξ]
  simp only [Complex.inner, conj_re, conj_im, mul_re, one_re, one_im, I_re, I_im]
  push_cast
  ring

/-- On the Fourier side `∂` is multiplication by `πi conj ξ`. -/
theorem fourier_wirtingerDerivCLM_apply (u : 𝓢(ℂ, F)) (ξ : ℂ) :
    𝓕 (wirtingerDerivCLM F u) ξ = (π * I * conj ξ) • 𝓕 u ξ := by
  simp only [wirtingerDerivCLM_eq, FourierTransform.fourier_smul,
    FourierTransform.fourier_add, smul_apply, add_apply,
    SchwartzMap.fourier_lineDerivOp_apply, smul_smul, ← add_smul]
  congr 1
  conv_rhs => rw [← re_add_im ξ]
  simp only [Complex.inner, conj_re, conj_im, mul_re, one_re, one_im, I_re, I_im,
    map_add, map_mul, conj_ofReal, conj_I]
  push_cast
  ring

end SchwartzMap
