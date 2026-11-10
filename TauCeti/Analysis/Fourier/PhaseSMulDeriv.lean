/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# Derivative of a map multiplied by a Fourier phase

For a continuous linear phase `L : X →L[ℝ] E` into a real inner product space and a frequency
`ζ : E`, this file computes the derivative of `p ↦ 𝐞 ⟪ζ, L p⟫ • g p`: the derivative of `g` plus
the derivative `2πi ⟪ζ, L ·⟫ g p` of the phase, both multiplied by the phase. It also bounds this
derivative in Japanese-bracket weights `⟨2πζ⟩ ^ m = (1 + ‖2πζ‖²) ^ (m / 2)` and proves that it is
continuous in the frequency.

These facts differentiate oscillatory integrals `∫ 𝐞 ⟪ζ, L p⟫ • g(p, ζ) dζ` under the integral sign,
such as the quantization integrand (`L = id`) and the kernel integrand (`L = fst - snd`) of
pseudodifferential operators.

## Main declarations

* `TauCeti.fourierCharSMulFDeriv`: the derivative of `p ↦ 𝐞 ⟪ζ, L p⟫ • g p` at `p`, in terms of
  the value and the derivative of `g` at `p`.
* `TauCeti.hasFDerivAt_fourierChar_inner_smul`: the derivative of `p ↦ 𝐞 ⟪ζ, L p⟫ • g p`.
* `TauCeti.norm_fourierCharSMulFDeriv_le`: the bound `(A + ‖L‖ B) ⟨2πζ⟩ ^ (m + 1)` when
  `‖∂g‖ ≤ A ⟨2πζ⟩ ^ m` and `‖g‖ ≤ B ⟨2πζ⟩ ^ m`.
* `TauCeti.continuous_fourierCharSMulFDeriv`: continuity of the derivative in the frequency.
-/

public section

open scoped FourierTransform RealInnerProductSpace
open Real ContinuousLinearMap

noncomputable section

namespace TauCeti

variable {E X F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The derivative at `p` of `p ↦ 𝐞 ⟪ζ, L p⟫ • g p`, for a continuous linear phase `L` and a map
`g` with value `v` and derivative `D` at `p`: the derivative `D` of `g` plus the derivative
`2πi ⟪ζ, L ·⟫ v` of the phase, both multiplied by the phase. -/
def fourierCharSMulFDeriv (L : X →L[ℝ] E) (ζ : E) (p : X) (v : F) (D : X →L[ℝ] F) :
    X →L[ℝ] F :=
  (𝐞 ⟪ζ, L p⟫ : ℂ) • D +
    (toSpanSingleton ℝ (2 * π * Complex.I * 𝐞 ⟪ζ, L p⟫) ∘L innerSL ℝ ζ ∘L L).smulRight v

@[simp]
theorem fourierCharSMulFDeriv_apply (L : X →L[ℝ] E) (ζ : E) (p : X) (v : F) (D : X →L[ℝ] F)
    (q : X) :
    fourierCharSMulFDeriv L ζ p v D q =
      𝐞 ⟪ζ, L p⟫ • (D q + (2 * π * Complex.I * ⟪ζ, L q⟫ : ℂ) • v) := by
  simp only [fourierCharSMulFDeriv, add_apply, smul_apply, comp_apply, smulRight_apply,
    toSpanSingleton_apply, innerSL_apply_apply, Circle.smul_def, smul_add, smul_smul,
    Complex.real_smul]
  congr 2
  ring

/-- **Derivative of a map multiplied by a Fourier phase.** -/
theorem hasFDerivAt_fourierChar_inner_smul (L : X →L[ℝ] E) (ζ : E) {g : X → F}
    {D : X →L[ℝ] F} {p : X} (hg : HasFDerivAt g D p) :
    HasFDerivAt (fun p ↦ 𝐞 ⟪ζ, L p⟫ • g p) (fourierCharSMulFDeriv L ζ p (g p) D) p := by
  have hc := (Real.hasDerivAt_fourierChar ⟪ζ, L p⟫).hasFDerivAt.comp p
    ((innerSL ℝ ζ ∘L L).hasFDerivAt (x := p))
  simp only [Circle.smul_def]
  exact hc.smul hg

/-- If `‖D‖ ≤ A ⟨2πζ⟩ ^ m` and `‖v‖ ≤ B ⟨2πζ⟩ ^ m`, the derivative of `p ↦ 𝐞 ⟪ζ, L p⟫ • g p` is
bounded by `(A + ‖L‖ B) ⟨2πζ⟩ ^ (m + 1)`: the derivative of the phase costs one power of the
frequency. -/
theorem norm_fourierCharSMulFDeriv_le {L : X →L[ℝ] E} {ζ : E} {p : X} {v : F}
    {D : X →L[ℝ] F} {A B m : ℝ} (hD : ‖D‖ ≤ A * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2))
    (hv : ‖v‖ ≤ B * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2)) :
    ‖fourierCharSMulFDeriv L ζ p v D‖ ≤
      (A + ‖L‖ * B) * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) := by
  set w := 1 + ‖(2 * π) • ζ‖ ^ 2
  have hw : 0 < w ^ (m / 2) := by positivity
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hD) hw
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hv) hw
  have hw₁ : w ^ (m / 2) * ‖(2 * π) • ζ‖ ≤ w ^ ((m + 1) / 2) :=
    one_add_norm_sq_rpow_mul_norm_le _ m
  have hw₂ : w ^ (m / 2) ≤ w ^ ((m + 1) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖(2 * π) • ζ‖]) (by linarith)
  have hζ : 2 * π * ‖ζ‖ = ‖(2 * π) • ζ‖ := by
    rw [norm_smul, Real.norm_of_nonneg two_pi_pos.le]
  refine opNorm_le_bound _ (by positivity) fun q ↦ ?_
  rw [fourierCharSMulFDeriv_apply, Circle.norm_smul]
  refine (norm_add_le _ _).trans ?_
  have h₂ : ‖(2 * π * Complex.I * ⟪ζ, L q⟫ : ℂ) • v‖ ≤
      ‖L‖ * B * (w ^ (m / 2) * ‖(2 * π) • ζ‖) * ‖q‖ := by
    rw [norm_smul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg pi_pos.le, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, ← hζ]
    calc 2 * π * |⟪ζ, L q⟫| * ‖v‖ ≤ 2 * π * (‖ζ‖ * (‖L‖ * ‖q‖)) * (B * w ^ (m / 2)) := by
          gcongr
          exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact le_opNorm _ _)
      _ = ‖L‖ * B * (w ^ (m / 2) * (2 * π * ‖ζ‖)) * ‖q‖ := by ring
  calc _ ≤ A * w ^ (m / 2) * ‖q‖ + ‖L‖ * B * (w ^ (m / 2) * ‖(2 * π) • ζ‖) * ‖q‖ :=
        add_le_add ((le_opNorm _ _).trans (by gcongr)) h₂
    _ ≤ A * w ^ ((m + 1) / 2) * ‖q‖ + ‖L‖ * B * w ^ ((m + 1) / 2) * ‖q‖ := by gcongr
    _ = (A + ‖L‖ * B) * w ^ ((m + 1) / 2) * ‖q‖ := by ring

/-- The derivative of `p ↦ 𝐞 ⟪ζ, L p⟫ • g p` depends continuously on the frequency `ζ` when the
value and the directional derivatives of `g` do. -/
theorem continuous_fourierCharSMulFDeriv [FiniteDimensional ℝ X] (L : X →L[ℝ] E) (p : X)
    {v : E → F} {D : E → X →L[ℝ] F} (hv : Continuous v) (hD : ∀ q, Continuous fun ζ ↦ D ζ q) :
    Continuous fun ζ ↦ fourierCharSMulFDeriv L ζ p (v ζ) (D ζ) := by
  have he : Continuous fun ζ : E ↦ (𝐞 ⟪ζ, L p⟫ : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))
  refine continuous_clm_apply.2 fun q ↦ ?_
  have hDq := hD q
  simp only [fourierCharSMulFDeriv_apply, Circle.smul_def]
  fun_prop

end TauCeti
