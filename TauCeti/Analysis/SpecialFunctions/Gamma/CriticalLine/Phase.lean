/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
import TauCeti.Analysis.SpecialFunctions.Gamma.Conjugation
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The phase of `Γ` on the line `Re s = ½`

This file defines the continuous phase `φ₂(a) = ph Γ(½ + ia)` with `φ₂(0) = 0` (DLMF 12.14.7),

$$
\varphi_2(a) = \int_0^a \operatorname{Re} \psi\bigl(\tfrac12 + it\bigr)\, dt,
$$

and proves `Γ(½ + ia) = |Γ(½ + ia)| e^{iφ₂(a)}`. Together with the modulus
`Complex.norm_Gamma_sq_of_re_eq_one_half` (`|Γ(½ + ia)|² = π / cosh(πa)`), this gives the polar
form of `Γ` on the line `Re s = ½`.

## Main declarations

* `Real.gammaHalfPhase`: the phase `φ₂`, with defining equation `Real.gammaHalfPhase_def`.
* `Real.gammaHalfPhase_eq_im_logGamma`: `φ₂(a) = Im log Γ(½ + ia)`, for the normalized
  logarithm `TauCeti.logGamma`.
* `Real.Gamma_one_half_add_mul_I`: `Γ(½ + ia) = |Γ(½ + ia)| e^{iφ₂(a)}`.
* `Real.hasDerivAt_gammaHalfPhase`: `φ₂′(a) = Re ψ(½ + ia)`.
* `Real.gammaHalfPhase_zero`, `Real.gammaHalfPhase_neg`, `Real.deriv_gammaHalfPhase_zero`:
  `φ₂(0) = 0`, `φ₂` is odd, and `φ₂′(0) = ψ(½) = −γ − 2 log 2`.

## Implementation notes

Since `d/da log Γ(½ + ia) = i ψ(½ + ia)`, the fundamental theorem of calculus identifies `φ₂(a)`
with `Im log Γ(½ + ia)`, where `log Γ` is the normalized logarithm `TauCeti.logGamma`, real on
the positive axis. Exponentiating `log Γ = Re log Γ + i Im log Γ` gives the phase identity.
The oddness of `φ₂` uses `Complex.digamma_conj`
(in `TauCeti.Analysis.SpecialFunctions.Gamma.Conjugation`).

The real-argument declarations live in the root `Real` namespace.

The phase identity is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/ParabolicCylinder/Weber/Solutions.lean`.
-/

public section

noncomputable section

open Complex TauCeti

open scoped ComplexConjugate Real

namespace Real

/-- The line `Re s = ½` lies in the slit plane. -/
private theorem one_half_add_mul_I_mem_slitPlane (a : ℝ) : (1 / 2 + a * I : ℂ) ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by simp))

/-- `ψ` is continuous on the line `Re s = ½`. -/
private theorem continuous_digamma_one_half_add_mul_I :
    Continuous fun t : ℝ => Complex.digamma (1 / 2 + t * I) :=
  analyticOnNhd_digamma_re_pos.continuousOn.comp_continuous (by fun_prop) fun t => by simp

/-- The continuous phase `φ₂(a) = ph Γ(½ + ia)` with `φ₂(0) = 0` (DLMF 12.14.7),
`φ₂(a) = ∫₀ᵃ Re ψ(½ + it) dt`. -/
def gammaHalfPhase (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..a, (Complex.digamma (1 / 2 + t * I)).re

/-- The defining equation of `φ₂`: `φ₂(a) = ∫₀ᵃ Re ψ(½ + it) dt`. -/
theorem gammaHalfPhase_def (a : ℝ) :
    gammaHalfPhase a = ∫ t in (0 : ℝ)..a, (Complex.digamma (1 / 2 + t * I)).re :=
  (rfl)

/-- `φ₂′(a) = Re ψ(½ + ia)`. -/
theorem hasDerivAt_gammaHalfPhase (a : ℝ) :
    HasDerivAt gammaHalfPhase (Complex.digamma (1 / 2 + a * I)).re a := by
  rw [funext gammaHalfPhase_def]
  exact ((continuous_re.comp continuous_digamma_one_half_add_mul_I).integral_hasStrictDerivAt
    0 a).hasDerivAt

/-- `φ₂(0) = 0`. -/
@[simp]
theorem gammaHalfPhase_zero : gammaHalfPhase 0 = 0 := by
  simp [gammaHalfPhase_def]

/-- `φ₂` is odd: `φ₂(−a) = −φ₂(a)`. -/
@[simp]
theorem gammaHalfPhase_neg (a : ℝ) : gammaHalfPhase (-a) = -gammaHalfPhase a := by
  have h := intervalIntegral.integral_comp_neg
    (fun t : ℝ => (Complex.digamma (1 / 2 + t * I)).re) (a := 0) (b := a)
  simp only [neg_zero] at h
  rw [gammaHalfPhase_def, gammaHalfPhase_def, intervalIntegral.integral_symm (-a) 0, ← h]
  -- `½ − it` is the conjugate of `½ + it`, and `Re ψ` is invariant under conjugation.
  have hc (t : ℝ) : (1 / 2 + ((-t : ℝ) : ℂ) * I) = conj (1 / 2 + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  simp only [hc, digamma_conj, conj_re]

/-- `φ₂′(0) = ψ(½) = −γ − 2 log 2`. -/
theorem deriv_gammaHalfPhase_zero :
    deriv gammaHalfPhase 0 = -eulerMascheroniConstant - 2 * log 2 := by
  rw [(hasDerivAt_gammaHalfPhase 0).deriv]
  simp only [ofReal_zero, zero_mul, add_zero]
  -- Mathlib's value `ψ(½) = −2 log 2 − γ`, whose real part is computed by `log_re`.
  have h : (Complex.digamma (1 / 2)).re = -2 * log 2 - eulerMascheroniConstant := by
    rw [Complex.digamma_one_half]
    norm_num [log_re]
  rw [h]
  ring

/-- `φ₂(a) = Im log Γ(½ + ia)`, for the normalized logarithm `TauCeti.logGamma` of `Γ`. -/
theorem gammaHalfPhase_eq_im_logGamma (a : ℝ) :
    gammaHalfPhase a = (logGamma (1 / 2 + a * I)).im := by
  rw [gammaHalfPhase_def]
  have h := integral_re_digamma_ofReal_add_mul_I (σ := 1 / 2) (by norm_num) a
  push_cast at h
  exact h

/-- **The phase identity** (DLMF 12.14.7): `Γ(½ + ia) = |Γ(½ + ia)| e^{iφ₂(a)}`. -/
theorem Gamma_one_half_add_mul_I (a : ℝ) :
    Complex.Gamma (1 / 2 + a * I) =
      ‖Complex.Gamma (1 / 2 + a * I)‖ * Complex.exp (gammaHalfPhase a * I) := by
  rw [gammaHalfPhase_eq_im_logGamma, ← exp_logGamma (one_half_add_mul_I_mem_slitPlane a),
    norm_exp]
  conv_lhs => rw [← re_add_im (logGamma _), Complex.exp_add, ← ofReal_exp]

end Real
