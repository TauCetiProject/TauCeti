/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The phase of `Γ` on the line `Re s = ½`

This file defines the continuous phase `φ₂(a) = ph Γ(½ + ia)` with `φ₂(0) = 0` (DLMF 12.14.7),

$$
\varphi_2(a) = \int_0^a \operatorname{Re} \psi\bigl(\tfrac12 + it\bigr)\, dt,
$$

and proves `Γ(½ + ia) = |Γ(½ + ia)| e^{iφ₂(a)}`.

## Main declarations

* `TauCeti.Real.gammaHalfPhase`: the phase `φ₂`, with defining equation
  `TauCeti.Real.gammaHalfPhase_def`.
* `TauCeti.Gamma_one_half_add_mul_I`: `Γ(½ + ia) = |Γ(½ + ia)| e^{iφ₂(a)}`.
* `TauCeti.Real.hasDerivAt_gammaHalfPhase`: `φ₂′(a) = Re ψ(½ + ia)`.
* `TauCeti.Real.gammaHalfPhase_zero`, `TauCeti.Real.gammaHalfPhase_neg`,
  `TauCeti.Real.deriv_gammaHalfPhase_zero`: `φ₂(0) = 0`, `φ₂` is odd, and
  `φ₂′(0) = ψ(½) = −γ − 2 log 2`.

## Implementation notes

With `Φ(a) = ∫₀ᵃ Im ψ(½ + it) dt`, the function `Γ(½ + ia) e^{−iφ₂(a)} e^{Φ(a)}` has derivative
zero, because `d/da Γ(½ + ia) = i ψ(½ + ia) Γ(½ + ia)`. Its value at `a = 0` is `Γ(½) = √π`,
so `Γ(½ + ia) = √π e^{−Φ(a)} e^{iφ₂(a)}`, and the modulus is `√π e^{−Φ(a)}`.
The oddness of `φ₂` uses `Complex.digamma_conj` (in `TauCeti.Analysis.SpecialFunctions.Gamma.Real`).

The phase identity is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/ParabolicCylinder/Weber/Solutions.lean`.
-/

public section

noncomputable section

open Complex

open scoped ComplexConjugate Real

namespace TauCeti

/-- `ψ` is continuous on the line `Re s = ½`. -/
private theorem continuous_digamma_one_half_add_mul_I :
    Continuous fun t : ℝ => digamma (1 / 2 + t * I) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hG : DifferentiableOn ℂ Gamma {s : ℂ | 0 < s.re} := fun s hs =>
    (hasDerivAt_Gamma_of_re_pos hs).differentiableAt.differentiableWithinAt
  have hdG : ContinuousOn (deriv Gamma) {s : ℂ | 0 < s.re} := (hG.deriv hU).continuousOn
  have hψ : ContinuousOn digamma {s : ℂ | 0 < s.re} := by
    have : ContinuousOn (fun s => deriv Gamma s / Gamma s) {s : ℂ | 0 < s.re} :=
      hdG.div hG.continuousOn (fun s hs => Gamma_ne_zero_of_re_pos hs)
    exact this.congr fun s _ => by rw [digamma_def, logDeriv_apply]
  exact hψ.comp_continuous (by fun_prop) fun t => by simp

namespace Real

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

/-- `Re ψ(½ + it)` is even in `t`. -/
private theorem re_digamma_one_half_add_neg_mul_I (t : ℝ) :
    (Complex.digamma (1 / 2 + ((-t : ℝ) : ℂ) * I)).re =
      (Complex.digamma (1 / 2 + t * I)).re := by
  have h : (1 / 2 + ((-t : ℝ) : ℂ) * I) = conj (1 / 2 + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [h, Complex.digamma_conj, conj_re]

/-- `φ₂` is odd: `φ₂(−a) = −φ₂(a)`. -/
@[simp]
theorem gammaHalfPhase_neg (a : ℝ) : gammaHalfPhase (-a) = -gammaHalfPhase a := by
  have h := intervalIntegral.integral_comp_neg
    (fun t : ℝ => (Complex.digamma (1 / 2 + t * I)).re) (a := 0) (b := a)
  simp only [neg_zero] at h
  rw [gammaHalfPhase_def, gammaHalfPhase_def, intervalIntegral.integral_symm (-a) 0, ← h]
  simp only [re_digamma_one_half_add_neg_mul_I]

/-- `φ₂′(0) = ψ(½) = −γ − 2 log 2`. -/
theorem deriv_gammaHalfPhase_zero :
    deriv gammaHalfPhase 0 = -Real.eulerMascheroniConstant - 2 * Real.log 2 := by
  rw [(hasDerivAt_gammaHalfPhase 0).deriv]
  simp only [ofReal_zero, zero_mul, add_zero]
  rw [Complex.digamma_one_half]
  simp [log_re]
  ring

end Real

/-- With `Φ(x) = ∫₀ˣ Im ψ(½ + it) dt`, the function `Γ(½ + ix) e^{−iφ₂(x)} e^{Φ(x)}` has
derivative zero, because `d/dx Γ(½ + ix) = i ψ(½ + ix) Γ(½ + ix)`. -/
private theorem hasDerivAt_Gamma_one_half_add_mul_I_mul_exp (x : ℝ) :
    HasDerivAt (fun x : ℝ => Gamma (1 / 2 + x * I) * exp (-(Real.gammaHalfPhase x * I)) *
      exp ((∫ t : ℝ in 0..x, (digamma (1 / 2 + t * I)).im : ℝ) : ℂ)) 0 x := by
  set Th : ℝ → ℝ := fun a => ∫ t : ℝ in 0..a, (digamma (1 / 2 + t * I)).im
  have hre : 0 < (1 / 2 + (x : ℂ) * I).re := by simp
  have h1 : HasDerivAt (fun x : ℝ => Gamma (1 / 2 + x * I))
      (deriv Gamma (1 / 2 + x * I) * I) x := by
    have hd := (hasDerivAt_Gamma_of_re_pos hre).differentiableAt.hasDerivAt
    have hl : HasDerivAt (fun x : ℝ => (1 / 2 : ℂ) + x * I) I x := by
      simpa using (((hasDerivAt_id (x : ℂ)).mul_const I).const_add (1 / 2 : ℂ)).comp_ofReal
    exact hd.comp x hl
  have h2 : HasDerivAt (fun x : ℝ => exp (-(Real.gammaHalfPhase x * I)))
      (exp (-(Real.gammaHalfPhase x * I)) * (-((digamma (1 / 2 + x * I)).re * I))) x := by
    have := (((Real.hasDerivAt_gammaHalfPhase x).ofReal_comp.mul_const I).neg).cexp
    simpa using this
  have h3 : HasDerivAt (fun x : ℝ => exp ((Th x : ℂ)))
      (exp (Th x) * (digamma (1 / 2 + x * I)).im) x := by
    have hThd : HasDerivAt Th (digamma (1 / 2 + x * I)).im x :=
      ((continuous_im.comp continuous_digamma_one_half_add_mul_I).integral_hasStrictDerivAt
        0 x).hasDerivAt
    simpa using hThd.ofReal_comp.cexp
  refine ((h1.mul h2).mul h3).congr_deriv ?_
  have hG0 : Gamma (1 / 2 + x * I) ≠ 0 := Gamma_ne_zero_of_re_pos hre
  have hψ : deriv Gamma (1 / 2 + x * I) = Gamma (1 / 2 + x * I) *
      (((digamma (1 / 2 + x * I)).re : ℂ) + ((digamma (1 / 2 + x * I)).im : ℂ) * I) := by
    rw [re_add_im, digamma_def, logDeriv_apply, mul_div_assoc', eq_div_iff hG0]
    ring
  simp only [Pi.mul_apply]
  rw [hψ]
  ring_nf
  rw [I_sq]
  ring

/-- **The phase identity** (DLMF 12.14.7): `Γ(½ + ia) = |Γ(½ + ia)| e^{iφ₂(a)}`. -/
theorem Gamma_one_half_add_mul_I (a : ℝ) :
    Gamma (1 / 2 + a * I) =
      ‖Gamma (1 / 2 + a * I)‖ * exp (Real.gammaHalfPhase a * I) := by
  set Ph : ℝ → ℝ := Real.gammaHalfPhase with hPh
  set Th : ℝ → ℝ := fun a => ∫ t : ℝ in 0..a, (digamma (1 / 2 + t * I)).im with hTh
  set h : ℝ → ℂ := fun x => Gamma (1 / 2 + x * I) * exp (-(Ph x * I)) * exp (Th x) with hh
  have hhd (x : ℝ) : HasDerivAt h 0 x := hasDerivAt_Gamma_one_half_add_mul_I_mul_exp x
  have hdiff : Differentiable ℝ h := fun x => (hhd x).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun x => (hhd x).deriv) a 0
  have h0 : h 0 = Real.sqrt π := by
    -- Write `1 / 2` as a real coercion, to apply `Gamma_ofReal` and the real value `Γ(½) = √π`.
    have h12 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
    have hg : Gamma (1 / 2) = (Real.sqrt π : ℂ) := by
      rw [← h12, Gamma_ofReal, Real.Gamma_one_half_eq]
    simp only [hh, hPh, hTh, Real.gammaHalfPhase_zero, intervalIntegral.integral_same,
      ofReal_zero, zero_mul, add_zero, neg_zero, exp_zero, mul_one, hg]
  rw [h0] at hconst
  simp only [hh] at hconst
  have e1 : exp (Ph a * I) * exp (-(Ph a * I)) = 1 := by rw [← Complex.exp_add]; simp
  have e2 : exp (-((Th a : ℝ) : ℂ)) * exp ((Th a : ℝ) : ℂ) = 1 := by
    rw [← Complex.exp_add]; simp
  have hE : Gamma (1 / 2 + a * I) =
      (Real.sqrt π : ℂ) * exp (-((Th a : ℝ) : ℂ)) * exp (Ph a * I) := by
    linear_combination (exp (Ph a * I) * exp (-((Th a : ℝ) : ℂ))) * hconst +
      (-(Gamma (1 / 2 + a * I)) * (exp (-((Th a : ℝ) : ℂ)) * exp ((Th a : ℝ) : ℂ))) * e1 +
      (-(Gamma (1 / 2 + a * I))) * e2
  have hn : ‖Gamma (1 / 2 + a * I)‖ = Real.sqrt π * Real.exp (-Th a) := by
    rw [hE, norm_mul, norm_mul, norm_exp, norm_exp, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    simp
  rw [hn]
  conv_lhs => rw [hE]
  push_cast
  ring

end TauCeti
