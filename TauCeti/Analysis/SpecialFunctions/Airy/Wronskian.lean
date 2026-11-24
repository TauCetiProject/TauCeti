/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Equation
import TauCeti.Analysis.Calculus.Deriv.Second
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Airy functions: rotated solutions and their Wronskians

For a cube root of unity `ν`, the functions `z ↦ Ai(νz)` and `z ↦ Bi(νz)` solve Airy's equation
(DLMF 9.2.2). Their Wronskians with one another are constants, which DLMF 9.2.8–9.2.9 evaluate for
`ν = ω^{±1}`, where `ω = e^{2πi/3}`.

## Main results

* `TauCeti.airy_ode_comp_mul_left`: if `w″ = z w` and `ν³ = 1`, then `z ↦ w(νz)` solves the same
  equation;
* `TauCeti.airyAi_ode_comp_mul_left`, `TauCeti.airyBi_ode_comp_mul_left`: `z ↦ Ai(νz)` and
  `z ↦ Bi(νz)` solve Airy's equation (DLMF 9.2.2);
* `TauCeti.airyAi_zero_mul_deriv_airyAi_zero`: `Ai(0) Ai′(0) = −1/(2π√3)`;
* `TauCeti.wronskian_airyAi_comp_mul_left`: for cube roots of unity `μ` and `ν`,
  `𝒲{Ai(μz), Ai(νz)} = (μ − ν)/(2π√3)`;
* `TauCeti.wronskian_airyAi_mul_exp_neg_two_pi_mul_I_div_three`,
  `TauCeti.wronskian_airyAi_mul_exp_two_pi_mul_I_div_three`:
  `𝒲{Ai(z), Ai(z ω^{∓1})} = e^{±πi/6}/(2π)` (DLMF 9.2.8);
* `TauCeti.wronskian_airyAi_rotations`: `𝒲{Ai(z ω^{−1}), Ai(z ω)} = 1/(2πi)` (DLMF 9.2.9).

## Implementation notes

The Wronskian of two entire solutions of Airy's equation is constant
(`TauCeti.wronskian_eq_of_airy_ode`), so each Wronskian is its value at `0`. There it is a multiple
of `Ai(0) Ai′(0)`, which `𝒲{Ai, Bi} = 1/π` (DLMF 9.2.7) evaluates, since `Bi(0) = √3 Ai(0)` and
`Bi′(0) = −√3 Ai′(0)`.

## References

* NIST Digital Library of Mathematical Functions, §9.2(iii), <https://dlmf.nist.gov/9.2.iii>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Basic/Connections.lean`.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

/-- **Rotation symmetry** of Airy's equation: if `w″ = z w` and `ν³ = 1`, then `z ↦ w(νz)` solves
the same equation. No differentiability of `w` is needed. -/
theorem airy_ode_comp_mul_left {w : ℂ → ℂ} {ν : ℂ} (hw : ∀ z, deriv^[2] w z = z * w z)
    (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun u => w (ν * u)) z = z * w (ν * z) := by
  have h2 (f : ℂ → ℂ) (x : ℂ) : deriv^[2] f x = deriv (deriv f) x := rfl
  rw [h2, deriv_deriv_comp_mul_left, smul_eq_mul, ← h2, hw]
  linear_combination z * w (ν * z) * hν

/-- For a cube root of unity `ν`, `z ↦ Ai(νz)` solves Airy's equation (DLMF 9.2.2). -/
theorem airyAi_ode_comp_mul_left {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun u => airyAi (ν * u)) z = z * airyAi (ν * z) :=
  airy_ode_comp_mul_left airyAi_ode hν z

/-- For a cube root of unity `ν`, `z ↦ Bi(νz)` solves Airy's equation (DLMF 9.2.2). -/
theorem airyBi_ode_comp_mul_left {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun u => airyBi (ν * u)) z = z * airyBi (ν * z) :=
  airy_ode_comp_mul_left airyBi_ode hν z

/-- `(3 : ℂ)^{1/2} = √3`. -/
private theorem three_cpow_one_div_two : (3 : ℂ) ^ (1 / 2 : ℂ) = (√3 : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- `Ai(0) Ai′(0) = −1/(2π√3)`. -/
theorem airyAi_zero_mul_deriv_airyAi_zero :
    airyAi 0 * deriv airyAi 0 = -(2 * π * √3 : ℂ)⁻¹ := by
  have hW := wronskian_airyAi_airyBi 0
  rw [airyBi_zero_eq_cpow_mul_airyAi_zero, deriv_airyBi_zero_eq_neg_cpow_mul_deriv_airyAi_zero,
    three_cpow_one_div_two] at hW
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (√3 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  field_simp at hW ⊢
  linear_combination -hW

/-- For cube roots of unity `μ` and `ν`, `𝒲{Ai(μz), Ai(νz)} = (μ − ν)/(2π√3)`. -/
theorem wronskian_airyAi_comp_mul_left {μ ν : ℂ} (hμ : μ ^ 3 = 1) (hν : ν ^ 3 = 1) (z : ℂ) :
    airyAi (μ * z) * deriv (fun u => airyAi (ν * u)) z -
        deriv (fun u => airyAi (μ * u)) z * airyAi (ν * z) =
      (μ - ν) / (2 * π * √3) := by
  have hd {c : ℂ} : Differentiable ℂ fun u => airyAi (c * u) :=
    differentiable_airyAi.comp (differentiable_id.const_mul c)
  have h := wronskian_eq_of_airy_ode hd hd (airyAi_ode_comp_mul_left hμ)
    (airyAi_ode_comp_mul_left hν) z 0
  simp only [deriv_comp_mul_left, smul_eq_mul, mul_zero] at h ⊢
  rw [h, div_eq_mul_inv, ← neg_neg (2 * π * √3 : ℂ)⁻¹, ← airyAi_zero_mul_deriv_airyAi_zero]
  ring

/-- `ω = e^{2πi/3} = −1/2 + (√3/2) i`. -/
private theorem exp_two_pi_mul_I_div_three : cexp (2 * π * I / 3) = -1 / 2 + √3 / 2 * I := by
  rw [show 2 * π * I / 3 = ((π - π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- `ω^{−1} = e^{−2πi/3} = −1/2 − (√3/2) i`. -/
private theorem exp_neg_two_pi_mul_I_div_three :
    cexp (-(2 * π * I / 3)) = -1 / 2 - √3 / 2 * I := by
  rw [show -(2 * π * I / 3) = ((-(π - π / 3) : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

/-- `e^{πi/6} = √3/2 + i/2`. -/
private theorem exp_pi_mul_I_div_six : cexp (π * I / 6) = √3 / 2 + 1 / 2 * I := by
  rw [show π * I / 6 = ((π / 6 : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- `e^{−πi/6} = √3/2 − i/2`. -/
private theorem exp_neg_pi_mul_I_div_six : cexp (-(π * I / 6)) = √3 / 2 - 1 / 2 * I := by
  rw [show -(π * I / 6) = ((-(π / 6) : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- `(√3 : ℂ)² = 3`. -/
private theorem ofReal_sqrt_three_sq : (√3 : ℂ) ^ 2 = 3 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `𝒲{Ai(z), Ai(zν)} = (1 − ν)/(2π√3)` for a cube root of unity `ν`. -/
private theorem wronskian_airyAi_mul {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    airyAi z * deriv (fun u => airyAi (u * ν)) z - deriv airyAi z * airyAi (z * ν) =
      (1 - ν) / (2 * π * √3) := by
  simp_rw [mul_comm _ ν]
  simpa only [one_mul] using wronskian_airyAi_comp_mul_left (one_pow 3) hν z

/-- `𝒲{Ai(z), Ai(z e^{−2πi/3})} = e^{πi/6}/(2π)` (DLMF 9.2.8, upper signs). -/
theorem wronskian_airyAi_mul_exp_neg_two_pi_mul_I_div_three (z : ℂ) :
    airyAi z * deriv (fun u => airyAi (u * cexp (-(2 * π * I / 3)))) z -
        deriv airyAi z * airyAi (z * cexp (-(2 * π * I / 3))) =
      cexp (π * I / 6) / (2 * π) := by
  have hω : cexp (2 * π * I / 3) ^ 3 = 1 := by
    exact_mod_cast (isPrimitiveRoot_exp 3 (by norm_num)).pow_eq_one
  rw [wronskian_airyAi_mul (by rw [exp_neg, inv_pow, hω, inv_one]),
    exp_neg_two_pi_mul_I_div_three, exp_pi_mul_I_div_six]
  have hs : (√3 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination -ofReal_sqrt_three_sq

/-- `𝒲{Ai(z), Ai(z e^{2πi/3})} = e^{−πi/6}/(2π)` (DLMF 9.2.8, lower signs). -/
theorem wronskian_airyAi_mul_exp_two_pi_mul_I_div_three (z : ℂ) :
    airyAi z * deriv (fun u => airyAi (u * cexp (2 * π * I / 3))) z -
        deriv airyAi z * airyAi (z * cexp (2 * π * I / 3)) =
      cexp (-(π * I / 6)) / (2 * π) := by
  have hω : cexp (2 * π * I / 3) ^ 3 = 1 := by
    exact_mod_cast (isPrimitiveRoot_exp 3 (by norm_num)).pow_eq_one
  rw [wronskian_airyAi_mul hω, exp_two_pi_mul_I_div_three,
    exp_neg_pi_mul_I_div_six]
  have hs : (√3 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination -ofReal_sqrt_three_sq

/-- `𝒲{Ai(z e^{−2πi/3}), Ai(z e^{2πi/3})} = 1/(2πi)` (DLMF 9.2.9). -/
theorem wronskian_airyAi_rotations (z : ℂ) :
    airyAi (z * cexp (-(2 * π * I / 3))) * deriv (fun u => airyAi (u * cexp (2 * π * I / 3))) z -
        deriv (fun u => airyAi (u * cexp (-(2 * π * I / 3)))) z *
          airyAi (z * cexp (2 * π * I / 3)) =
      1 / (2 * π * I) := by
  have hω : cexp (2 * π * I / 3) ^ 3 = 1 := by
    exact_mod_cast (isPrimitiveRoot_exp 3 (by norm_num)).pow_eq_one
  simp_rw [mul_comm _ (cexp _)]
  rw [wronskian_airyAi_comp_mul_left (by rw [exp_neg, inv_pow, hω, inv_one]) hω z,
    exp_neg_two_pi_mul_I_div_three, exp_two_pi_mul_I_div_three]
  have hs : (√3 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination (-2 * √3) * I_sq

end TauCeti
