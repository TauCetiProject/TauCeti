/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Airy functions: connection formulas

The connection formulas of DLMF 9.2.10–9.2.15 express `Bi`, and `Ai` and `Bi` at `−z`, through
`Ai` at the rotated arguments `z ω^{±1}` and `z e^{±πi/3}`, where `ω = e^{2πi/3}`.

## Main results

* `TauCeti.airyAi_mul_of_pow_three_eq_one`, `TauCeti.airyBi_mul_of_pow_three_eq_one`: for a cube
  root of unity `ν`, `Ai(νz)` and `Bi(νz)` as combinations of `Ai(z)` and `Bi(z)`;
* `TauCeti.airyBi_eq_airyAi_rotations`: `Bi(z) = e^{−πi/6} Ai(z ω^{−1}) + e^{πi/6} Ai(z ω)`
  (DLMF 9.2.10);
* `TauCeti.airyAi_mul_exp_neg_two_pi_mul_I_div_three`,
  `TauCeti.airyAi_mul_exp_two_pi_mul_I_div_three`:
  `Ai(z ω^{∓1}) = ½ e^{∓πi/3} (Ai(z) ± i Bi(z))` (DLMF 9.2.11);
* `TauCeti.airyAi_add_rotations_eq_zero`, `TauCeti.airyBi_add_rotations_eq_zero`:
  `Ai(z) + ω^{−1} Ai(z ω^{−1}) + ω Ai(z ω) = 0` and the same for `Bi` (DLMF 9.2.12–9.2.13);
* `TauCeti.airyAi_neg_eq_airyAi_rotations`, `TauCeti.airyBi_neg_eq_airyAi_rotations`: `Ai(−z)`
  and `Bi(−z)` through `Ai(z e^{±πi/3})` (DLMF 9.2.14–9.2.15).

## Implementation notes

The proofs use the series definitions directly rather than the uniqueness theorem for Airy's
equation. Both `Ai` and `Bi` are combinations of an even part `P(z) = 3^{−2/3} 𝐅(⅔, z³/9)`, which
is invariant under `z ↦ νz` for `ν³ = 1`, and an odd part `Q(z) = 3^{−4/3} z 𝐅(4/3, z³/9)`, which
picks up the factor `ν`; since `Ai = P − Q` and `Bi = √3 (P + Q)`, this gives
`TauCeti.airyAi_mul_of_pow_three_eq_one` and `TauCeti.airyBi_mul_of_pow_three_eq_one`. The
formulas 9.2.10–9.2.13 follow from these and the explicit values of the exponentials, and
9.2.14–9.2.15 are 9.2.12 and 9.2.10 at `−z`, since `−ω^{∓1} = e^{±πi/3}`.

## References

* NIST Digital Library of Mathematical Functions, §9.2(iv), <https://dlmf.nist.gov/9.2.iv>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Airy/Basic/Properties.lean` and `DLMF/Airy/Basic/Connections.lean`.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

/-- `3^{−1/6} = √3 · 3^{−2/3}`, the ratio of the even parts of `Bi` and `Ai`. -/
private theorem three_cpow_neg_one_div_six :
    (3 : ℂ) ^ (-1 / 6 : ℂ) = (√3 : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num)]
  push_cast
  rw [← cpow_add _ _ (by norm_num)]
  norm_num

/-- `3^{−5/6} = √3 · 3^{−4/3}`, the ratio of the odd parts of `Bi` and `Ai`. -/
private theorem three_cpow_neg_five_div_six :
    (3 : ℂ) ^ (-5 / 6 : ℂ) = (√3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num)]
  push_cast
  rw [← cpow_add _ _ (by norm_num)]
  norm_num

/-- `(√3)² = 3` in `ℂ`. -/
private theorem ofReal_sqrt_three_sq : (√3 : ℂ) ^ 2 = 3 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- For a cube root of unity `ν`, `Ai(νz) = ((1 + ν) Ai(z) + (1 − ν) Bi(z)/√3)/2`. -/
theorem airyAi_mul_of_pow_three_eq_one {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    airyAi (ν * z) = ((1 + ν) * airyAi z + (1 - ν) * airyBi z / √3) / 2 := by
  rw [airyAi_def, airyAi_def, airyBi_def, mul_pow, hν, one_mul, three_cpow_neg_one_div_six,
    three_cpow_neg_five_div_six]
  field_simp
  ring

/-- For a cube root of unity `ν`, `Bi(νz) = ((1 + ν) Bi(z) + √3 (1 − ν) Ai(z))/2`. -/
theorem airyBi_mul_of_pow_three_eq_one {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    airyBi (ν * z) = ((1 + ν) * airyBi z + √3 * (1 - ν) * airyAi z) / 2 := by
  rw [airyBi_def, airyAi_def, airyBi_def, mul_pow, hν, one_mul, three_cpow_neg_one_div_six,
    three_cpow_neg_five_div_six]
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

/-- `e^{πi/3} = 1/2 + (√3/2) i`. -/
private theorem exp_pi_mul_I_div_three : cexp (π * I / 3) = 1 / 2 + √3 / 2 * I := by
  rw [show π * I / 3 = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- `e^{−πi/3} = 1/2 − (√3/2) i`. -/
private theorem exp_neg_pi_mul_I_div_three : cexp (-(π * I / 3)) = 1 / 2 - √3 / 2 * I := by
  rw [show -(π * I / 3) = ((-(π / 3) : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three]
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

/-- `ω³ = 1`. -/
private theorem exp_two_pi_mul_I_div_three_pow_three : cexp (2 * π * I / 3) ^ 3 = 1 := by
  exact_mod_cast (isPrimitiveRoot_exp 3 (by norm_num)).pow_eq_one

/-- `ω^{−3} = 1`. -/
private theorem exp_neg_two_pi_mul_I_div_three_pow_three : cexp (-(2 * π * I / 3)) ^ 3 = 1 := by
  rw [exp_neg, inv_pow, exp_two_pi_mul_I_div_three_pow_three, inv_one]

/-- `Ai(z e^{−2πi/3}) = ½ e^{−πi/3} (Ai(z) + i Bi(z))` (DLMF 9.2.11, upper signs). -/
theorem airyAi_mul_exp_neg_two_pi_mul_I_div_three (z : ℂ) :
    airyAi (z * cexp (-(2 * π * I / 3))) =
      1 / 2 * cexp (-(π * I / 3)) * (airyAi z + I * airyBi z) := by
  rw [mul_comm, airyAi_mul_of_pow_three_eq_one exp_neg_two_pi_mul_I_div_three_pow_three,
    exp_neg_two_pi_mul_I_div_three, exp_neg_pi_mul_I_div_three]
  field_simp
  linear_combination (I ^ 2 * airyBi z) * ofReal_sqrt_three_sq + 3 * airyBi z * I_sq

/-- `Ai(z e^{2πi/3}) = ½ e^{πi/3} (Ai(z) − i Bi(z))` (DLMF 9.2.11, lower signs). -/
theorem airyAi_mul_exp_two_pi_mul_I_div_three (z : ℂ) :
    airyAi (z * cexp (2 * π * I / 3)) =
      1 / 2 * cexp (π * I / 3) * (airyAi z - I * airyBi z) := by
  rw [mul_comm, airyAi_mul_of_pow_three_eq_one exp_two_pi_mul_I_div_three_pow_three,
    exp_two_pi_mul_I_div_three, exp_pi_mul_I_div_three]
  field_simp
  linear_combination (I ^ 2 * airyBi z) * ofReal_sqrt_three_sq + 3 * airyBi z * I_sq

/-- **Connection formula** `Bi(z) = e^{−πi/6} Ai(z e^{−2πi/3}) + e^{πi/6} Ai(z e^{2πi/3})`
(DLMF 9.2.10). -/
theorem airyBi_eq_airyAi_rotations (z : ℂ) :
    airyBi z = cexp (-(π * I / 6)) * airyAi (z * cexp (-(2 * π * I / 3))) +
      cexp (π * I / 6) * airyAi (z * cexp (2 * π * I / 3)) := by
  rw [airyAi_mul_exp_neg_two_pi_mul_I_div_three, airyAi_mul_exp_two_pi_mul_I_div_three,
    exp_neg_pi_mul_I_div_six, exp_pi_mul_I_div_six, exp_neg_pi_mul_I_div_three,
    exp_pi_mul_I_div_three]
  linear_combination (I ^ 2 * airyBi z / 4) * ofReal_sqrt_three_sq +
    (airyBi z - √3 * airyAi z / 4) * I_sq

/-- `Ai(z) + e^{−2πi/3} Ai(z e^{−2πi/3}) + e^{2πi/3} Ai(z e^{2πi/3}) = 0` (DLMF 9.2.12). -/
theorem airyAi_add_rotations_eq_zero (z : ℂ) :
    airyAi z + cexp (-(2 * π * I / 3)) * airyAi (z * cexp (-(2 * π * I / 3))) +
      cexp (2 * π * I / 3) * airyAi (z * cexp (2 * π * I / 3)) = 0 := by
  rw [airyAi_mul_exp_neg_two_pi_mul_I_div_three, airyAi_mul_exp_two_pi_mul_I_div_three,
    exp_neg_two_pi_mul_I_div_three, exp_two_pi_mul_I_div_three, exp_neg_pi_mul_I_div_three,
    exp_pi_mul_I_div_three]
  linear_combination (I ^ 2 * airyAi z / 4) * ofReal_sqrt_three_sq + 3 * airyAi z / 4 * I_sq

/-- `Bi(z) + e^{−2πi/3} Bi(z e^{−2πi/3}) + e^{2πi/3} Bi(z e^{2πi/3}) = 0` (DLMF 9.2.13). -/
theorem airyBi_add_rotations_eq_zero (z : ℂ) :
    airyBi z + cexp (-(2 * π * I / 3)) * airyBi (z * cexp (-(2 * π * I / 3))) +
      cexp (2 * π * I / 3) * airyBi (z * cexp (2 * π * I / 3)) = 0 := by
  rw [mul_comm z, mul_comm z,
    airyBi_mul_of_pow_three_eq_one exp_neg_two_pi_mul_I_div_three_pow_three,
    airyBi_mul_of_pow_three_eq_one exp_two_pi_mul_I_div_three_pow_three,
    exp_neg_two_pi_mul_I_div_three, exp_two_pi_mul_I_div_three]
  linear_combination (I ^ 2 * (airyBi z - √3 * airyAi z) / 4) * ofReal_sqrt_three_sq +
    3 * (airyBi z - √3 * airyAi z) / 4 * I_sq

/-- `−z e^{−2πi/3} = z e^{πi/3}`: the rotations of `−z` by `ω^{∓1}` are the rotations of `z`
by `e^{±πi/3}`. -/
private theorem neg_mul_exp_neg_two_pi_mul_I_div_three (z : ℂ) :
    -z * cexp (-(2 * π * I / 3)) = z * cexp (π * I / 3) := by
  rw [exp_neg_two_pi_mul_I_div_three, exp_pi_mul_I_div_three]
  ring

/-- `−z e^{2πi/3} = z e^{−πi/3}`. -/
private theorem neg_mul_exp_two_pi_mul_I_div_three (z : ℂ) :
    -z * cexp (2 * π * I / 3) = z * cexp (-(π * I / 3)) := by
  rw [exp_two_pi_mul_I_div_three, exp_neg_pi_mul_I_div_three]
  ring

/-- **Connection formula** `Ai(−z) = e^{πi/3} Ai(z e^{πi/3}) + e^{−πi/3} Ai(z e^{−πi/3})`
(DLMF 9.2.14). -/
theorem airyAi_neg_eq_airyAi_rotations (z : ℂ) :
    airyAi (-z) = cexp (π * I / 3) * airyAi (z * cexp (π * I / 3)) +
      cexp (-(π * I / 3)) * airyAi (z * cexp (-(π * I / 3))) := by
  have h := airyAi_add_rotations_eq_zero (-z)
  rw [neg_mul_exp_neg_two_pi_mul_I_div_three, neg_mul_exp_two_pi_mul_I_div_three,
    exp_neg_two_pi_mul_I_div_three, exp_two_pi_mul_I_div_three] at h
  linear_combination h - airyAi (z * cexp (π * I / 3)) * exp_pi_mul_I_div_three -
    airyAi (z * cexp (-(π * I / 3))) * exp_neg_pi_mul_I_div_three

/-- **Connection formula** `Bi(−z) = e^{−πi/6} Ai(z e^{πi/3}) + e^{πi/6} Ai(z e^{−πi/3})`
(DLMF 9.2.15). -/
theorem airyBi_neg_eq_airyAi_rotations (z : ℂ) :
    airyBi (-z) = cexp (-(π * I / 6)) * airyAi (z * cexp (π * I / 3)) +
      cexp (π * I / 6) * airyAi (z * cexp (-(π * I / 3))) := by
  rw [airyBi_eq_airyAi_rotations, neg_mul_exp_neg_two_pi_mul_I_div_three,
    neg_mul_exp_two_pi_mul_I_div_three]

end TauCeti
