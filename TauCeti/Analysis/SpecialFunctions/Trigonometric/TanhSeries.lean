/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# The partial-fraction expansion of the hyperbolic tangent

The hyperbolic tangent has simple poles at the odd multiples of `i π / 2`, and its Mittag-Leffler
expansion runs over the odd integers: for every real `y`,

`(π / 2) tanh (π y / 2) = ∑_{n ≥ 0} 2 y / (y² + (2 n + 1)²)`.

This file derives it from Mathlib's partial-fraction expansion of the cotangent
(`cot_series_rep'`), whose terms `cotTerm z n = 1 / (z - (n + 1)) + 1 / (z + (n + 1))` collect the
poles at `± (n + 1)`. Halving the argument keeps exactly the poles at even integers
(`TauCeti.cotTerm_div_two`), so subtracting the two expansions isolates the odd poles
(`TauCeti.hasSum_cotTerm_two_mul`):

`π cot (π z) - (π / 2) cot (π z / 2) = ∑_{n ≥ 0} (1 / (z - (2 n + 1)) + 1 / (z + (2 n + 1)))`

for every non-integer `z`. Evaluating at `z = i y` turns cotangents into hyperbolic cotangents
(`Complex.cot_mul_I`), and `coth (2 u) - coth u / 2 = tanh u / 2` gives the expansion of the
hyperbolic tangent (`TauCeti.hasSum_pi_div_two_mul_tanh`).

## Main results

* `TauCeti.hasSum_cotTerm_two_mul`: the odd-pole part of the cotangent expansion;
* `TauCeti.hasSum_pi_div_two_mul_tanh`: the partial-fraction expansion of `tanh (π y / 2)`.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- Halving the argument of the cotangent term doubles the pole index:
`cotTerm (z / 2) n = 2 cotTerm z (2 n + 1)`, both sides collecting the poles at `± (2 n + 2)`. -/
theorem cotTerm_div_two (z : ℂ) (n : ℕ) : cotTerm (z / 2) n = 2 * cotTerm z (2 * n + 1) := by
  have h₁ : z / 2 - (n + 1) = (z - ((2 * n + 1 : ℕ) + 1)) / 2 := by push_cast; ring
  have h₂ : z / 2 + (n + 1) = (z + ((2 * n + 1 : ℕ) + 1)) / 2 := by push_cast; ring
  rw [cotTerm, cotTerm, h₁, h₂, one_div_div, one_div_div]
  ring

/-- **The odd-pole part of the cotangent expansion.** For `z ∉ ℤ`,
`π cot (π z) - (π / 2) cot (π z / 2) = ∑_{n ≥ 0} (1 / (z - (2 n + 1)) + 1 / (z + (2 n + 1)))`.
The full expansion of `π cot (π z)` collects all integer poles, and that of `π cot (π z / 2)`
exactly the even ones (`cotTerm_div_two`). -/
theorem hasSum_cotTerm_two_mul {z : ℂ} (hz : z ∈ integerComplement) :
    HasSum (fun n : ℕ ↦ cotTerm z (2 * n)) (π * cot (π * z) - π / 2 * cot (π * (z / 2))) := by
  have hz₂ : z / 2 ∈ integerComplement := by
    rintro ⟨k, hk⟩
    exact hz ⟨2 * k, by push_cast; rw [hk]; ring⟩
  have hall : HasSum (cotTerm z) (π * cot (π * z) - 1 / z) := by
    rw [cot_series_rep' hz]
    exact (summable_cotTerm hz).hasSum
  have hodd : HasSum (fun n : ℕ ↦ cotTerm z (2 * n + 1))
      ((π * cot (π * (z / 2)) - 1 / (z / 2)) / 2) := by
    have h := (summable_cotTerm hz₂).hasSum
    rw [← cot_series_rep' hz₂] at h
    simpa [cotTerm_div_two] using h.div_const 2
  have heven : HasSum (fun n : ℕ ↦ cotTerm z (2 * n)) (∑' n : ℕ, cotTerm z (2 * n)) :=
    ((summable_cotTerm hz).comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))).hasSum
  convert heven using 1
  have h := hall.unique (heven.even_add_odd hodd)
  linear_combination h

/-- **The partial-fraction expansion of the hyperbolic tangent.** For every real `y`,
`(π / 2) tanh (π y / 2) = ∑_{n ≥ 0} 2 y / (y² + (2 n + 1)²)`. -/
theorem hasSum_pi_div_two_mul_tanh (y : ℝ) :
    HasSum (fun n : ℕ ↦ 2 * y / (y ^ 2 + (2 * n + 1) ^ 2)) (π / 2 * Real.tanh (π * y / 2)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hz : (y : ℂ) * I ∈ integerComplement := by
    rintro ⟨k, hk⟩
    exact hy (by simpa using congrArg Complex.im hk.symm)
  have h := (hasSum_cotTerm_two_mul hz).mul_left I
  -- The terms of the odd-pole expansion at `z = i y` are real.
  have hterm (n : ℕ) :
      I * cotTerm (y * I) (2 * n) = ((2 * y / (y ^ 2 + (2 * n + 1) ^ 2) : ℝ) : ℂ) := by
    have hd : ((y : ℂ) ^ 2 + (2 * n + 1) ^ 2) ≠ 0 := by
      exact_mod_cast (by positivity : (0 : ℝ) < y ^ 2 + (2 * n + 1) ^ 2).ne'
    have hmul : (y * I + (2 * n + 1)) * (y * I - (2 * n + 1)) =
        -((y : ℂ) ^ 2 + (2 * n + 1) ^ 2) := by
      linear_combination (y : ℂ) ^ 2 * I_sq
    rw [cotTerm_identity hz]
    push_cast
    rw [hmul]
    field_simp
    linear_combination -(y : ℂ) * I_sq
  simp only [hterm] at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  -- At `z = i y` the cotangents become hyperbolic cotangents, `cot (i x) = -i coth x`, and
  -- `coth (2 u) - coth u / 2 = tanh u / 2` for `u = π y / 2`.
  have hu : π * y / 2 ≠ 0 := by positivity
  have hs : sinh (π * y / 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sinh_ne_zero.mpr hu
  have hc : cosh (π * y / 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos (π * y / 2)).ne'
  have e₁ : (π : ℂ) * (y * I) = 2 * (π * y / 2) * I := by ring
  have e₂ : (π : ℂ) * (y * I / 2) = π * y / 2 * I := by ring
  rw [e₁, e₂, cot_mul_I, cot_mul_I, cosh_two_mul, sinh_two_mul]
  push_cast [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [I_sq]
  ring

end TauCeti
