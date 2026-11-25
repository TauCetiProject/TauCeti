/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The characters `θ ↦ e^{iℓθ}` of the real line are distinct

For `ℓ ∈ ℤ`, the function `θ ↦ e^{iℓθ}` is a character of `ℝ` trivial on `2πℤ`, that is a
character of the circle. Distinct integers give distinct characters: if `ℓ ≠ ℓ'`, the two
functions differ at `θ = π / (ℓ - ℓ')`, where their ratio is `e^{iπ} = -1`.

## Main results

* `TauCeti.injective_exp_intCast_mul_mul_I`: `ℓ ↦ (θ ↦ e^{iℓθ})` is injective.
-/

public section

open Complex

namespace TauCeti

/-- The characters `θ ↦ e^{iℓθ}` of the rotation group are distinct for distinct `ℓ`. -/
theorem injective_exp_intCast_mul_mul_I :
    Function.Injective fun (ℓ : ℤ) (θ : ℝ) ↦ exp (ℓ * θ * I) := by
  intro ℓ ℓ' h
  by_contra hne
  set x : ℝ := Real.pi / (ℓ - ℓ' : ℤ)
  have hd : ((ℓ - ℓ' : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hx : ((ℓ - ℓ' : ℤ) : ℝ) * x = Real.pi := by
    simp only [x]
    field_simp
  have h1 : exp (ℓ * x * I) = exp (ℓ' * x * I) := congrFun h x
  have h2 : exp (ℓ * x * I) = exp (ℓ' * x * I) * exp (Real.pi * I) := by
    rw [← exp_add]
    congr 1
    have := congrArg (fun r : ℝ ↦ (r : ℂ) * I) hx
    push_cast at this
    linear_combination this
  rw [h2, exp_pi_mul_I] at h1
  exact exp_ne_zero _ (by linear_combination (-1 / 2 : ℂ) * h1)

end TauCeti
