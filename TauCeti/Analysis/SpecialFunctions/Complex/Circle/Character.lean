/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

import TauCeti.Analysis.Fourier.AddCircle

/-!
# The characters `θ ↦ e^{iℓθ}` of the real line are distinct

For `ℓ ∈ ℤ`, the function `θ ↦ e^{iℓθ}` is a character of `ℝ` trivial on `2πℤ`, that is a
character of the circle, namely the Fourier monomial `fourier ℓ` on `AddCircle (2 * π)`. Distinct
integers give distinct characters, by `TauCeti.fourier_injective`.

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
  -- On the circle `ℝ / 2πℤ` the Fourier monomial `fourier n` is `θ ↦ e^{inθ}`.
  have key (n : ℤ) (x : ℝ) :
      2 * (Real.pi : ℂ) * I * n * x / ((2 * Real.pi : ℝ) : ℂ) = n * x * I := by
    push_cast
    field_simp
  refine fourier_injective (T := 2 * Real.pi) Real.two_pi_pos.ne' (ContinuousMap.ext fun x ↦ ?_)
  induction x using QuotientAddGroup.induction_on with
  | H x => rw [fourier_coe_apply, fourier_coe_apply, key, key]; exact congrFun h x

end TauCeti
