/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Real inner products with a unit complex number

Multiplication by a unit complex number `ζ` is a rotation of the plane, so the real inner product
of `ζ` with `ζ * w` is the real inner product of `1` with `w`, namely the real part of `w`. This
lets the level sets `⟪ζ, z⟫_ℝ = t` be read in the rotated coordinate `w = conj ζ * z`.

## Main declarations

* `Complex.mul_conj_eq_one_of_norm_eq_one` -- a unit complex number times its conjugate is `1`.
* `Complex.inner_mul_left_of_norm_eq_one` -- `⟪ζ, ζ * w⟫_ℝ = w.re` for a unit `ζ`.
-/

public section

namespace Complex

variable {ζ : ℂ}

/-- A complex number of norm `1` times its conjugate is `1`. -/
theorem mul_conj_eq_one_of_norm_eq_one (hζ : ‖ζ‖ = 1) : ζ * (starRingEnd ℂ) ζ = 1 := by
  rw [mul_conj', hζ]
  norm_num

/-- The real inner product of a unit complex number `ζ` with `ζ * w` is the real part of `w`. -/
theorem inner_mul_left_of_norm_eq_one (hζ : ‖ζ‖ = 1) (w : ℂ) : inner ℝ ζ (ζ * w) = w.re := by
  rw [Complex.inner, mul_comm ζ w, mul_assoc, mul_conj_eq_one_of_norm_eq_one hζ, mul_one]

end Complex
