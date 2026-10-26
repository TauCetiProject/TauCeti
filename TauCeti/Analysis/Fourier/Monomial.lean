/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pointwise identities and estimates for the Fourier monomials

Mathlib's lemmas about `fourier n : C(AddCircle T, ℂ)` mostly record its behaviour in the index
`n`. This file records the facts about the dependence on the point that translation-invariant
Fourier arguments use: the monomial turns a sum of points into a product, differentiating it
produces the frequency factor `2πin/T` of norm `2π|n|/T`, and consequently it is Lipschitz in a
real parameter with that constant.

## Main statements

* `TauCeti.fourier_apply_add`: `fourier n (x + y) = fourier n x * fourier n y`.
* `TauCeti.norm_two_pi_I_mul_intCast_div`: `‖2πin/T‖ = 2π/T |n|` for `T > 0`.
* `TauCeti.norm_fourier_coe_sub_le`: `‖e_n φ - e_n ψ‖ ≤ ‖2πin/T‖ |φ - ψ|` for real `φ, ψ`.
-/

public section

open Complex Real

namespace TauCeti

variable {T : ℝ}

/-- A Fourier monomial turns a sum of points into a product:
`fourier n (x + y) = fourier n x * fourier n y`. -/
theorem fourier_apply_add (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp [AddCircle.toCircle_add]

/-- The frequency factor `2πin/T` by which differentiation multiplies the Fourier monomial
`fourier n` (`hasDerivAt_fourier`) has norm `2π/T |n|`. -/
theorem norm_two_pi_I_mul_intCast_div (hT : 0 < T) (n : ℤ) :
    ‖(2 * π * I * n / T : ℂ)‖ = 2 * π / T * |(n : ℝ)| := by
  simp only [norm_div, norm_mul, norm_I, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos hT, abs_of_pos Real.pi_pos]
  ring

/-- The Fourier monomial `x ↦ e^{2πinx/T}` is Lipschitz in a real parameter with constant
`‖2πin/T‖`. -/
theorem norm_fourier_coe_sub_le (n : ℤ) (φ ψ : ℝ) :
    ‖fourier n (φ : AddCircle T) - fourier n (ψ : AddCircle T)‖ ≤
      ‖(2 * π * I * n / T : ℂ)‖ * |φ - ψ| := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ ↦ fourier n (y : AddCircle T)) (s := Set.univ)
    (fun y _ ↦ (hasDerivAt_fourier T n y).hasDerivWithinAt)
    (fun y _ ↦ by rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]) (Set.mem_univ ψ)
    (Set.mem_univ φ)
  rwa [Real.norm_eq_abs] at h

end TauCeti
