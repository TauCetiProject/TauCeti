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
* `TauCeti.norm_fourier_sub_one_le`: `‖e_n h - 1‖ ≤ ‖2πin/T‖ ‖h‖` on the circle, where `‖h‖` is
  the distance from `h` to `0`.
* `TauCeti.one_le_norm_fourier_sub_one`: `1 ≤ ‖e_n x - 1‖` for `T / (6 |n|) ≤ x ≤ T / (3 |n|)`.
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

/-- The Fourier monomial is Lipschitz on the circle with constant `‖2πin/T‖`, measured from `0`:
`‖e_n h - 1‖ ≤ ‖2πin/T‖ ‖h‖`, where `‖h‖` is the distance from `h` to `0`. -/
theorem norm_fourier_sub_one_le (n : ℤ) (h : AddCircle T) :
    ‖fourier n h - 1‖ ≤ ‖(2 * π * I * n / T : ℂ)‖ * ‖h‖ := by
  induction h using QuotientAddGroup.induction_on with | H x => ?_
  -- Read `h` on its representative `x - round (x / T) * T` closest to `0`.
  have hy : ((x - round (T⁻¹ * x) * T : ℝ) : AddCircle T) = x := by
    rw [AddCircle.coe_sub, sub_eq_self, AddCircle.coe_eq_zero_iff]
    exact ⟨round (T⁻¹ * x), zsmul_eq_mul _ _⟩
  have h := norm_fourier_coe_sub_le (T := T) n (x - round (T⁻¹ * x) * T) 0
  rwa [QuotientAddGroup.mk_zero, fourier_eval_zero, sub_zero, ← AddCircle.norm_eq, hy] at h

/-- `1 ≤ ‖e_n x - 1‖` for `T / (6 |n|) ≤ x ≤ T / (3 |n|)`, where the half angle `π n x / T` lies
between `π / 6` and `π / 3` in absolute value. -/
theorem one_le_norm_fourier_sub_one (hT : 0 < T) {n : ℤ} (hn : n ≠ 0) {x : ℝ}
    (hx₁ : T / (6 * |(n : ℝ)|) ≤ x) (hx₂ : x ≤ T / (3 * |(n : ℝ)|)) :
    1 ≤ ‖fourier n (x : AddCircle T) - 1‖ := by
  have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
  have hexp : (2 * π * I * n * x / T : ℂ) = I * ((2 * π * n * x / T : ℝ) : ℂ) := by
    push_cast
    ring
  rw [fourier_coe_apply, hexp, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
    Real.norm_two, Real.norm_eq_abs]
  set y := 2 * π * n * x / T / 2
  -- The angle `|y| = π |n| x / T` lies between `π / 6` and `π / 3`.
  have hy : |y| = π * (|(n : ℝ)| * x) / T := by
    have hx0 : 0 ≤ x := le_trans (by positivity) hx₁
    simp only [y, abs_div, abs_mul, abs_two, abs_of_pos pi_pos, abs_of_nonneg hx0, abs_of_pos hT]
    ring
  have hlo : π / 6 ≤ |y| := by
    rw [hy, le_div_iff₀ hT]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * |(n : ℝ)|)).1 hx₁
    nlinarith [pi_pos]
  have hhi : |y| ≤ π / 2 := by
    rw [hy, div_le_iff₀ hT]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * |(n : ℝ)|)).1 hx₂
    nlinarith [pi_pos]
  have hsin : 1 / 2 ≤ Real.sin |y| := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hhi hlo
  have habs : Real.sin |y| ≤ |Real.sin y| := by
    rcases abs_cases y with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      exact le_abs_self _
    · rw [h, Real.sin_neg]
      exact neg_le_abs _
  linarith

end TauCeti
