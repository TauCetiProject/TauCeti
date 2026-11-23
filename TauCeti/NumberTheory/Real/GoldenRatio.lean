/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Algebraic and numerical properties of the golden ratio

The golden ratio `φ` and its conjugate `ψ` are the two roots of `X² - X - 1`. This file records
the complex root multiset of this polynomial, which is used to compute with the conjugates of `φ`,
for instance to show that `φ` is a Pisot number and that the Mahler measure of `X² - X - 1` is `φ`.
It also records the identity `φ⁻¹ = φ - 1`, which keeps computations with `φ⁻¹` inside `ℤ[φ]`, the
integer and fractional parts of `φ` (so that `φ` is a fixed point of the Gauss map), the
evaluation `TauCeti.goldenEval` of `ℤ[φ] = QuadraticAlgebra ℤ 1 1` at `φ`, the elementary bound
`log φ < 1 / 2` (`φ² < e`), and the lower bound `1 ≤ |q * φ - p| * |q * ψ - p|` for integers `p`
and `q` that are not both zero, which holds because the product is the nonzero integer
`p ^ 2 - p * q - q ^ 2`. Since `q * ψ - p = q * φ - p - q * √5`, this gives the bound
`1 ≤ x * (x + |q| * √5)` on `x = |q * φ - p|`.

## Main results

* `TauCeti.floor_goldenRatio`, `TauCeti.fract_goldenRatio`, `TauCeti.inv_fract_goldenRatio`:
  `⌊φ⌋ = 1`, `Int.fract φ = φ - 1`, and `φ` is a fixed point of the Gauss map
  `x ↦ (Int.fract x)⁻¹`.
* `TauCeti.aroots_X_sq_sub_X_sub_one`: the complex roots of `X² - X - 1` are `φ` and `ψ`.
* `TauCeti.inv_goldenRatio_eq_goldenRatio_sub_one`: `φ⁻¹ = φ - 1`.
* `TauCeti.goldenEval_apply`: the evaluation at `φ` sends `a + b ω` to `a + b φ`.
* `TauCeti.log_goldenRatio_lt_one_half`: `Real.log Real.goldenRatio < 1 / 2`.
* `TauCeti.one_le_abs_mul_goldenRatio_sub_mul_abs_mul_goldenConj_sub`: for integers `p` and `q`
  that are not both zero, `1 ≤ |q * φ - p| * |q * ψ - p|`.
* `TauCeti.one_le_abs_mul_goldenRatio_sub_mul_add`: for integers `p` and `q` that are not both
  zero, `1 ≤ |q * φ - p| * (|q * φ - p| + |q| * √5)`.
-/

public section

open Polynomial
open scoped Real

namespace TauCeti

open scoped goldenRatio

/-- The inverse of the golden ratio is `φ⁻¹ = φ - 1`. -/
theorem inv_goldenRatio_eq_goldenRatio_sub_one : φ⁻¹ = φ - 1 := by
  rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
  ring

/-- Evaluation of `ℤ[φ] = QuadraticAlgebra ℤ 1 1`, whose generator `ω` satisfies `ω² = 1 + ω`, at
the golden ratio. -/
noncomputable def goldenEval : QuadraticAlgebra ℤ 1 1 →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨φ, by rw [one_smul, one_smul, ← sq, Real.goldenRatio_sq, add_comm]⟩

@[simp]
theorem goldenEval_apply (z : QuadraticAlgebra ℤ 1 1) : goldenEval z = z.re + z.im * φ := by
  simp [goldenEval, QuadraticAlgebra.lift_apply_apply]

/-- The integer part of the golden ratio is `1`. -/
@[simp]
theorem floor_goldenRatio : ⌊Real.goldenRatio⌋ = 1 :=
  Int.floor_eq_iff.mpr ⟨by simpa using Real.one_lt_goldenRatio.le, by
    norm_num; linarith [Real.goldenRatio_lt_two]⟩

/-- The fractional part of the golden ratio is `φ - 1`. -/
theorem fract_goldenRatio : Int.fract Real.goldenRatio = Real.goldenRatio - 1 := by
  simp [Int.fract]

/-- The golden ratio is a fixed point of the Gauss map `x ↦ (Int.fract x)⁻¹`. -/
theorem inv_fract_goldenRatio : (Int.fract Real.goldenRatio)⁻¹ = Real.goldenRatio := by
  rw [fract_goldenRatio, ← inv_goldenRatio_eq_goldenRatio_sub_one, inv_inv]

/-- The complex roots of `X² - X - 1` are the golden ratio `φ` and its conjugate `ψ`. -/
theorem aroots_X_sq_sub_X_sub_one :
    (X ^ 2 - X - 1 : ℤ[X]).aroots ℂ = {(Real.goldenRatio : ℂ), (Real.goldenConj : ℂ)} := by
  have hP : (X ^ 2 - X - 1 : ℤ[X]) = C 1 * X ^ 2 + C (-1) * X + C (-1) := by
    simp [sub_eq_add_neg]
  rw [hP, aroots_quadratic_eq_pair_iff_of_ne_zero' (by simp), map_neg, map_one, neg_neg, div_one,
    div_one]
  exact ⟨mod_cast Real.goldenRatio_add_goldenConj, mod_cast Real.goldenRatio_mul_goldenConj⟩

/-- The natural logarithm of the golden ratio is strictly less than `1 / 2`. -/
theorem log_goldenRatio_lt_one_half : Real.log Real.goldenRatio < 1 / 2 := by
  have hφ_sq : Real.goldenRatio ^ 2 < Real.exp 1 := by
    have h21 : Real.goldenRatio ^ 2 < 21 / 8 := by
      have h5 : √(5 : ℝ) < 9 / 4 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
      rw [Real.goldenRatio_sq, Real.goldenRatio]; linarith
    exact h21.trans (by linarith [Real.exp_one_gt_d9])
  have h := (Real.log_lt_log_iff (pow_pos Real.goldenRatio_pos 2) (Real.exp_pos 1)).mpr hφ_sq
  rw [Real.log_pow, Nat.cast_ofNat, Real.log_exp] at h
  linarith

/-- For integers `p` and `q` that are not both zero, the product of `|q * φ - p|` and
`|q * ψ - p|` is at least `1`, where `ψ` is the conjugate of `φ`. -/
theorem one_le_abs_mul_goldenRatio_sub_mul_abs_mul_goldenConj_sub {p q : ℤ} (h : p ≠ 0 ∨ q ≠ 0) :
    1 ≤ |q * φ - p| * |q * ψ - p| := by
  -- `q * x - p` vanishes for no irrational `x`: this is `p ≠ 0` when `q = 0`
  have hne : ∀ {x : ℝ}, Irrational x → (q : ℝ) * x - p ≠ 0 := fun {x} hx ↦ by
    rcases eq_or_ne q 0 with rfl | hq
    · simpa using h
    · exact sub_ne_zero.mpr ((hx.intCast_mul hq).ne_int p)
  have hprod : ((q : ℝ) * φ - p) * (q * ψ - p) = ((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ) := by
    push_cast
    linear_combination (q : ℝ) ^ 2 * Real.goldenRatio_mul_goldenConj -
      (p * q : ℝ) * Real.goldenRatio_add_goldenConj
  have h0 : p ^ 2 - p * q - q ^ 2 ≠ 0 := fun h0 ↦
    mul_ne_zero (hne Real.goldenRatio_irrational) (hne Real.goldenConj_irrational)
      (by rw [hprod, h0, Int.cast_zero])
  rw [← abs_mul, hprod, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h0

/-- For integers `p` and `q` that are not both zero, `x = |q * φ - p|` satisfies
`1 ≤ x * (x + |q| * √5)`. This bounds the approximation error `x` from below in terms of `|q|`. -/
theorem one_le_abs_mul_goldenRatio_sub_mul_add {p q : ℤ} (h : p ≠ 0 ∨ q ≠ 0) :
    1 ≤ |q * φ - p| * (|q * φ - p| + |(q : ℝ)| * √5) := by
  have hy : (q : ℝ) * ψ - p = q * φ - p - q * √5 := by
    rw [← Real.goldenRatio_sub_goldenConj]
    ring
  have hle : |(q : ℝ) * ψ - p| ≤ |q * φ - p| + |(q : ℝ)| * √5 :=
    calc |(q : ℝ) * ψ - p| = |q * φ - p - q * √5| := by rw [hy]
      _ ≤ |q * φ - p| + |(q : ℝ) * √5| := abs_sub _ _
      _ = |q * φ - p| + |(q : ℝ)| * √5 := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 5)]
  exact (one_le_abs_mul_goldenRatio_sub_mul_abs_mul_goldenConj_sub h).trans
    (mul_le_mul_of_nonneg_left hle (abs_nonneg _))

end TauCeti
