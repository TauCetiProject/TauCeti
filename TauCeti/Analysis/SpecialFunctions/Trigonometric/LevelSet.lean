/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Set.Countable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Level sets of first-order trigonometric polynomials

A real combination `a cos x + b sin x` is a single shifted cosine: with `z = a + b i`,

`a cos x + b sin x = ‖z‖ cos (x - arg z)`

(`Real.mul_cos_add_mul_sin_eq_norm_mul_cos_sub_arg`), the harmonic addition formula. Each level
set of `cos` is a union of two cosets of `2πℤ`, so it is countable (`Real.countable_setOf_cos_eq`),
and hence so is each level set of `a cos x + b sin x` unless `a = b = 0`
(`Real.countable_setOf_mul_cos_add_mul_sin_eq`). Since an interval of positive length is
uncountable, the complement of such a level set, or of a countable union of them, is dense.

This is the form in which a one-parameter family of `2 × 2` matrices such as `θ ↦ R(θ) A`, with
`R(θ)` a rotation, has trace avoiding a prescribed countable set of values for all but countably
many parameters.
-/

public section

open Complex Set

namespace Real

/-- **Harmonic addition.** A real combination of `cos x` and `sin x` is a shifted multiple of
`cos`: `a cos x + b sin x = ‖a + b i‖ cos (x - arg (a + b i))`. -/
theorem mul_cos_add_mul_sin_eq_norm_mul_cos_sub_arg (a b x : ℝ) :
    a * cos x + b * sin x = ‖(a + b * I : ℂ)‖ * cos (x - arg (a + b * I)) := by
  have hcos := norm_mul_cos_arg (a + b * I : ℂ)
  have hsin := norm_mul_sin_arg (a + b * I : ℂ)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hcos hsin
  rw [cos_sub]
  linear_combination (-cos x) * hcos - sin x * hsin

/-- **The level sets of `cos` are countable**: `cos x = c` only on the two cosets
`±arccos c + 2πℤ`, and nowhere if `|c| > 1`. -/
theorem countable_setOf_cos_eq (c : ℝ) : {x : ℝ | cos x = c}.Countable := by
  refine ((countable_range fun k : ℤ ↦ 2 * k * π + arccos c).union
    (countable_range fun k : ℤ ↦ 2 * k * π - arccos c)).mono ?_
  intro x (hx : cos x = c)
  have hc : cos (arccos c) = cos x := by
    rw [cos_arccos (hx ▸ neg_one_le_cos x) (hx ▸ cos_le_one x), hx]
  obtain ⟨k, hk | hk⟩ := cos_eq_cos_iff.1 hc
  · exact .inl ⟨k, hk.symm⟩
  · exact .inr ⟨k, hk.symm⟩

/-- **The level sets of `a cos x + b sin x` are countable** unless `a = b = 0`. -/
theorem countable_setOf_mul_cos_add_mul_sin_eq {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) (c : ℝ) :
    {x : ℝ | a * cos x + b * sin x = c}.Countable := by
  set z : ℂ := a + b * I
  have hz : ‖z‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    have hre := congrArg re h
    have him := congrArg im h
    simp [z] at hre him
    tauto
  -- On the level set, `cos (x - arg z) = c / ‖z‖`, and `x ↦ x - arg z` is injective.
  refine ((countable_setOf_cos_eq (c / ‖z‖)).preimage (sub_left_injective (b := arg z))).mono ?_
  intro x (hx : a * cos x + b * sin x = c)
  rw [mul_cos_add_mul_sin_eq_norm_mul_cos_sub_arg] at hx
  simp only [mem_preimage, mem_ofPred_eq]
  rw [eq_div_iff hz, ← hx, mul_comm]

end Real
