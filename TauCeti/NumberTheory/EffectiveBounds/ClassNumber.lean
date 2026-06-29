/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.EffectiveBounds.IdealCount

/-!
# An effective class-number bound

For a number field `F` of degree `n`, the class number is bounded by

`h_F ≤ |d_F| · 4ⁿ`.

By Mathlib's Minkowski bound (`NumberField.exists_ideal_in_class_of_norm_le`) every ideal
class contains an integral ideal of norm at most `(4/π)^s · (n!/nⁿ) · √|d_F| ≤ √|d_F|`, so the
classes inject into the ideals of norm `≤ √|d_F|`, of which there are at most `|d_F| · 2ⁿ` by
`card_ideal_absNorm_le`.

## Main result

* `TauCeti.NumberField.classNumber_le_bound`: `h_F ≤ |d_F| · 4^[F:ℚ]`.
* `TauCeti.NumberField.classNumber_le_of_abs_discr_le_of_finrank_le`: the monotone
  corollary from separate discriminant and degree bounds.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture.
-/

public section

open _root_.NumberField

namespace TauCeti.NumberField

/-- The squared Minkowski covolume factor, times `2 ^ n`, is at most `4 ^ n` whenever
`2 * s ≤ n`. -/
private lemma minkowski_factor_sq_mul_two_pow_le_four_pow {n s : ℕ} (h : 2 * s ≤ n) :
    (4 / Real.pi) ^ (2 * s) * ((n.factorial / n ^ n : ℝ)) ^ 2 * 2 ^ n ≤ 4 ^ n := by
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) ?_)
    (by positivity)) ?_
  · have h_factorial_le_pow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast Nat.factorial_le_pow n
    exact pow_le_one₀ (by positivity) (div_le_one_of_le₀ h_factorial_le_pow (by positivity))
  · have h_pi_le_two : (4 : ℝ) / Real.pi ≤ 2 := by
      rw [div_le_iff₀] <;> linarith [Real.pi_gt_three]
    have h_four : (4 : ℝ) = 2 ^ 2 := by norm_num
    refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
      h_pi_le_two _)
      (by positivity)) ?_
    rw [h_four, ← pow_mul, ← pow_add]
    gcongr <;> norm_num
    linarith

/-- **Class number bound.** The class number of a number field `F` is at most
`|discr F| * 4 ^ [F : ℚ]`. -/
theorem classNumber_le_bound (F : Type*) [Field F] [NumberField F] :
    (NumberField.classNumber F : ℝ) ≤
      |(NumberField.discr F : ℝ)| * 4 ^ Module.finrank ℚ F := by
  have := @NumberField.exists_ideal_in_class_of_norm_le F _ _
  choose f hf using this
  have h_card : (Set.ncard (Set.image (fun C => (f C : Ideal (𝓞 F))) Set.univ)) ≤
      (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
        ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
        |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
    have h_card : (Set.ncard {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤
        (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F *
          ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F *
            Real.sqrt |(discr F : ℝ)|)}) ≤
        (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
          ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
          |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
      convert card_ideal_absNorm_le F _ |>.2 using 1
      · ring_nf; norm_num [Real.sq_sqrt <| abs_nonneg _]
      · refine le_trans ?_ (hf 1 |>.2)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
    refine le_trans ?_ h_card
    gcongr
    · convert card_ideal_absNorm_le F _ |>.1 using 1
      refine le_trans ?_ (hf 1 |>.2)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
    · simp only [Set.image_univ]
      exact Set.range_subset_iff.mpr fun C =>
        ⟨by intro h; simpa [h] using f C |>.2, hf C |>.2⟩
  refine le_trans ?_ (h_card.trans ?_)
  · rw [Set.ncard_image_of_injective _ fun x y hxy => ?_, Set.ncard_univ]
    · norm_num [classNumber]
    · have := hf x; have := hf y; aesop
  · -- Simplify the right-hand side of the inequality.
    suffices h_simp : (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
        ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
        2 ^ Module.finrank ℚ F ≤ 4 ^ Module.finrank ℚ F by
      convert mul_le_mul_of_nonneg_left h_simp (abs_nonneg (discr F : ℝ)) using 1; ring
    have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
    exact minkowski_factor_sq_mul_two_pow_le_four_pow (by linarith)

/-- If a number field has discriminant bounded by `D` and degree bounded by `n`, then its class
number is bounded by `D * 4^n`.

This is the monotone form of `TauCeti.NumberField.classNumber_le_bound`, useful when the
discriminant and degree have already been bounded separately. -/
theorem classNumber_le_of_abs_discr_le_of_finrank_le (F : Type*) [Field F] [NumberField F]
    {D : ℝ} {n : ℕ} (hD : |(NumberField.discr F : ℝ)| ≤ D)
    (hn : Module.finrank ℚ F ≤ n) :
    (NumberField.classNumber F : ℝ) ≤ D * 4 ^ n := by
  calc
    (NumberField.classNumber F : ℝ)
        ≤ |(NumberField.discr F : ℝ)| * 4 ^ Module.finrank ℚ F :=
          classNumber_le_bound F
    _ ≤ D * 4 ^ n := by
      gcongr
      · exact le_trans (abs_nonneg (NumberField.discr F : ℝ)) hD
      · norm_num

/-- A version of `classNumber_le_of_abs_discr_le_of_finrank_le` with a natural-number
discriminant bound and a natural-number conclusion.

Here `|NumberField.discr F|` is the natural absolute value of the integer discriminant, so
this is the form to use when the available discriminant estimate is stated in `ℕ`. -/
theorem classNumber_le_nat_of_abs_discr_le_of_finrank_le (F : Type*) [Field F] [NumberField F]
    {D n : ℕ} (hD : |NumberField.discr F| ≤ D) (hn : Module.finrank ℚ F ≤ n) :
    NumberField.classNumber F ≤ D * 4 ^ n := by
  have hD_real : |(NumberField.discr F : ℝ)| ≤ (D : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast hD
  exact_mod_cast classNumber_le_of_abs_discr_le_of_finrank_le F hD_real hn

/-- If `|d_F| ≤ D`, then `h_F ≤ D * 4^[F:ℚ]`. -/
theorem classNumber_le_of_abs_discr_le (F : Type*) [Field F] [NumberField F] {D : ℝ}
    (hD : |(NumberField.discr F : ℝ)| ≤ D) :
    (NumberField.classNumber F : ℝ) ≤ D * 4 ^ Module.finrank ℚ F :=
  classNumber_le_of_abs_discr_le_of_finrank_le F hD le_rfl

/-- Natural-number version of `classNumber_le_of_abs_discr_le`. -/
theorem classNumber_le_nat_of_abs_discr_le (F : Type*) [Field F] [NumberField F] {D : ℕ}
    (hD : |NumberField.discr F| ≤ D) :
    NumberField.classNumber F ≤ D * 4 ^ Module.finrank ℚ F :=
  classNumber_le_nat_of_abs_discr_le_of_finrank_le F hD le_rfl

end TauCeti.NumberField
