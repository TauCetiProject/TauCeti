/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.ClassNumber
public import TauCeti.NumberTheory.EffectiveBounds.UnitSquaresCorollaries

/-!
# Product bounds for class groups and unit-square quotients

The Layer 1 EffectiveBounds roadmap supplies two independent estimates for a number field `F`:

* `TauCeti.NumberField.classNumber_le_bound`, equivalently
  `h_F ≤ |d_F| * 4^[F:ℚ]`;
* `TauCeti.NumberField.units_sq_index_le`, equivalently
  `[O_F^× : (O_F^×)^2] ≤ 2^[F:ℚ]`.

Later effective arguments often need the product of these finite contributions. This file records
the direct consumer forms

`h_F * [O_F^× : (O_F^×)^2] ≤ |d_F| * 8^[F:ℚ]`

and the same estimate for the elementary-2 quotient `O_F^×/(O_F^×)^2`, together with monotone
versions using separate discriminant and degree bounds.

No formal code is vendored. These are arithmetic corollaries of the migrated Layer 1 bounds, whose
source attribution is in `TauCeti/NumberTheory/EffectiveBounds/ClassNumber.lean` and
`TauCeti/NumberTheory/EffectiveBounds/UnitSquares.lean`.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

open Module NumberField

private lemma abs_discr_le_natAbs (F : Type*) [Field F] [NumberField F] :
    |NumberField.discr F| ≤ (NumberField.discr F).natAbs := by
  rw [Int.abs_eq_natAbs]

private lemma four_pow_mul_two_pow (n : ℕ) : 4 ^ n * 2 ^ n = 8 ^ n := by
  rw [← mul_pow]
  norm_num

/-- **Class-number/unit-square product bound.** For a number field `F`, the product of its class
number and the index of squares in its unit group is at most `|d_F| * 8^[F:ℚ]`. -/
theorem classNumber_mul_units_sq_index_le (F : Type*) [Field F] [NumberField F] :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤
      (NumberField.discr F).natAbs * 8 ^ finrank ℚ F := by
  have hclass :
      NumberField.classNumber F ≤ (NumberField.discr F).natAbs * 4 ^ finrank ℚ F :=
    classNumber_le_nat_of_abs_discr_le F (abs_discr_le_natAbs F)
  have hunits : (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ finrank ℚ F :=
    units_sq_index_le F
  calc
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index
        ≤ ((NumberField.discr F).natAbs * 4 ^ finrank ℚ F) * 2 ^ finrank ℚ F :=
          Nat.mul_le_mul hclass hunits
    _ = (NumberField.discr F).natAbs * 8 ^ finrank ℚ F := by
      rw [mul_assoc, four_pow_mul_two_pow]

/-- Monotone form of `TauCeti.NumberField.classNumber_mul_units_sq_index_le`: if `|d_F| ≤ D`
and `[F : ℚ] ≤ n`, then
`h_F * [O_F^× : (O_F^×)^2] ≤ D * 8^n`. -/
theorem classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {D n : ℕ}
    (hD : |NumberField.discr F| ≤ D) (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤ D * 8 ^ n := by
  have hclass : NumberField.classNumber F ≤ D * 4 ^ n :=
    classNumber_le_nat_of_abs_discr_le_of_finrank_le F hD hn
  have hunits : (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ n :=
    units_sq_index_le_of_finrank_le F hn
  calc
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index
        ≤ (D * 4 ^ n) * 2 ^ n := Nat.mul_le_mul hclass hunits
    _ = D * 8 ^ n := by
      rw [mul_assoc, four_pow_mul_two_pow]

/-- If `|d_F| ≤ D`, then
`h_F * [O_F^× : (O_F^×)^2] ≤ D * 8^[F:ℚ]`. -/
theorem classNumber_mul_units_sq_index_le_of_abs_discr_le
    (F : Type*) [Field F] [NumberField F] {D : ℕ}
    (hD : |NumberField.discr F| ≤ D) :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤
      D * 8 ^ finrank ℚ F :=
  classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le F hD le_rfl

/-- If `[F : ℚ] ≤ n`, then
`h_F * [O_F^× : (O_F^×)^2] ≤ |d_F| * 8^n`. -/
theorem classNumber_mul_units_sq_index_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {n : ℕ} (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤
      (NumberField.discr F).natAbs * 8 ^ n :=
  classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le F
    (abs_discr_le_natAbs F) hn

/-- The same product bound expressed using the elementary-2 quotient of units:
`h_F * #(O_F^×/(O_F^×)^2) ≤ |d_F| * 8^[F:ℚ]`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le
    (F : Type*) [Field F] [NumberField F] :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      (NumberField.discr F).natAbs * 8 ^ finrank ℚ F := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le F

/-- Monotone elementary-2 quotient form: if `|d_F| ≤ D` and `[F : ℚ] ≤ n`, then
`h_F * #(O_F^×/(O_F^×)^2) ≤ D * 8^n`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_of_abs_discr_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {D n : ℕ}
    (hD : |NumberField.discr F| ≤ D) (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      D * 8 ^ n := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le F hD hn

/-- If `|d_F| ≤ D`, then
`h_F * #(O_F^×/(O_F^×)^2) ≤ D * 8^[F:ℚ]`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_of_abs_discr_le
    (F : Type*) [Field F] [NumberField F] {D : ℕ}
    (hD : |NumberField.discr F| ≤ D) :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      D * 8 ^ finrank ℚ F := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le_of_abs_discr_le F hD

/-- If `[F : ℚ] ≤ n`, then
`h_F * #(O_F^×/(O_F^×)^2) ≤ |d_F| * 8^n`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {n : ℕ} (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      (NumberField.discr F).natAbs * 8 ^ n := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le_of_finrank_le F hn

end TauCeti.NumberField
