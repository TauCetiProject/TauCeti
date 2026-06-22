/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.EffectiveBounds.ClassNumber

/-!
# Usable corollaries of the effective class-number bound

The main Layer-1 class-number estimate in `TauCeti.NumberField.classNumber_le_bound` is stated in
terms of the exact discriminant and exact degree:

`h_F ≤ |d_F| * 4^[F:ℚ]`.

In applications one often has only separate upper bounds for the discriminant and the degree, for
example after a quadratic discriminant estimate or a Hermite--Minkowski degree bound. This file
records the monotone corollaries that turn those two inputs into the directly usable estimate

`h_F ≤ D * 4^n`.

## Main results

* `TauCeti.NumberField.classNumber_le_of_abs_discr_le_of_finrank_le`: real-valued bound from
  `|d_F| ≤ D` and `[F:ℚ] ≤ n`.
* `TauCeti.NumberField.classNumber_le_nat_of_abs_discr_le_of_finrank_le`: the same bound as a
  natural-number inequality.
* `TauCeti.NumberField.classNumber_le_of_finrank_eq_two_of_abs_discr_le_twenty`: the small
  quadratic specialization behind the roadmap's `ℚ(√-5)` sanity check, giving `h_F ≤ 20 * 4^2`
  from `|d_F| ≤ 20` and `[F:ℚ] = 2`.
-/

namespace TauCeti

namespace NumberField

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
discriminant bound and a natural-number conclusion. -/
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

/-- A quadratic field with `|d_F| ≤ 20` has class number at most `20 * 4^2 = 320`.

This is the numerical upper-bound form used by the roadmap's `ℚ(√-5)` sanity check: once the
quadratic discriminant estimate gives `|d_F| ≤ 20` and the field has degree two, the general
class-number bound becomes a concrete inequality. -/
theorem classNumber_le_of_finrank_eq_two_of_abs_discr_le_twenty
    (F : Type*) [Field F] [NumberField F] (hfin : Module.finrank ℚ F = 2)
    (hD : |NumberField.discr F| ≤ 20) :
    NumberField.classNumber F ≤ 20 * 4 ^ 2 := by
  refine classNumber_le_nat_of_abs_discr_le_of_finrank_le F hD ?_
  omega

/-- The preceding quadratic specialization in evaluated form: `20 * 4^2 = 320`. -/
theorem classNumber_le_threeHundredTwenty_of_finrank_eq_two_of_abs_discr_le_twenty
    (F : Type*) [Field F] [NumberField F] (hfin : Module.finrank ℚ F = 2)
    (hD : |NumberField.discr F| ≤ 20) :
    NumberField.classNumber F ≤ 320 := by
  simpa using classNumber_le_of_finrank_eq_two_of_abs_discr_le_twenty F hfin hD

end NumberField

end TauCeti
