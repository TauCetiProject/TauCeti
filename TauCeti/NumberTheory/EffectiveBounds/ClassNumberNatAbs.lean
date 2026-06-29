/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.ClassNumber

/-!
# Natural-discriminant forms of the effective class-number bound

The EffectiveBounds roadmap's Layer 1 class-number estimate gives

`h_F ≤ |d_F| * 4^[F:ℚ]`.

The core API in `TauCeti.NumberTheory.EffectiveBounds.ClassNumber` states the natural-number
consumer forms using the integer absolute value `|NumberField.discr F| ≤ D`. Later explicit
estimates often carry the same bound as `(NumberField.discr F).natAbs ≤ D`, especially after
using Mathlib's discriminant divisibility and tower formulas. This file records the direct
bridges from that spelling to the existing class-number estimate.

## Main results

* `TauCeti.NumberField.classNumber_le_of_natAbs_discr_le_of_finrank_le`: real-valued
  class-number bound from a natural absolute discriminant bound and a degree bound.
* `TauCeti.NumberField.classNumber_le_nat_of_natAbs_discr_le_of_finrank_le`: natural-number
  version of the same estimate.
* `TauCeti.NumberField.classNumber_le_natAbs_discr_mul_four_pow`: the exact consumer form
  `h_F ≤ (discr F).natAbs * 4^[F:ℚ]`.

No formal code is vendored. These are direct corollaries of the migrated Layer 1 class-number
bound; the source attribution for that proof is in
`TauCeti/NumberTheory/EffectiveBounds/ClassNumber.lean`.
-/

public section

open Module NumberField

namespace TauCeti.NumberField

/-- A natural absolute discriminant bound, viewed as a real absolute discriminant bound. -/
private lemma real_abs_discr_le_of_natAbs_le (F : Type*) [Field F] [NumberField F] {D : ℕ}
    (hD : (NumberField.discr F).natAbs ≤ D) :
    |(NumberField.discr F : ℝ)| ≤ D := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast hD

/-- **Class-number bound from a natural absolute discriminant bound.** If
`(discr F).natAbs ≤ D` and `[F : ℚ] ≤ n`, then `h_F ≤ D * 4^n`, as a real inequality. -/
theorem classNumber_le_of_natAbs_discr_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {D n : ℕ}
    (hD : (NumberField.discr F).natAbs ≤ D) (hn : finrank ℚ F ≤ n) :
    (NumberField.classNumber F : ℝ) ≤ D * 4 ^ n :=
  classNumber_le_of_abs_discr_le_of_finrank_le F
    (real_abs_discr_le_of_natAbs_le F hD) hn

/-- **Class-number bound from a natural absolute discriminant bound.** If
`(discr F).natAbs ≤ D` and `[F : ℚ] ≤ n`, then `h_F ≤ D * 4^n`. -/
theorem classNumber_le_nat_of_natAbs_discr_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {D n : ℕ}
    (hD : (NumberField.discr F).natAbs ≤ D) (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F ≤ D * 4 ^ n := by
  have hD_abs : |NumberField.discr F| ≤ D := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hD
  exact classNumber_le_nat_of_abs_discr_le_of_finrank_le F
    hD_abs hn

/-- If `(discr F).natAbs ≤ D`, then `h_F ≤ D * 4^[F:ℚ]`, as a real inequality. -/
theorem classNumber_le_of_natAbs_discr_le
    (F : Type*) [Field F] [NumberField F] {D : ℕ}
    (hD : (NumberField.discr F).natAbs ≤ D) :
    (NumberField.classNumber F : ℝ) ≤ D * 4 ^ finrank ℚ F :=
  classNumber_le_of_natAbs_discr_le_of_finrank_le F hD le_rfl

/-- Natural-number version of `TauCeti.NumberField.classNumber_le_of_natAbs_discr_le`. -/
theorem classNumber_le_nat_of_natAbs_discr_le
    (F : Type*) [Field F] [NumberField F] {D : ℕ}
    (hD : (NumberField.discr F).natAbs ≤ D) :
    NumberField.classNumber F ≤ D * 4 ^ finrank ℚ F :=
  classNumber_le_nat_of_natAbs_discr_le_of_finrank_le F hD le_rfl

/-- If `(discr F).natAbs ≤ D` and `[F : ℚ] = n`, then `h_F ≤ D * 4^n`. -/
theorem classNumber_le_nat_of_natAbs_discr_le_of_finrank_eq
    (F : Type*) [Field F] [NumberField F] {D n : ℕ}
    (hD : (NumberField.discr F).natAbs ≤ D) (hn : finrank ℚ F = n) :
    NumberField.classNumber F ≤ D * 4 ^ n :=
  classNumber_le_nat_of_natAbs_discr_le_of_finrank_le F hD (le_of_eq hn)

/-- **Exact natural-discriminant class-number bound.** For every number field,
`h_F ≤ (discr F).natAbs * 4^[F:ℚ]`. -/
theorem classNumber_le_natAbs_discr_mul_four_pow
    (F : Type*) [Field F] [NumberField F] :
    NumberField.classNumber F ≤ (NumberField.discr F).natAbs * 4 ^ finrank ℚ F :=
  classNumber_le_nat_of_natAbs_discr_le F le_rfl

/-- Degree-monotone exact natural-discriminant class-number bound. If `[F : ℚ] ≤ n`, then
`h_F ≤ (discr F).natAbs * 4^n`. -/
theorem classNumber_le_natAbs_discr_mul_four_pow_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {n : ℕ}
    (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F ≤ (NumberField.discr F).natAbs * 4 ^ n :=
  classNumber_le_nat_of_natAbs_discr_le_of_finrank_le F le_rfl hn

/-- Exact-degree natural-discriminant class-number bound. If `[F : ℚ] = n`, then
`h_F ≤ (discr F).natAbs * 4^n`. -/
theorem classNumber_le_natAbs_discr_mul_four_pow_of_finrank_eq
    (F : Type*) [Field F] [NumberField F] {n : ℕ}
    (hn : finrank ℚ F = n) :
    NumberField.classNumber F ≤ (NumberField.discr F).natAbs * 4 ^ n :=
  classNumber_le_natAbs_discr_mul_four_pow_of_finrank_le F (le_of_eq hn)

end TauCeti.NumberField
