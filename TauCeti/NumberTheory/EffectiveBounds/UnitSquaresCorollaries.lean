/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.UnitSquares
public import TauCeti.Algebra.Group.ElementaryTwoQuotient
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Degree-bounded forms of the unit-square index bound

The EffectiveBounds roadmap's Layer 1 unit-square target gives the exact estimate

`[O_F^× : (O_F^×)^2] ≤ 2^[F:ℚ]`.

Later effective arguments often know only an external degree bound, or have already specialized the
degree to a small value. This file records those consumer forms without exposing the proof through
Dirichlet's unit theorem again.

## Main results

* `TauCeti.NumberField.units_sq_index_le_of_finrank_le`: if `[F : ℚ] ≤ n`, then
  `[O_F^× : (O_F^×)^2] ≤ 2^n`.
* `TauCeti.NumberField.units_sq_index_le_of_finrank_eq`: the exact-degree specialization.
* `TauCeti.NumberField.units_sq_index_le_quadratic`: the quadratic-field bound
  `[O_F^× : (O_F^×)^2] ≤ 4`.
* `TauCeti.NumberField.card_units_elementaryTwoQuotient_le_of_finrank_le`: the same bound for the
  cardinality of the elementary-2 quotient `O_F^×/(O_F^×)^2`.
* `TauCeti.NumberField.card_units_elementaryTwoQuotient_le_of_finrank_le_two`: the quotient
  cardinality bound specialized to `[F : ℚ] ≤ 2`.

No formal code is vendored. These are monotone corollaries of the migrated bound
`TauCeti.NumberField.units_sq_index_le`, whose source attribution is in
`TauCeti/NumberTheory/EffectiveBounds/UnitSquares.lean`.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

open Module NumberField

/-- If a number field has degree at most `n`, then the square subgroup of its unit group has
index at most `2^n`. This is the monotone form of
`TauCeti.NumberField.units_sq_index_le`, useful when the degree has been bounded separately. -/
theorem units_sq_index_le_of_finrank_le (F : Type*) [Field F] [NumberField F] {n : ℕ}
    (hn : finrank ℚ F ≤ n) :
    (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ n :=
  (units_sq_index_le F).trans (Nat.pow_le_pow_right (by norm_num) hn)

/-- Exact-degree specialization of `TauCeti.NumberField.units_sq_index_le`: if `[F : ℚ] = n`,
then `[O_F^× : (O_F^×)^2] ≤ 2^n`. -/
theorem units_sq_index_le_of_finrank_eq (F : Type*) [Field F] [NumberField F] {n : ℕ}
    (hn : finrank ℚ F = n) :
    (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ n :=
  units_sq_index_le_of_finrank_le F (le_of_eq hn)

/-- In a degree-one number field, the square subgroup of the unit group has index at most `2`. -/
theorem units_sq_index_le_of_finrank_eq_one (F : Type*) [Field F] [NumberField F]
    (hF : finrank ℚ F = 1) :
    (Subgroup.square (𝓞 F)ˣ).index ≤ 2 := by
  simpa using units_sq_index_le_of_finrank_eq F hF

/-- The square subgroup of `ℤˣ` has index at most `2`, viewed as the unit group of the ring of
integers of `ℚ`. -/
theorem units_sq_index_rat_le_two :
    (Subgroup.square (𝓞 ℚ)ˣ).index ≤ 2 :=
  units_sq_index_le_of_finrank_eq_one ℚ (finrank_self ℚ)

/-- In a quadratic number field, the square subgroup of the unit group has index at most `4`. -/
theorem units_sq_index_le_quadratic (F : Type*) [Field F] [NumberField F]
    (hF : finrank ℚ F = 2) :
    (Subgroup.square (𝓞 F)ˣ).index ≤ 4 := by
  simpa using units_sq_index_le_of_finrank_eq F hF

/-- If a number field has degree at most two, the square subgroup of the unit group has index at
most `4`. This is the form used when a quadratic-model argument supplies only `[F : ℚ] ≤ 2`. -/
theorem units_sq_index_le_of_finrank_le_two (F : Type*) [Field F] [NumberField F]
    (hF : finrank ℚ F ≤ 2) :
    (Subgroup.square (𝓞 F)ˣ).index ≤ 4 := by
  simpa using units_sq_index_le_of_finrank_le F hF

/-- If `[F : ℚ] ≤ n`, then the elementary-2 quotient `O_F^×/(O_F^×)^2` has at most `2^n`
elements. This is just the unit-square index bound translated through
`TauCeti.card_elementaryTwoQuotient_eq_index_square`. -/
theorem card_units_elementaryTwoQuotient_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {n : ℕ} (hn : finrank ℚ F ≤ n) :
    Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤ 2 ^ n := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact units_sq_index_le_of_finrank_le F hn

/-- Exact-degree version of
`TauCeti.NumberField.card_units_elementaryTwoQuotient_le_of_finrank_le`. -/
theorem card_units_elementaryTwoQuotient_le_of_finrank_eq
    (F : Type*) [Field F] [NumberField F] {n : ℕ} (hn : finrank ℚ F = n) :
    Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤ 2 ^ n :=
  card_units_elementaryTwoQuotient_le_of_finrank_le F (le_of_eq hn)

/-- If `[F : ℚ] ≤ 2`, then the elementary-2 quotient `O_F^×/(O_F^×)^2` has at most four
elements. -/
theorem card_units_elementaryTwoQuotient_le_of_finrank_le_two
    (F : Type*) [Field F] [NumberField F] (hF : finrank ℚ F ≤ 2) :
    Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤ 4 := by
  simpa using card_units_elementaryTwoQuotient_le_of_finrank_le F hF

/-- For a quadratic number field, the elementary-2 quotient `O_F^×/(O_F^×)^2` has at most four
elements. -/
theorem card_units_elementaryTwoQuotient_le_quadratic
    (F : Type*) [Field F] [NumberField F] (hF : finrank ℚ F = 2) :
    Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤ 4 := by
  exact card_units_elementaryTwoQuotient_le_of_finrank_le_two F (le_of_eq hF)

end TauCeti.NumberField
