/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.Algebra.Group.PowMonoidHom
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.EffectiveBounds.UnitSquares.Equality

/-!
# The index of squares in the unit group of a number field

For a number field `F`, the subgroup of squares of the unit group has index at most `2^[F:ℚ]`:

`[O_F^× : (O_F^×)²] ≤ 2^[F:ℚ]`.

This is the degree-bounded shadow of the exact index
`TauCeti.NumberField.units_sq_index_eq` (`[O_F^× : (O_F^×)²] = 2^(rank F + 1)`, from
Dirichlet's unit theorem, in `TauCeti.NumberTheory.EffectiveBounds.UnitSquares.Equality`):
the bound follows since `rank F + 1 ≤ [F:ℚ]`
(`TauCeti.NumberField.rank_add_one_le_finrank`).

## Main results

* `TauCeti.NumberField.units_sq_index_le`: `[O_F^× : (O_F^×)²] ≤ 2^[F:ℚ]`.

The remaining declarations are its degree-bounded consumer forms
(`units_sq_index_le_of_finrank_le`, `..._of_finrank_eq`, the quadratic `..._le_quadratic`, and so
on) together with the same estimates transported to the cardinality of the elementary-2 quotient
`O_F^×/(O_F^×)²` via `TauCeti.card_elementaryTwoQuotient_eq_index_square`. They restate the exact
bound above against an external degree bound and add no new content beyond `units_sq_index_le`.

## Provenance

The statement was migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where this bound fed an explicit class-number estimate. (The original
generating-set proof has since been replaced by the derivation from the exact index.)
-/

public section

open scoped NumberField

open Module NumberField NumberField.Units

namespace TauCeti.NumberField

/-- **Squares have small index in the unit group.** `[O_F^× : (O_F^×)²] ≤ 2^[F:ℚ]`, stated
using Mathlib's `Subgroup.square` for the subgroup of squares. This is the degree-bounded
corollary of the exact index `TauCeti.NumberField.units_sq_index_eq`
(`= 2^(rank F + 1)`), via `rank F + 1 ≤ [F:ℚ]`. -/
theorem units_sq_index_le (F : Type*) [Field F] [NumberField F] :
    (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ Module.finrank ℚ F := by
  rw [units_sq_index_eq F]
  exact Nat.pow_le_pow_right (by norm_num) (rank_add_one_le_finrank F)

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
integers of `ℚ`. This is the `≤` shadow of the exact value
`TauCeti.NumberField.units_sq_index_rat_eq_two`. -/
theorem units_sq_index_rat_le_two :
    (Subgroup.square (𝓞 ℚ)ˣ).index ≤ 2 :=
  le_of_eq units_sq_index_rat_eq_two

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

/-- In a degree-one number field, the elementary-2 quotient `O_F^×/(O_F^×)^2` has at most two
elements. -/
theorem card_units_elementaryTwoQuotient_le_of_finrank_eq_one
    (F : Type*) [Field F] [NumberField F] (hF : finrank ℚ F = 1) :
    Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤ 2 := by
  simpa using card_units_elementaryTwoQuotient_le_of_finrank_eq F hF

/-- The elementary-2 quotient of `ℤˣ` has at most two elements, viewed as the unit group of the
ring of integers of `ℚ`. This is the `≤` shadow of the exact value
`TauCeti.NumberField.units_sq_index_rat_eq_two`. -/
theorem card_units_elementaryTwoQuotient_rat_le_two :
    Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 ℚ)ˣ) ≤ 2 := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact le_of_eq units_sq_index_rat_eq_two

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
