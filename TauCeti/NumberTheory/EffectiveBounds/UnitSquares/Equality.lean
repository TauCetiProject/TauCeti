/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.UnitsElementaryTwoQuotient
import TauCeti.NumberTheory.EffectiveBounds.Regulator

/-!
# When the unit-square index bound is an equality: the exact index

The equality companion of `TauCeti.NumberTheory.EffectiveBounds.UnitSquares.Basic`, mirroring
`TauCeti.NumberTheory.EffectiveBounds.Discriminant.Equality`: a purely downstream refinement of
the bound `[𝓞 F^× : (𝓞 F^×)²] ≤ 2^[F:ℚ]`. That bound is in fact the shadow of an exact value:
by Dirichlet's unit theorem (counted in
`TauCeti.NumberTheory.NumberField.UnitsElementaryTwoQuotient`),

`[𝓞 F^× : (𝓞 F^×)²] = 2 ^ (rank F + 1)`,

and `rank F + 1 ≤ [F : ℚ]` recovers the bound. Over `ℚ` the index is exactly `2` (the square
classes of `±1`).

## Main results

* `TauCeti.NumberField.units_sq_index_eq`: `[𝓞 F^× : (𝓞 F^×)²] = 2 ^ (rank F + 1)`.
* `TauCeti.NumberField.units_sq_index_rat_eq_two`: over `ℚ` the index is exactly `2`.
-/

public section

open scoped NumberField

open Module NumberField NumberField.Units

namespace TauCeti.NumberField

variable (F : Type*) [Field F] [NumberField F]

/-- **The exact unit-square index of genus theory.** For a number field `F`,
`[𝓞 F^× : (𝓞 F^×)²] = 2 ^ (rank F + 1)`. This is the subgroup-index reading of
`TauCeti.NumberField.card_units_elementaryTwoQuotient`; it sharpens the bound
`TauCeti.NumberField.units_sq_index_le` to an equality. -/
theorem units_sq_index_eq :
    (Subgroup.square (𝓞 F)ˣ).index = 2 ^ (rank F + 1) := by
  rw [← TauCeti.card_elementaryTwoQuotient_eq_index_square, card_units_elementaryTwoQuotient]

/-- Over `ℚ` the unit rank is zero, so the square subgroup of `(𝓞 ℚ)ˣ` has index exactly `2`
(the square classes of `±1`). This sharpens `TauCeti.NumberField.units_sq_index_rat_le_two`
and keeps the exact index formula honest in the smallest case. -/
theorem units_sq_index_rat_eq_two : (Subgroup.square (𝓞 ℚ)ˣ).index = 2 := by
  rw [units_sq_index_eq, TauCeti.NumberField.Units.rank_eq_zero_of_finrank_eq_one ℚ
    (finrank_self ℚ), pow_one]

end TauCeti.NumberField
