/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Cyclic
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.FreeModule
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Prod
public import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# The exact number of square classes in the unit group of a number field

For a number field `F`, Dirichlet's unit theorem decomposes the unit group of its ring of
integers as the product of its torsion subgroup (finite cyclic of even order, as it contains
`-1`) and a free abelian group of rank `NumberField.Units.rank F` — the structural equivalence
`TauCeti.NumberField.unitsMulEquivTorsionProdMultiplicative` of
`TauCeti.NumberTheory.NumberField.Units.Dirichlet`. Counting square classes in each factor gives
the exact number of unit square classes of genus theory:

`|𝓞 F^× / (𝓞 F^×)²| = 2 ^ (rank F + 1)`.

This is the unit-square-class input of Layer 2 of the multiquadratic roadmap, feeding the
ambiguous-class-number formula and the genus-field 2-rank computation. Its reading as the exact
subgroup index `[𝓞 F^× : (𝓞 F^×)²] = 2 ^ (rank F + 1)` — sharpening the bound
`TauCeti.NumberField.units_sq_index_le` — lives with that bound, in
`TauCeti.NumberTheory.EffectiveBounds.UnitSquares.Equality`.

The counting combines the cyclic and free square-class computations of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Cyclic` and
`TauCeti.Algebra.Group.ElementaryTwoQuotient.FreeModule` through the product decomposition of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Prod`.

## Main results

* `TauCeti.NumberField.card_units_elementaryTwoQuotient`:
  `|𝓞 F^× / (𝓞 F^×)²| = 2 ^ (rank F + 1)`.
* `TauCeti.NumberField.twoRank_units`: the 2-rank of the unit group is `rank F + 1`.
-/

public section

open scoped NumberField

open Module NumberField NumberField.Units

namespace TauCeti.NumberField

variable (F : Type*) [Field F] [NumberField F]

/-- Mathlib's `NumberField.Units.torsionOrder` is by definition `Nat.card (torsion F)`, so
`even_torsionOrder` supplies the parity of `Nat.card (torsion F)` that the cyclic even-order
count expects. -/
private theorem even_card_torsion : Even (Nat.card (torsion F)) :=
  even_torsionOrder F

/-- **The unit group of a number field has `2 ^ (rank + 1)` square classes.** The torsion
subgroup is cyclic of even order (it contains `-1`), contributing one factor of `2`, and the
free part of Dirichlet rank contributes `2 ^ rank`. -/
theorem card_units_elementaryTwoQuotient :
    Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) = 2 ^ (rank F + 1) := by
  rw [Nat.card_congr
      (TauCeti.elementaryTwoQuotientCongr (unitsMulEquivTorsionProdMultiplicative F)).toEquiv,
    TauCeti.card_elementaryTwoQuotient_prod,
    TauCeti.card_elementaryTwoQuotient_of_isCyclic_of_even _ (even_card_torsion F),
    TauCeti.card_elementaryTwoQuotient_multiplicative, finrank_pi, Fintype.card_fin]
  ring

/-- The elementary-2 quotient of the unit group of a number field is finite. -/
instance : Finite (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) :=
  Nat.finite_of_card_ne_zero (by simp [card_units_elementaryTwoQuotient])

/-- The 2-rank of the unit group of a number field is `rank F + 1`. -/
theorem twoRank_units : TauCeti.twoRank (𝓞 F)ˣ = rank F + 1 :=
  TauCeti.twoRank_eq_of_card_elementaryTwoQuotient_eq_two_pow _
    (card_units_elementaryTwoQuotient F)

end TauCeti.NumberField
