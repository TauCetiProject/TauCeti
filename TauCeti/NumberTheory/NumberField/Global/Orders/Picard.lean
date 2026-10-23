/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.ProperIdeal
public import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Invertible ideals and the Picard group of an order

For an order in a number field, the invertible fractional ideals are precisely the units of its
fractional-ideal monoid. Every such ideal is proper, although a proper ideal need not be invertible.
The wide Picard group is their quotient by nonzero principal ideals. Mathlib's `ClassGroup` already
forms this quotient for every domain, so the Picard group of an order uses that carrier rather than
constructing a second quotient.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The wide Picard group of an order: invertible fractional ideals modulo principal ideals.
`ClassGroup` already implements this quotient for every integral domain. -/
abbrev Pic (O : NumberFieldOrder K) := ClassGroup O.toSubalgebra

namespace NumberFieldOrder

/-- The wide Picard class of an invertible fractional ideal. -/
abbrev mkPic (O : NumberFieldOrder K) : O.invertibleProperFractionalIdeals →* Pic O :=
  ClassGroup.mk K

/-- Every wide Picard class has an invertible fractional-ideal representative. -/
theorem mkPic_surjective (O : NumberFieldOrder K) : Function.Surjective O.mkPic :=
  fun c => ClassGroup.induction (K := K) (P := fun c => ∃ I, O.mkPic I = c)
    (fun I => ⟨I, rfl⟩) c

end NumberFieldOrder

end TauCeti.GlobalNumberFields
