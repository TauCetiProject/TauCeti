/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic
public import TauCeti.RepresentationTheory.FrobeniusGroup.Basic

/-!
# Finite affine groups as Frobenius groups

For a finite division ring `F` with at least three elements, the affine group `F ⋊ Fˣ` is a
Frobenius group.  Its linear factor `Fˣ` is the Frobenius complement and its translations form
the Frobenius kernel.  The general Frobenius theorem constructs the kernel from the complement
alone; the main result here identifies that abstractly constructed subgroup with the visible
translation factor.

The specialization to `ZMod 5` gives the roadmap's group of order twenty, with kernel of order
five and complement of order four.

## Main results

* `TauCeti.frobeniusKernelSubgroup_affineLinearSubgroup`: the Frobenius kernel is the translation
  subgroup.
* `TauCeti.card_frobeniusKernelSubgroup_affineLinearSubgroup`: the kernel has `|F|` elements.
* `TauCeti.card_affineLinearSubgroup`: the complement has `|F| - 1` elements.
* `TauCeti.card_affineGroup`: the affine group has `|F| (|F| - 1)` elements.
* `TauCeti.card_affineGroup_zmod_five`: the `F₅` example has order twenty.

The construction follows Isaacs, *Character Theory of Finite Groups*, Chapter 7.
-/

public section

namespace TauCeti

/-- The Frobenius kernel constructed from the linear factor of a finite affine group is exactly
its translation subgroup. -/
theorem frobeniusKernelSubgroup_affineLinearSubgroup
    (F : Type*) [DivisionRing F] [Finite F] :
    frobeniusKernelSubgroup (isTISubgroup_affineLinearSubgroup F) =
      affineTranslationSubgroup F :=
  frobeniusKernelSubgroup_eq_of_isComplement'
    (isTISubgroup_affineLinearSubgroup F)
    (isComplement'_affineTranslationSubgroup_affineLinearSubgroup F)

/-- The Frobenius kernel of a finite affine group has `|F|` elements. -/
theorem card_frobeniusKernelSubgroup_affineLinearSubgroup
    (F : Type*) [DivisionRing F] [Finite F] :
    Nat.card (frobeniusKernelSubgroup (isTISubgroup_affineLinearSubgroup F)) =
      Nat.card F := by
  rw [frobeniusKernelSubgroup_affineLinearSubgroup F,
    card_affineTranslationSubgroup]

section ZModFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The linear factor of the affine group over `F₅` is a Frobenius complement. -/
theorem isFrobeniusComplement_affineLinearSubgroup_zmod_five :
    IsFrobeniusComplement (affineLinearSubgroup (ZMod 5)) :=
  isFrobeniusComplement_affineLinearSubgroup (ZMod 5) (by rw [Nat.card_zmod]; omega)

/-- The affine group over `F₅` has order twenty. -/
theorem card_affineGroup_zmod_five : Nat.card (AffineGroup (ZMod 5)) = 20 := by
  rw [card_affineGroup, Nat.card_zmod]

/-- The linear Frobenius complement in the affine group over `F₅` has order four. -/
theorem card_affineLinearSubgroup_zmod_five :
    Nat.card (affineLinearSubgroup (ZMod 5)) = 4 := by
  rw [card_affineLinearSubgroup, Nat.card_zmod]

/-- The Frobenius kernel constructed from the linear complement in the affine group over `F₅`
has order five. -/
theorem card_frobeniusKernelSubgroup_affineLinearSubgroup_zmod_five :
    Nat.card (frobeniusKernelSubgroup
      (isTISubgroup_affineLinearSubgroup (ZMod 5))) = 5 := by
  rw [card_frobeniusKernelSubgroup_affineLinearSubgroup, Nat.card_zmod]

end ZModFive

end TauCeti
