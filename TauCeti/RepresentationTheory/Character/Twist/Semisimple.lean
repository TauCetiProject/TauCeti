/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# Twists of semisimple representations

The twist `Representation.charTwist χ ρ` of a representation `ρ` by a linear character `χ` has the
same lattice of subrepresentations as `ρ` (`Representation.subrepresentationCharTwistOrderIso`).
A representation is semisimple when this lattice is complemented, so the twist is semisimple
exactly when `ρ` is. The tensor products of `ρ` with the one-dimensional representation of `χ`, on
either side, are equivalent to the twist, so they are semisimple exactly when `ρ` is.

## Main results

* `Representation.isSemisimpleRepresentation_charTwist_iff`: the twist of `ρ` by a linear character
  is semisimple exactly when `ρ` is.
* `Representation.isSemisimpleRepresentation_ofLinearCharacter_tprod_iff` and
  `Representation.isSemisimpleRepresentation_tprod_ofLinearCharacter_iff`: the tensor product of
  `ρ` with a one-dimensional representation, on either side, is semisimple exactly when `ρ` is.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] (χ : G →* kˣ)
  (ρ : Representation k G V)

/-- **The twist of a representation by a linear character is semisimple exactly when the
representation is.** -/
@[simp]
theorem isSemisimpleRepresentation_charTwist_iff :
    (charTwist χ ρ).IsSemisimpleRepresentation ↔ ρ.IsSemisimpleRepresentation :=
  OrderIso.complementedLattice_iff (subrepresentationCharTwistOrderIso χ ρ)

/-- The instance form of `Representation.isSemisimpleRepresentation_charTwist_iff`: the twist of a
semisimple representation by a linear character is semisimple. -/
instance isSemisimpleRepresentation_charTwist [ρ.IsSemisimpleRepresentation] :
    (charTwist χ ρ).IsSemisimpleRepresentation :=
  (isSemisimpleRepresentation_charTwist_iff χ ρ).mpr ‹_›

/-- **The tensor product of the one-dimensional representation of a linear character with a
representation is semisimple exactly when the representation is.** -/
@[simp]
theorem isSemisimpleRepresentation_ofLinearCharacter_tprod_iff :
    ((ofLinearCharacter χ).tprod ρ).IsSemisimpleRepresentation ↔ ρ.IsSemisimpleRepresentation := by
  rw [← isSemisimpleRepresentation_charTwist_iff χ ρ]
  let e := tprodEquivCharTwist χ ρ
  exact ⟨fun _ ↦ e.toIntertwiningMap.isSemisimpleRepresentation_of_surjective e.surjective,
    fun _ ↦ e.symm.toIntertwiningMap.isSemisimpleRepresentation_of_surjective e.symm.surjective⟩

/-- **The tensor product of a representation with the one-dimensional representation of a linear
character is semisimple exactly when the representation is.** -/
@[simp]
theorem isSemisimpleRepresentation_tprod_ofLinearCharacter_iff :
    (ρ.tprod (ofLinearCharacter χ)).IsSemisimpleRepresentation ↔ ρ.IsSemisimpleRepresentation := by
  rw [← isSemisimpleRepresentation_charTwist_iff χ ρ]
  let e := tprodOfLinearCharacterEquivCharTwist χ ρ
  exact ⟨fun _ ↦ e.toIntertwiningMap.isSemisimpleRepresentation_of_surjective e.surjective,
    fun _ ↦ e.symm.toIntertwiningMap.isSemisimpleRepresentation_of_surjective e.symm.surjective⟩

/-- The instance form of `Representation.isSemisimpleRepresentation_ofLinearCharacter_tprod_iff`:
the tensor product of a one-dimensional representation with a semisimple representation is
semisimple. -/
instance isSemisimpleRepresentation_ofLinearCharacter_tprod [ρ.IsSemisimpleRepresentation] :
    ((ofLinearCharacter χ).tprod ρ).IsSemisimpleRepresentation :=
  (isSemisimpleRepresentation_ofLinearCharacter_tprod_iff χ ρ).mpr ‹_›

/-- The instance form of `Representation.isSemisimpleRepresentation_tprod_ofLinearCharacter_iff`:
the tensor product of a semisimple representation with a one-dimensional representation is
semisimple. -/
instance isSemisimpleRepresentation_tprod_ofLinearCharacter [ρ.IsSemisimpleRepresentation] :
    (ρ.tprod (ofLinearCharacter χ)).IsSemisimpleRepresentation :=
  (isSemisimpleRepresentation_tprod_ofLinearCharacter_iff χ ρ).mpr ‹_›

end Representation
