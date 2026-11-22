/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.RamificationGroup
public import Mathlib.GroupTheory.PGroup

/-!
# Positive ramification groups are p-groups

For a place in residue characteristic `p`, every successive quotient of the positive
ramification filtration has exponent `p`. When the inertia group is finite, the filtration
eventually reaches the trivial group. Iterating the quotient statement shows that every
element of a positive ramification group has `p`-power order, so the whole group is a
`p`-group. In particular, the first positive group is the wild inertia group.

This is the group-theoretic conclusion of Stichtenoth, *Algebraic Function Fields and Codes*,
second edition, Proposition 3.8.5. It uses no perfectness assumption on the residue field.
-/

public section

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (F)

omit [Algebra k F] [IsScalarTower k F F'] in
/-- Every positive ramification group of a finite inertia group is a `p`-group in residue
characteristic `p`. This includes the wild inertia group `G₁`. -/
theorem isPGroup_ramificationGroup_succ (P : Place k F') (p i : ℕ)
    [CharP P.ResidueField p] [Finite (ramificationGroup F P 0)] :
    IsPGroup p (ramificationGroup F P (i + 1)) := by
  have : Finite (ramificationGroup F P (i + 1)) :=
    Finite.of_injective _
      (Subgroup.inclusion_injective (ramificationGroup_antitone F P (Nat.zero_le (i + 1))))
  rw [ramificationGroup_def] at this ⊢
  exact IsLocalRing.isPGroup_ramificationGroup _ P.integers p (by push_cast; omega)

omit [Algebra k F] [IsScalarTower k F F'] in
/-- If the residue characteristic does not divide the order of inertia, every positive
ramification group is trivial. In a finite Galois extension with separable residue extension,
the order of inertia is the ramification index, so this is the tame case. -/
theorem ramificationGroup_succ_eq_bot_of_not_dvd_card_inertia
    (P : Place k F') (p i : ℕ) [CharP P.ResidueField p]
    (hp : ¬ p ∣ Nat.card (ramificationGroup F P 0)) :
    ramificationGroup F P (i + 1) = ⊥ := by
  rw [ramificationGroup_def] at *
  exact IsLocalRing.ramificationGroup_eq_bot_of_not_dvd_card_ramificationGroup_zero _ P.integers p
    (by push_cast; omega) hp

/-- Tame ramification has no wild inertia: in a finite Galois extension with separable
residue extension, if the residue characteristic does not divide the ramification index,
every positive ramification group is trivial. -/
theorem ramificationGroup_succ_eq_bot_of_tame (P : Place k F') (p i : ℕ)
    [CharP P.ResidueField p] [FiniteDimensional F F'] [IsGalois F F']
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    (hp : ¬ p ∣ ramificationIdx F P) :
    ramificationGroup F P (i + 1) = ⊥ := by
  apply ramificationGroup_succ_eq_bot_of_not_dvd_card_inertia F P p i
  rwa [ramificationGroup_zero, card_inertiaSubgroup F P]

end Place

end TauCeti
