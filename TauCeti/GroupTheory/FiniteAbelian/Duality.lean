/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# The character group of a finite group is the dual of its abelianization

A linear character of a group `G`, a homomorphism `G →* Mˣ` into the units of a commutative
monoid, kills every commutator, so it factors uniquely through the abelianization. Mathlib's
`Abelianization.lift` is that bijection, and Mathlib's
`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` counts the characters of a finite *commutative*
group. Composing the two counts the characters of an arbitrary finite group:

`Nat.card (G →* Mˣ) = Nat.card (Abelianization G)`.

The hypothesis is the one Mathlib's counting theorem carries, asked of the abelianization rather
than of `G`: `M` has enough roots of unity for the exponent of `Abelianization G`, which for an
algebraically closed field of characteristic zero is automatic. Nothing weaker will do, since a
character group can collapse for want of roots of unity — over `ℝ` the group `ZMod 3` has only the
trivial character, while its abelianization is itself.

## Main statements

* `TauCeti.card_monoidHom_eq_card_abelianization`: **the linear characters of a finite group are
  counted by its abelianization.**

In particular a finite group has a nontrivial linear character exactly when it is not perfect, and
a perfect group has none at all; the count is what turns a computation of the abelianization into a
complete list of linear characters.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 2, where the
  linear characters of `G` are identified with the characters of `G / G'`.
-/

public section

namespace TauCeti

/-- **The linear characters of a finite group are counted by its abelianization.** Every
homomorphism `G →* Mˣ` factors uniquely through `Abelianization G`, and the characters of a finite
commutative group with enough roots of unity in `M` are as many as its elements. -/
theorem card_monoidHom_eq_card_abelianization (G M : Type*) [Group G] [Finite G] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent (Abelianization G))] :
    Nat.card (G →* Mˣ) = Nat.card (Abelianization G) := by
  rw [← CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Abelianization G) M]
  exact Nat.card_congr Abelianization.lift

end TauCeti
