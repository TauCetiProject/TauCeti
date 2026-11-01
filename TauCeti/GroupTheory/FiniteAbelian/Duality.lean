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
than of `G`: writing `n` for `Monoid.exponent (Abelianization G)`, `HasEnoughRootsOfUnity M n` asks
that `M` contain a primitive `n`-th root of unity and that the `n`-th roots of unity in `M` form a
cyclic group. An algebraically closed field of characteristic zero satisfies it for every `n`. It is
a sufficient condition, not one shown here to be necessary, but some hypothesis on `M` is needed:
a character group can collapse for want of roots of unity — over `ℝ` the group `ZMod 3` has only the
trivial character, while its abelianization is itself — and it can also grow, since over `ℝ × ℝ`
the group `ZMod 2` has four characters rather than two.

In particular a finite group has a nontrivial linear character exactly when it is not perfect, and
a perfect group has none at all; the count is what turns a computation of the abelianization into a
complete list of linear characters.

## Main statements

* `TauCeti.card_monoidHom_eq_card_abelianization`: **the linear characters of a finite group are
  counted by its abelianization.**
* `CommGroup.card_monoidHom_not_le_ker`: for a finite commutative group `G` and a subgroup `H`,
  the characters of `G` that are nontrivial on `H` are `#G - #(G ⧸ H)` in number, since those
  trivial on `H` are the characters of `G ⧸ H` (Mathlib's `CommGroup.card_domRestrictHom_ker`).

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

namespace CommGroup

variable {G : Type*} (M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
  [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **The characters nontrivial on a subgroup.** If `M` has enough roots of unity, the
homomorphisms `G →* Mˣ` of a finite commutative group that are not trivial on a subgroup `H` are
`#G - #(G ⧸ H)` in number: those trivial on `H` are the characters of `G ⧸ H`. -/
theorem card_monoidHom_not_le_ker (H : Subgroup G) :
    Nat.card {φ : G →* Mˣ // ¬H ≤ φ.ker} = Nat.card G - Nat.card (G ⧸ H) := by
  classical
  have := Fintype.ofFinite (G →* Mˣ)
  have hle : Nat.card {φ : G →* Mˣ // H ≤ φ.ker} = Nat.card (G ⧸ H) := by
    rw [← card_domRestrictHom_ker M H]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun φ ↦ by simp [IsConcreteLE.le_iff])
  rw [← card_monoidHom_of_hasEnoughRootsOfUnity G M, ← hle, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

end CommGroup
