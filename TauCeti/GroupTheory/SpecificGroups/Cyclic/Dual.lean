/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `IsCyclic.monoidHom_equiv_self` identifies the character group of a finite cyclic group with
-- the group itself.
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
-- `IsCyclic.card_pow_eq_one_le` bounds the solutions of `x ^ n = 1` in a cyclic group.
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
-- Non-public: `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` gives the character group of a
-- finite commutative group the order of the group, inside a proof only.
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# The character group of a finite cyclic group

Let `G` be a finite cyclic group and `M` a commutative monoid with enough roots of unity of order
`|G|`, so that Mathlib's `IsCyclic.monoidHom_equiv_self` identifies the character group
`G →* Mˣ` with `G`. This file records one consequence: for `n > 1`, at most `n - 1` characters
are fixed by precomposition with the `n`-th power map `g ↦ g ^ n`, since such a character `χ`
satisfies `χ ^ (n - 1) = 1` and the character group, being isomorphic to `G`, is cyclic.

It also records the size of the character group of the archetypal finite cyclic group, the unit
group of a finite field `K`: by Mathlib's `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` it
has `|K| - 1` elements.

Both statements enter the count of the irreducible characters of `GL₂(𝔽_q)`: the character group
of `𝔽_{q²}ˣ` has `q² - 1` elements, and the first bounds the number of them fixed by the Frobenius
`u ↦ u ^ q`, which parametrise the reducible part of the cuspidal series.

## Main results

* `IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_le`: for `n > 1`, at most `n - 1` characters
  of a finite cyclic group are fixed by precomposition with the `n`-th power map.
* `FiniteField.natCard_monoidHom_units`: the character group of the unit group of a finite field
  `K` has `|K| - 1` elements.
-/

public section

namespace IsCyclic

variable (G M : Type*) [CommGroup G] [Finite G] [IsCyclic G] [CommMonoid M]
  [HasEnoughRootsOfUnity M (Nat.card G)]

/-- **At most `n - 1` characters of a finite cyclic group are fixed by the `n`-th power map**
(`n > 1`): a character `χ` with `χ (g ^ n) = χ g` for all `g` satisfies `χ ^ (n - 1) = 1`, and a
cyclic group has at most `n - 1` solutions of that equation. -/
theorem natCard_monoidHom_comp_powMonoidHom_eq_le {n : ℕ} (hn : 1 < n) :
    Nat.card {χ : G →* Mˣ // χ.comp (powMonoidHom n) = χ} ≤ n - 1 := by
  classical
  -- the character group is isomorphic to `G`, hence finite and cyclic
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self G M
  have : Finite (G →* Mˣ) := Finite.of_equiv G e.symm
  have : IsCyclic (G →* Mˣ) := e.isCyclic.2 ‹_›
  let := Fintype.ofFinite (G →* Mˣ)
  have hfix : ∀ χ : G →* Mˣ, χ.comp (powMonoidHom n) = χ ↔ χ ^ (n - 1) = 1 := by
    intro χ
    have hpow : χ.comp (powMonoidHom n) = χ ^ (n - 1) * χ := by
      refine MonoidHom.ext fun g => ?_
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, ← pow_succ, Nat.sub_add_cancel hn.le,
        MonoidHom.comp_apply, powMonoidHom_apply, map_pow]
    rw [hpow]
    exact ⟨fun h => mul_right_cancel (h.trans (one_mul χ).symm), fun h => by rw [h, one_mul]⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfix), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le (Nat.sub_pos_of_lt hn)

end IsCyclic

namespace FiniteField

/-- **The character group of the unit group of a finite field `K` has `|K| - 1` elements**, when
the coefficient monoid has enough roots of unity of order the exponent of `Kˣ`: the character
group of a finite commutative group has the order of the group, and `Kˣ` has `|K| - 1` elements. -/
theorem natCard_monoidHom_units (K M : Type*) [Field K] [Finite K] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Kˣ)] :
    Nat.card (Kˣ →* Mˣ) = Nat.card K - 1 := by
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_units]

end FiniteField
