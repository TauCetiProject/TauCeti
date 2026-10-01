/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `IsCyclic.monoidHom_equiv_self` identifies the character group of a finite cyclic group with
-- the group itself.
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Characters of a finite cyclic group fixed by a power map

Let `G` be a finite cyclic group and `M` a commutative monoid with enough roots of unity of order
`|G|`, so that Mathlib's `IsCyclic.monoidHom_equiv_self` identifies the character group
`G →* Mˣ` with `G`. This file bounds the number of characters fixed by precomposition with the
`n`-th power map `g ↦ g ^ n`: for `n > 1` there are at most `n - 1` of them.

This bound enters the count of the irreducible characters of `GL₂(𝔽_q)`, where it bounds the
number of characters of the cyclic group `𝔽_{q²}ˣ` fixed by the Frobenius `u ↦ u ^ q`.

## Main results

* `IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_le`: for `n > 1`, at most `n - 1` characters
  of a finite cyclic group are fixed by precomposition with the `n`-th power map.
-/

public section

namespace IsCyclic

variable (G M : Type*) [CommGroup G] [Finite G] [IsCyclic G] [CommMonoid M]
  [HasEnoughRootsOfUnity M (Nat.card G)]

/-- **At most `n - 1` characters of a finite cyclic group are fixed by the `n`-th power map**
(`n > 1`). -/
theorem natCard_monoidHom_comp_powMonoidHom_eq_le {n : ℕ} (hn : 1 < n) :
    Nat.card {χ : G →* Mˣ // χ.comp (powMonoidHom n) = χ} ≤ n - 1 := by
  classical
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self G M
  have : Finite (G →* Mˣ) := Finite.of_equiv G e.symm
  have : IsCyclic (G →* Mˣ) := e.isCyclic.2 ‹_›
  let := Fintype.ofFinite (G →* Mˣ)
  have hfix (χ : G →* Mˣ) : χ.comp (powMonoidHom n) = χ ↔ χ ^ (n - 1) = 1 := by
    rw [← mul_eq_right (b := χ), ← pow_succ, Nat.sub_add_cancel hn.le]
    simp [MonoidHom.ext_iff]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfix), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le (Nat.sub_pos_of_lt hn)

end IsCyclic
