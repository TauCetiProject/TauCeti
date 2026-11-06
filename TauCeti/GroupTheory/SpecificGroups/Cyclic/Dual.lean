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
`G →* Mˣ` with `G`. This file counts the characters fixed by precomposition with the `n`-th power
map `g ↦ g ^ n`: for `n ≠ 0` there are exactly `gcd(|G|, n - 1)` of them, in particular at most
`n - 1` when `n > 1`.

This count enters the classification of the irreducible characters of `GL₂(𝔽_q)`, where it bounds
the number of characters of the cyclic group `𝔽_{q²}ˣ` fixed by the Frobenius `u ↦ u ^ q`.

## Main results

* `IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_eq_gcd`: for `n ≠ 0`, exactly
  `gcd(|G|, n - 1)` characters of a finite cyclic group `G` are fixed by precomposition with the
  `n`-th power map.
-/

public section

namespace IsCyclic

variable (G M : Type*) [CommGroup G] [Finite G] [IsCyclic G] [CommMonoid M]
  [HasEnoughRootsOfUnity M (Nat.card G)]

/-- **Exactly `gcd(|G|, n - 1)` characters of a finite cyclic group `G` are fixed by the `n`-th
power map** (`n ≠ 0`): `χ ∘ (g ↦ g ^ n) = χ` says `χ ^ (n - 1) = 1`, and the character group is
isomorphic to `G`. -/
theorem natCard_monoidHom_comp_powMonoidHom_eq_eq_gcd {n : ℕ} (hn : n ≠ 0) :
    Nat.card {χ : G →* Mˣ // χ.comp (powMonoidHom n) = χ} = (Nat.card G).gcd (n - 1) := by
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self G M
  rw [← IsCyclic.card_powMonoidHom_ker]
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun χ => ?_)
  rw [MonoidHom.mem_ker, powMonoidHom_apply, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    ← map_pow, map_eq_one_iff e e.injective, ← mul_eq_right (b := χ), ← pow_succ,
    Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
  simp [MonoidHom.ext_iff]

end IsCyclic
