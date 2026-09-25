/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Multiset.MapFold

/-!
# The multiset of orbit sizes

For a group `G` acting on a finite type `X`, the multiset of the sizes of the orbits of `G` on
`X` is a basic invariant of the action. This file records two ways in which it is preserved: by a
change of the acting group that does not change the orbits, and by an equivariant bijection of
the underlying types.

## Main results

* `Equiv.map_card_orbit_eq_of_image_orbit_eq`: a bijection carrying the orbits of one action onto
  the orbits of another preserves the multiset of orbit sizes.
* `Equiv.map_card_orbit_eq_of_map_smul`: an equivariant bijection preserves the multiset of orbit
  sizes.
* `TauCeti.map_card_orbit_eq_of_orbit_eq`: two actions on the same finite type with the same
  orbits have the same multiset of orbit sizes.
-/

public section

open MulAction

namespace Equiv

open scoped Classical in
/-- **A bijection matching the orbits preserves the orbit sizes.** If `e : X ≃ Y` carries every
orbit of `G` on `X` onto an orbit of `G'` on `Y`, then the multisets of orbit sizes of the two
actions agree. -/
theorem map_card_orbit_eq_of_image_orbit_eq {G G' X Y : Type*} [Group G] [Group G']
    [MulAction G X] [MulAction G' Y] [Fintype X] [Fintype Y] (e : X ≃ Y)
    (h : ∀ x : X, e '' orbit G x = orbit G' (e x)) :
    (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit) =
      (Finset.univ : Finset (orbitRel.Quotient G' Y)).val.map (fun ω => Nat.card ω.orbit) := by
  have key : ∀ x y : X, orbitRel G X x y ↔ orbitRel G' Y (e x) (e y) := fun x y => by
    rw [orbitRel_apply, orbitRel_apply, ← h, e.injective.mem_set_image]
  -- `e` induces an equivalence of the orbit quotients preserving orbit sizes.
  let e' : orbitRel.Quotient G X ≃ orbitRel.Quotient G' Y := Quotient.congr e key
  have hcard : ∀ ω : orbitRel.Quotient G X, Nat.card ω.orbit = Nat.card (e' ω).orbit := by
    intro ω
    refine Quotient.inductionOn' ω fun x => ?_
    rw [orbitRel.Quotient.orbit_mk, Quotient.mk''_eq_mk, Quotient.congr_mk, ← Quotient.mk''_eq_mk,
      orbitRel.Quotient.orbit_mk, ← h, Nat.card_image_of_injective e.injective]
  calc (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit)
      = Finset.univ.val.map (fun ω => Nat.card (e' ω).orbit) :=
        Multiset.map_congr rfl fun ω _ => hcard ω
    _ = (Finset.univ.val.map e').map (fun ω => Nat.card ω.orbit) := by
        rw [Multiset.map_map, Function.comp_def]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

open scoped Classical in
/-- **Equivariant bijections preserve orbit sizes.** If `e : X ≃ Y` is a bijection between finite
`G`-sets commuting with the action, then the multisets of orbit sizes of `X` and of `Y` agree. -/
theorem map_card_orbit_eq_of_map_smul {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    [Fintype X] [Fintype Y] (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit) =
      (Finset.univ : Finset (orbitRel.Quotient G Y)).val.map (fun ω => Nat.card ω.orbit) :=
  e.map_card_orbit_eq_of_image_orbit_eq fun x => by
    ext y
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, (he g x).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g • x, ⟨g, rfl⟩, he g x⟩

end Equiv

namespace TauCeti

open scoped Classical in
/-- **Same orbits, same orbit sizes.** If two group actions on a finite type have the same orbits,
then they have the same multiset of orbit sizes. -/
theorem map_card_orbit_eq_of_orbit_eq {G G' X : Type*} [Group G] [Group G'] [MulAction G X]
    [MulAction G' X] [Fintype X] (h : ∀ x : X, orbit G x = orbit G' x) :
    (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit) =
      (Finset.univ : Finset (orbitRel.Quotient G' X)).val.map (fun ω => Nat.card ω.orbit) :=
  (Equiv.refl X).map_card_orbit_eq_of_image_orbit_eq fun x => by
    rw [Equiv.coe_refl, Set.image_id, h, id_eq]

end TauCeti
