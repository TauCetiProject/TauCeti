/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Quotient
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

* `MulAction.map_card_orbit_eq_of_orbit_eq`: two actions on the same finite type with the same
  orbits have the same multiset of orbit sizes.
* `MulAction.map_card_orbit_eq_of_equiv`: an equivariant bijection preserves the multiset of
  orbit sizes.
-/

public section

namespace MulAction

open scoped Classical in
/-- **Same orbits, same orbit sizes.** If two group actions on a finite type have the same orbits,
then they have the same multiset of orbit sizes. -/
theorem map_card_orbit_eq_of_orbit_eq {G G' X : Type*} [Group G] [Group G'] [MulAction G X]
    [MulAction G' X] [Fintype X] (h : ∀ x : X, orbit G x = orbit G' x) :
    (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit) =
      (Finset.univ : Finset (orbitRel.Quotient G' X)).val.map (fun ω => Nat.card ω.orbit) := by
  have key : ∀ x y : X, orbitRel G X x y ↔ orbitRel G' X (Equiv.refl X x) (Equiv.refl X y) :=
    fun x y => by rw [orbitRel_apply, orbitRel_apply, h, Equiv.refl_apply, Equiv.refl_apply]
  -- The identity of `X` induces an equivalence of the orbit quotients preserving orbit sizes.
  let e : orbitRel.Quotient G X ≃ orbitRel.Quotient G' X := Quotient.congr (Equiv.refl X) key
  have hcard : ∀ ω : orbitRel.Quotient G X, Nat.card ω.orbit = Nat.card (e ω).orbit := by
    intro ω
    refine Quotient.inductionOn' ω fun x => ?_
    rw [orbitRel.Quotient.orbit_mk, Quotient.mk''_eq_mk, Quotient.congr_mk, Equiv.refl_apply,
      ← Quotient.mk''_eq_mk, orbitRel.Quotient.orbit_mk, h]
  calc (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit)
      = Finset.univ.val.map (fun ω => Nat.card (e ω).orbit) :=
        Multiset.map_congr rfl fun ω _ => hcard ω
    _ = (Finset.univ.val.map e).map (fun ω => Nat.card ω.orbit) := by
        rw [Multiset.map_map, Function.comp_def]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

open scoped Classical in
/-- **Equivariant bijections preserve orbit sizes.** If `e : X ≃ Y` is a bijection between finite
`G`-sets commuting with the action, then the multisets of orbit sizes of `X` and of `Y` agree. -/
theorem map_card_orbit_eq_of_equiv {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    [Fintype X] [Fintype Y] (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit) =
      (Finset.univ : Finset (orbitRel.Quotient G Y)).val.map (fun ω => Nat.card ω.orbit) := by
  have himage : ∀ x : X, e '' orbit G x = orbit G (e x) := fun x => by
    ext y
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, (he g x).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g • x, ⟨g, rfl⟩, he g x⟩
  have key : ∀ x y : X, orbitRel G X x y ↔ orbitRel G Y (e x) (e y) := fun x y => by
    rw [orbitRel_apply, orbitRel_apply, ← himage, e.injective.mem_set_image]
  -- `e` induces an equivalence of the orbit quotients preserving orbit sizes.
  let e' : orbitRel.Quotient G X ≃ orbitRel.Quotient G Y := Quotient.congr e key
  have hcard : ∀ ω : orbitRel.Quotient G X, Nat.card ω.orbit = Nat.card (e' ω).orbit := by
    intro ω
    refine Quotient.inductionOn' ω fun x => ?_
    rw [orbitRel.Quotient.orbit_mk, Quotient.mk''_eq_mk, Quotient.congr_mk, ← Quotient.mk''_eq_mk,
      orbitRel.Quotient.orbit_mk, ← himage, Nat.card_image_of_injective e.injective]
  calc (Finset.univ : Finset (orbitRel.Quotient G X)).val.map (fun ω => Nat.card ω.orbit)
      = Finset.univ.val.map (fun ω => Nat.card (e' ω).orbit) :=
        Multiset.map_congr rfl fun ω _ => hcard ω
    _ = (Finset.univ.val.map e').map (fun ω => Nat.card ω.orbit) := by
        rw [Multiset.map_map, Function.comp_def]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

end MulAction
