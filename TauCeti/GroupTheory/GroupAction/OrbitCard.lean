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
  have key : ∀ x y : X, orbitRel G X x y ↔ orbitRel G' X x y := fun x y => by
    rw [orbitRel_apply, orbitRel_apply, h]
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ Finset.univ.nodup Finset.univ.nodup
    (fun ω _ => Quotient.mk'' ω.out) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro ω _ ω' _ hω
    rw [Quotient.eq''] at hω
    exact Quotient.out_equiv_out.mp ((key _ _).mpr hω)
  · intro ω' _
    refine ⟨Quotient.mk'' ω'.out, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [← Quotient.out_eq' ω']
    rw [Quotient.eq'']
    exact (key _ _).mp (Quotient.mk_out' ω'.out)
  · intro ω _
    rw [orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq', orbitRel.Quotient.orbit_mk, h]

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
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ Finset.univ.nodup Finset.univ.nodup
    (fun ω _ => Quotient.mk'' (e ω.out)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro ω _ ω' _ hω
    rw [Quotient.eq''] at hω
    exact Quotient.out_equiv_out.mp ((key _ _).mpr hω)
  · intro ω' _
    refine ⟨Quotient.mk'' (e.symm ω'.out), Finset.mem_univ _, ?_⟩
    conv_rhs => rw [← Quotient.out_eq' ω']
    rw [Quotient.eq'']
    have := (key _ _).mp (Quotient.mk_out' (e.symm ω'.out))
    rwa [e.apply_symm_apply] at this
  · intro ω _
    rw [orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq', orbitRel.Quotient.orbit_mk,
      ← himage, Nat.card_image_of_injective e.injective]

end MulAction
