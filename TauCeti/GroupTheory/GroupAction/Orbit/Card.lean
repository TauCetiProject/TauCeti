/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Multiset.MapFold
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The multiset of orbit sizes

For a group `G` acting on a finite type `X`, the multiset of the sizes of the orbits of `G` on
`X` is a basic invariant of the action. This file records two ways in which it is preserved: by a
change of the acting group that does not change the orbits, and by an equivariant bijection of
the underlying types. It also computes the natural cardinality of a cyclic orbit in terms of
`Function.minimalPeriod` and bounds the length of a list of group elements with distinct images of
a point by the size of the orbit of that point.

## Main results

* `MulAction.natCard_orbit_zpowers`: the `Subgroup.zpowers a`-orbit of `b` has natural cardinality
  `Function.minimalPeriod (a • ·) b` (with both sides `0` for an infinite orbit).
* `MulAction.orbitRel.Quotient.card_orbit_ne_zero`: an orbit in a finite action has nonzero
  natural cardinality.
* `MulAction.orbitRel.Quotient.card_filter_quotient_mk`: the fiber of the orbit quotient
  map has the cardinality of the corresponding orbit.
* `MulAction.inv_natCard_mul_sum_eq_sum_quotient`: for a function constant on orbits,
  `|G|⁻¹ ∑ₓ f x` is the sum over the orbits of `|G_x|⁻¹ f x`, each point weighted by the inverse
  order of its stabilizer.

* `Equiv.map_card_orbit_eq_of_image_orbit_eq`: a bijection carrying the orbits of one action onto
  the orbits of another preserves the multiset of orbit sizes.
* `Equiv.map_card_orbit_eq_of_map_smul`: an equivariant bijection preserves the multiset of orbit
  sizes.
* `TauCeti.map_card_orbit_eq_of_orbit_eq`: two actions on the same finite type with the same
  orbits have the same multiset of orbit sizes.
* `Subgroup.length_le_ncard_orbit`: a list of elements of a subgroup `K` with distinct images of `x`
  is no longer than the orbit of `x` under `K`, if that orbit is finite.
-/

public section

open MulAction

namespace MulAction

/-- The `Subgroup.zpowers a`-orbit of `b` has `Function.minimalPeriod (a • ·) b` points. If the
orbit is infinite, then both sides are `0`. -/
@[to_additive /-- The `AddSubgroup.zmultiples a`-orbit of `b` has
`Function.minimalPeriod (a +ᵥ ·) b` points. If the orbit is infinite, then both sides are `0`. -/]
theorem natCard_orbit_zpowers {G β : Type*} [Group G] [MulAction G β] (a : G) (b : β) :
    Nat.card (orbit (Subgroup.zpowers a) b) = Function.minimalPeriod (a • ·) b :=
  (Nat.card_congr (orbitZPowersEquiv a b)).trans (Nat.card_zmod _)

/-- **Weighting the points of a finite action by their stabilizers.** For a finite group `G`
acting on a finite type `X` and a function `f` constant on the orbits,
`|G|⁻¹ ∑ₓ f x = ∑_{orbits} |G_x|⁻¹ f x`, where the right side evaluates at one chosen point `x` of
each orbit. By orbit–stabilizer, an orbit has `|G| / |G_x|` points: averaging over `G` counts a
point with isotropy `G_x` with weight `|G_x|⁻¹`. -/
theorem inv_natCard_mul_sum_eq_sum_quotient {G X K : Type*} [Group G] [Finite G] [MulAction G X]
    [Fintype X] [Fintype (orbitRel.Quotient G X)] [DivisionRing K] [CharZero K] (f : X → K)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    (Nat.card G : K)⁻¹ * ∑ x, f x =
      ∑ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G ω.out) : K)⁻¹ * f ω.out := by
  classical
  rw [← (selfEquivSigmaOrbits G X).symm.sum_comp, Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  have hconst (y : orbit G ω.out) : f ((selfEquivSigmaOrbits G X).symm ⟨ω, y⟩) = f ω.out := by
    obtain ⟨_, g, rfl⟩ := y
    exact hf g _
  simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  -- By orbit–stabilizer, the orbit has `[G : G_x] = |G| / |G_x|` points.
  rw [← index_stabilizer, ← (stabilizer G ω.out).index_mul_card, Nat.cast_mul]
  have hI : ((stabilizer G ω.out).index : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  simp [mul_assoc, hI]

end MulAction

namespace MulAction.orbitRel.Quotient

/-- Every orbit in an action on a finite type has nonzero natural cardinality. -/
theorem card_orbit_ne_zero {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (O : orbitRel.Quotient G X) : Nat.card O.orbit ≠ 0 := by
  have : Nonempty O.orbit := O.nonempty_orbit.to_subtype
  exact Nat.card_pos.ne'

open Classical in
/-- The fiber of the orbit quotient map has the natural cardinality of that orbit. -/
theorem card_filter_quotient_mk {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (O : orbitRel.Quotient G X) :
    (Finset.univ.filter (fun x ↦ Quotient.mk (orbitRel G X) x = O)).card =
      Nat.card O.orbit := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp [orbitRel.Quotient.mem_orbit]

end MulAction.orbitRel.Quotient

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

namespace Subgroup

/-- The images of `x` under a list of elements of a subgroup `K` lie in the orbit of `x` under `K`,
so if that orbit is finite, a list with distinct images of `x` is no longer than it. -/
theorem length_le_ncard_orbit {G α : Type*} [Group G] [MulAction G α] {K : Subgroup G}
    {x : α} {R : List G} (hR : ∀ r ∈ R, r ∈ K) (hnodup : (R.map (· • x)).Nodup)
    (horbit : (orbit K x).Finite := by toFinite_tac) :
    R.length ≤ (orbit K x).ncard := by
  rw [← List.length_map (· • x)]
  refine hnodup.length_le_ncard horbit fun y hy ↦ ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
  exact mem_orbit_iff.2 ⟨⟨r, hR r hr⟩, rfl⟩

end Subgroup
