/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import TauCeti.GroupTheory.Commutator

/-!
# The upper central series step above a normal subgroup

For a normal subgroup `N` of `G`, Mathlib's `Subgroup.upperCentralSeriesStep N` is the preimage of
the centre of `G ⧸ N`.  This file records three facts about it that are used to find abelian normal
subgroups of a nilpotent group modulo a normal subgroup, without passing to the quotient.

* It is again normal (`Subgroup.normal_upperCentralSeriesStep`), so the step can be
  iterated. Mathlib only registers this for characteristic `N`.
* In a nilpotent group it is strictly larger than `N` unless `N = ⊤`
  (`TauCeti.lt_upperCentralSeriesStep`): the centre of a nontrivial nilpotent group is
  nontrivial, read in `G ⧸ N`.
* If `x` lies two steps above `N`, the normal closure of `x` is abelian modulo `N`
  (`TauCeti.commutator_normalClosure_singleton_le`): its generators are the conjugates of `x`,
  and modulo `N` each of them is `x` times a central element.

The last two together produce, in a nilpotent group whose quotient `G ⧸ N` is not abelian, a
normal subgroup that is abelian modulo `N` but not central modulo `N`.  This is the group theory
behind the theorem that the irreducible characters of a finite nilpotent group are induced from
linear characters.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §8.5.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The upper central series step above a normal subgroup is normal: it is the preimage of the
centre of the quotient. -/
instance normal_upperCentralSeriesStep (N : Subgroup G) [N.Normal] :
    (upperCentralSeriesStep N).Normal := by
  rw [upperCentralSeriesStep_eq_comap_center]
  infer_instance

end Subgroup

namespace TauCeti

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **In a nilpotent group, the upper central series step strictly enlarges every proper normal
subgroup.**  The quotient `G ⧸ N` is a nontrivial nilpotent group, so its centre is nontrivial. -/
theorem lt_upperCentralSeriesStep [Group.IsNilpotent G] {N : Subgroup G} [N.Normal]
    (hN_ne : N ≠ ⊤) : N < Subgroup.upperCentralSeriesStep N := by
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hN_ne
  have h := (Subgroup.comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective N)).mpr
    (bot_lt_iff_ne_bot.mpr (Group.IsNilpotent.center_ne_bot (G ⧸ N)))
  simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk',
    ← Subgroup.upperCentralSeriesStep_eq_comap_center] using h

/-- **The normal closure of an element two steps above `N` is abelian modulo `N`.**  If `x` is
central modulo `upperCentralSeriesStep N`, then any two conjugates of `x` commute modulo `N`, so
the commutator subgroup of the normal closure of `x` lies in `N`. -/
theorem commutator_normalClosure_singleton_le {N : Subgroup G} [N.Normal] {x : G}
    (hx : x ∈ Subgroup.upperCentralSeriesStep (Subgroup.upperCentralSeriesStep N)) :
    ⁅Subgroup.normalClosure {x}, Subgroup.normalClosure {x}⁆ ≤ N := by
  have hnorm : Subgroup.closure (Group.conjugatesOfSet {x}) ≤
      Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  refine commutator_closure_closure_le hnorm hnorm ?_
  rintro _ ha _ hb
  obtain ⟨_, hxa, hya⟩ := Group.mem_conjugatesOfSet_iff.mp ha
  obtain ⟨_, hxb, hzb⟩ := Group.mem_conjugatesOfSet_iff.mp hb
  obtain ⟨y, rfl⟩ := isConj_iff.mp (Set.mem_singleton_iff.mp hxa ▸ hya)
  obtain ⟨z, rfl⟩ := isConj_iff.mp (Set.mem_singleton_iff.mp hxb ▸ hzb)
  -- Modulo `N`, the conjugate `y * x * y⁻¹ = ⁅y, x⁆ * x` is `x` times a central element.
  have hcentral (c : G) (hc : c ∈ Subgroup.upperCentralSeriesStep N) (g : G) :
      Commute (c : G ⧸ N) (g : G ⧸ N) :=
    QuotientGroup.commute_mk_iff.mpr (hc g)
  have hconj (y : G) : y * x * y⁻¹ = ⁅y, x⁆ * x := by group
  have hmem (y : G) : ⁅y, x⁆ ∈ Subgroup.upperCentralSeriesStep N := by
    rw [← commutatorElement_inv]
    exact inv_mem (hx y)
  rw [← QuotientGroup.commute_mk_iff, hconj, hconj, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
  exact (hcentral _ (hmem y) _).mul_left
    ((hcentral _ (hmem z) x).symm.mul_right (Commute.refl _))

end TauCeti
