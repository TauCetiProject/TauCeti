/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Conjugate subgroups

This file characterizes membership in the orbit of a subgroup under conjugation and transports
that orbit across a group isomorphism. A conjugate of `H ≤ G` is the image of `H` under
`MulAut.conj g` for some `g : G`. The number of conjugates is the normalizer index. Consequently,
a conjugation-invariant sum over subgroups can be grouped by their conjugacy classes with
that multiplicity.

## Main definitions

* `MulEquiv.conjugateSubgroupsEquiv`: a group isomorphism identifies the conjugates of
  corresponding subgroups.

## Main results

* `TauCeti.mem_orbit_conjAct_iff`: orbit membership is subgroup conjugation.
* `Subgroup.index_normalizer_eq_ncard_orbit`: the number of conjugates is the index of the
  normalizer.
* `Subgroup.ncard_orbit_mul_relIndex_normalizer`: multiplying the number of conjugates by
  `[N_G(H) : H]` gives `[G : H]`.
* `TauCeti.sum_subgroups_eq_sum_conjugacy`: group a conjugation-invariant sum by subgroup
  conjugacy classes.
-/

public section

namespace TauCeti

open scoped Pointwise

/-- Membership in the conjugacy orbit of `H` means being obtained from `H` by conjugation. -/
@[simp]
theorem mem_orbit_conjAct_iff {G : Type*} [Group G] {H H' : Subgroup G} :
    H' ∈ MulAction.orbit (ConjAct G) H ↔ ∃ g : G, H.map (MulAut.conj g) = H' := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.toConjAct g, rfl⟩

end TauCeti

open scoped Pointwise

namespace Subgroup

/-- The number of conjugates of a subgroup is the index of its normalizer. -/
theorem index_normalizer_eq_ncard_orbit {G : Type*} [Group G] (H : Subgroup G) :
    (normalizer (H : Set G)).index = (MulAction.orbit (ConjAct G) H).ncard := by
  have hstab : normalizer (H : Set G) =
      (MulAction.stabilizer (ConjAct G) H).comap ConjAct.toConjAct.toMonoidHom := by
    ext g
    exact conjAct_pointwise_smul_iff.symm
  calc
    (normalizer (H : Set G)).index = (MulAction.stabilizer (ConjAct G) H).index :=
      (congrArg Subgroup.index hstab).trans
        ((MulAction.stabilizer (ConjAct G) H).index_comap_of_surjective
          ConjAct.toConjAct.surjective)
    _ = _ := MulAction.index_stabilizer (ConjAct G) H

/-- The number of conjugates of `H` times `[N_G(H) : H]` is `[G : H]`. -/
theorem ncard_orbit_mul_relIndex_normalizer {G : Type*} [Group G] (H : Subgroup G) :
    (MulAction.orbit (ConjAct G) H).ncard * H.relIndex (normalizer (H : Set G)) = H.index := by
  rw [← H.index_normalizer_eq_ncard_orbit, mul_comm]
  exact relIndex_mul_index le_normalizer

end Subgroup

namespace TauCeti

open scoped Classical in
/-- A conjugation-invariant sum over subgroups can be grouped by conjugacy classes, weighted
by the normalizer index of each representative. -/
theorem sum_subgroups_eq_sum_conjugacy {G M : Type*} [Group G] [Fintype G]
    [AddCommMonoid M] (f : Subgroup G → M)
    (hf : ∀ (g : G) (H : Subgroup G), f (H.map (MulAut.conj g)) = f H) :
    ∑ H : Subgroup G, f H =
      ∑ ω : MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G),
        (Subgroup.normalizer (ω.out : Set G)).index • f ω.out := by
  classical
  rw [← Fintype.sum_fiberwise
    (Quotient.mk'' : Subgroup G → MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G))]
  apply Finset.sum_congr rfl
  intro ω _
  have hvalue (H : Subgroup G) (hH : Quotient.mk'' H = ω) : f H = f ω.out := by
    have hmem : H ∈ MulAction.orbit (ConjAct G) ω.out := by
      rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
      exact MulAction.orbitRel.Quotient.mem_orbit.mpr hH
    obtain ⟨g, rfl⟩ := mem_orbit_conjAct_iff.mp hmem
    exact hf g ω.out
  have hcard : Nat.card {H : Subgroup G // Quotient.mk'' H = ω} =
      (Subgroup.normalizer (ω.out : Set G)).index := by
    rw [Subgroup.index_normalizer_eq_ncard_orbit, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun H ↦ by
      rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
      exact MulAction.orbitRel.Quotient.mem_orbit.symm)
  rw [Finset.sum_congr rfl
    (fun (H : {H : Subgroup G // Quotient.mk'' H = ω}) _ ↦ hvalue H.1 H.2),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]

end TauCeti

namespace MulEquiv

/-- A group isomorphism identifies the sets of conjugates of corresponding subgroups. -/
def conjugateSubgroupsEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) :
    MulAction.orbit (ConjAct G) H ≃
      MulAction.orbit (ConjAct G') (H.map (e : G →* G')) :=
  e.mapSubgroup.subtypeEquiv fun J ↦ by
    constructor
    · intro h
      obtain ⟨g, hg⟩ := TauCeti.mem_orbit_conjAct_iff.mp h
      apply TauCeti.mem_orbit_conjAct_iff.mpr
      refine ⟨e g, ?_⟩
      -- `Subgroup.map` sees the monoid homomorphism underlying `MulAut.conj`.
      change H.map (MulAut.conj g).toMonoidHom = J at hg
      change (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom = J.map e.toMonoidHom
      have hmap : (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom =
          (H.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
        simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using
          (Subgroup.map_map_conj H e.toMonoidHom g).symm
      exact hmap.trans (congrArg (·.map e.toMonoidHom) hg)
    · intro h
      obtain ⟨g, hg⟩ := TauCeti.mem_orbit_conjAct_iff.mp h
      apply TauCeti.mem_orbit_conjAct_iff.mpr
      refine ⟨e.symm g, ?_⟩
      apply e.mapSubgroup.injective
      -- Expose the underlying homomorphisms to apply `Subgroup.map_map_conj`.
      change (H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
        J.map e.toMonoidHom
      change (H.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = J.map e.toMonoidHom at hg
      have heg : e.toMonoidHom (e.symm g) = g := e.apply_symm_apply g
      have hmap : (H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
          (H.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        simpa only [heg] using Subgroup.map_map_conj H e.toMonoidHom (e.symm g)
      exact hmap.trans hg

/-- On conjugate subgroups the equivalence maps each subgroup along the given isomorphism. -/
@[simp]
theorem conjugateSubgroupsEquiv_apply {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (J : MulAction.orbit (ConjAct G) H) :
    ((conjugateSubgroupsEquiv e H) J).1 = J.1.map (e : G →* G') := by
  -- The subtype equivalence applies `e.mapSubgroup`; its map is the underlying monoid hom.
  change e.mapSubgroup J.1 = J.1.map e.toMonoidHom
  rfl

/-- The inverse equivalence maps a conjugate subgroup along the inverse isomorphism. -/
@[simp]
theorem conjugateSubgroupsEquiv_symm_apply {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G)
    (J : MulAction.orbit (ConjAct G') (H.map (e : G →* G'))) :
    (((conjugateSubgroupsEquiv e H).symm J).1) = J.1.map (e.symm : G' →* G) := by
  -- The inverse subtype equivalence applies `e.mapSubgroup.symm`.
  change e.mapSubgroup.symm J.1 = J.1.map e.symm.toMonoidHom
  rfl

end MulEquiv
