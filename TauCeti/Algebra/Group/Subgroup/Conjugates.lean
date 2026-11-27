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
import Mathlib.Order.Atoms
import TauCeti.Algebra.GroupAction.OrbitRelQuotient

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
* `MulEquiv.orbitRelQuotientSubgroupEquiv`: a group isomorphism identifies the conjugacy classes of
  subgroups.

## Main results

* `TauCeti.mem_orbit_conjAct_iff`: orbit membership is subgroup conjugation.
* `Subgroup.index_normalizer_eq_ncard_orbit`: the number of conjugates is the index of the
  normalizer.
* `Subgroup.ncard_orbit_mul_relIndex_normalizer`: multiplying the number of conjugates by
  `[N_G(H) : H]` gives `[G : H]`.
* `TauCeti.sum_subgroups_eq_sum_conjugacy`: group a conjugation-invariant sum by subgroup
  conjugacy classes.
* `Subgroup.exists_map_conj_comap_eq_iff`: the preimages of two subgroups under a group
  isomorphism are conjugate exactly when the subgroups are.
* `Subgroup.exists_map_conj_mem_of_forall_covBy`: descent through maximal subgroups. In a finite
  group, let `P` be a property of subgroups that is inherited by larger subgroups and by
  conjugates. If a family of subgroups contains `⊤` and contains a conjugate of every maximal
  subgroup with property `P` of each of its members, then it contains a conjugate of every
  subgroup with property `P`.
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
    (fun (H : {H : Subgroup G // Quotient.mk'' H = ω}) _ ↦ hvalue H.val H.property),
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
    ((conjugateSubgroupsEquiv e H) J).val = J.val.map (e : G →* G') := by
  -- The subtype equivalence applies `e.mapSubgroup`; its map is the underlying monoid hom.
  change e.mapSubgroup J.val = J.val.map e.toMonoidHom
  rfl

/-- The inverse equivalence maps a conjugate subgroup along the inverse isomorphism. -/
@[simp]
theorem conjugateSubgroupsEquiv_symm_apply {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G)
    (J : MulAction.orbit (ConjAct G') (H.map (e : G →* G'))) :
    (((conjugateSubgroupsEquiv e H).symm J).val) = J.val.map (e.symm : G' →* G) := by
  -- The inverse subtype equivalence applies `e.mapSubgroup.symm`.
  change e.mapSubgroup.symm J.val = J.val.map e.symm.toMonoidHom
  rfl

/-- A group isomorphism identifies the conjugacy classes of subgroups of `G` and `G'`. -/
def orbitRelQuotientSubgroupEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G) ≃
      MulAction.orbitRel.Quotient (ConjAct G') (Subgroup G') :=
  TauCeti.MulAction.orbitRelQuotientCongr (ConjAct.ofConjAct.trans (e.trans ConjAct.toConjAct))
    e.mapSubgroup.toEquiv fun g H ↦ Subgroup.map_map_conj H e.toMonoidHom (ConjAct.ofConjAct g)

/-- `e.orbitRelQuotientSubgroupEquiv` maps the conjugacy class of `H` to that of its image. -/
@[simp]
theorem orbitRelQuotientSubgroupEquiv_mk {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    e.orbitRelQuotientSubgroupEquiv (Quotient.mk'' H) = Quotient.mk'' (H.map (e : G →* G')) :=
  (TauCeti.MulAction.orbitRelQuotientCongr_mk _ _ _ H).trans <| congrArg Quotient.mk'' <| by simp

/-- `e.orbitRelQuotientSubgroupEquiv.symm` maps the conjugacy class of `H` to that of its image
under `e.symm`. -/
@[simp]
theorem orbitRelQuotientSubgroupEquiv_symm_mk {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G') :
    e.orbitRelQuotientSubgroupEquiv.symm (Quotient.mk'' H) =
      Quotient.mk'' (H.map (e.symm : G' →* G)) :=
  (TauCeti.MulAction.orbitRelQuotientCongr_symm_mk _ _ _ H).trans <| congrArg Quotient.mk'' <| by
    simp

end MulEquiv

namespace Subgroup

variable {G Γ : Type*} [Group G] [Group Γ]

/-- **Conjugacy of subgroups is pulled back along group isomorphisms.** For an isomorphism
`e : G ≃* Γ`, the preimages of two subgroups of `Γ` are conjugate in `G` exactly when the
subgroups themselves are conjugate in `Γ`. -/
theorem exists_map_conj_comap_eq_iff (e : G ≃* Γ) (H K : Subgroup Γ) :
    (∃ σ : G, (H.comap (e : G →* Γ)).map (MulAut.conj σ : G →* G) = K.comap (e : G →* Γ)) ↔
      ∃ τ : Γ, H.map (MulAut.conj τ : Γ →* Γ) = K := by
  have key (σ : G) : (H.comap (e : G →* Γ)).map (MulAut.conj σ : G →* G) =
      (H.map (MulAut.conj (e σ) : Γ →* Γ)).comap (e : G →* Γ) := by
    -- The commuting square of conjugation with `e.symm`, conjugating by `e.symm (e σ) = σ`.
    rw [comap_equiv_eq_map_symm, comap_equiv_eq_map_symm]
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply] using
      (map_map_conj H (e.symm : Γ →* G) (e σ)).symm
  have hinj : Function.Injective (comap (e : G →* Γ)) := comap_injective e.surjective
  refine ⟨fun ⟨σ, hσ⟩ ↦ ⟨e σ, hinj (by rwa [← key])⟩, fun ⟨τ, hτ⟩ ↦ ⟨e.symm τ, ?_⟩⟩
  rw [key, MulEquiv.apply_symm_apply, hτ]

/-- **Descent through maximal subgroups.** Let `P` be a property of subgroups of a finite group
`G` that passes to larger subgroups and to conjugates, and let `𝓡` be a family of subgroups
containing `⊤` such that every maximal subgroup `M` of a member of `𝓡` with `P M` is conjugate to a
member of `𝓡`. Then every subgroup with property `P` is conjugate to a member of `𝓡`.

Applied to the transitive subgroups of a finite symmetric group, this reduces the completeness of
a list of representatives of transitive groups up to conjugacy to a check on the transitive maximal
subgroups of its members. -/
theorem exists_map_conj_mem_of_forall_covBy [Finite G] {P : Subgroup G → Prop}
    (hP : ∀ ⦃H K : Subgroup G⦄, H ≤ K → P H → P K)
    (hPconj : ∀ (g : G) ⦃H : Subgroup G⦄, P H → P (H.map (MulAut.conj g).toMonoidHom))
    {𝓡 : Set (Subgroup G)} (htop : ⊤ ∈ 𝓡)
    (h𝓡 : ∀ R ∈ 𝓡, ∀ M : Subgroup G, M ⋖ R → P M →
      ∃ g : G, M.map (MulAut.conj g).toMonoidHom ∈ 𝓡)
    {H : Subgroup G} (hH : P H) : ∃ g : G, H.map (MulAut.conj g).toMonoidHom ∈ 𝓡 := by
  -- Strong induction on the order of a member `R` of `𝓡` containing a conjugate of `H`.
  suffices key : ∀ n, ∀ R ∈ 𝓡, Nat.card R = n → ∀ g : G,
      H.map (MulAut.conj g).toMonoidHom ≤ R → ∃ g : G, H.map (MulAut.conj g).toMonoidHom ∈ 𝓡 from
    key _ ⊤ htop rfl 1 le_top
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro R hR rfl g hle
    obtain heq | hlt := hle.eq_or_lt
    · exact ⟨g, heq ▸ hR⟩
    -- Otherwise the conjugate of `H` lies in a maximal subgroup `M` of `R`, which has property
    -- `P` and is conjugate to a member of `𝓡` of smaller order.
    obtain ⟨M, hHM, hMR⟩ := exists_le_covBy_of_lt hlt
    obtain ⟨h, hh⟩ := h𝓡 R hR M hMR (hP hHM (hPconj g hH))
    refine ih _ ?_ _ hh rfl (h * g) ?_
    · rw [card_map_of_injective (MulAut.conj h).injective]
      exact card_lt_of_lt hMR.lt
    · rw [← map_conj_map_conj]
      exact map_mono hHM

end Subgroup
