/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Classification
import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed

/-!
# Marked permutation triples and finite-index subgroups

A connected permutation triple with a marked sheet determines the subgroup of loops whose
monodromy fixes that sheet. Relabeling the triple and its marked sheet together does not change
the subgroup. Conversely, for nonzero `n`, every subgroup of index `n` is obtained this way,
and the marked isomorphism class is unique.

`MarkedIsoClass.subgroupEquiv` is this classification for nonzero `n`. The nonzero hypothesis
is necessary: the natural-number index of an infinite-index subgroup is zero, whereas there
are no connected triples on zero sheets. The subgroup map itself is defined for every degree.

The classification combines the marked monodromy classification with the existing pointed
cover classification by recovered subgroups. In particular, the inverse direction uses the
quotient of the universal cover by the prescribed subgroup.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.38.
-/

public section

open CategoryTheory Equiv MulAction FundamentalGroup

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

namespace MarkedIsoClass

/-- The subgroup of loops whose monodromy fixes the marked sheet. The representation is the
unique one taking the two peripheral generators to the first two permutations of the triple. -/
noncomputable def subgroup (c : MarkedIsoClass n) :
    Subgroup (FundamentalGroup ThricePuncturedSphere basePt) :=
  lift
    (fun t i => (stabilizer (Perm (Fin n)) i).comap
      (peripheralBasis.lift ![t.1.σ0, t.1.σ1]))
    (by
      intro τ t i
      have hρ : peripheralBasis.lift ![(τ • t).1.σ0, (τ • t).1.σ1] =
          (MulAut.conj τ).toMonoidHom.comp (peripheralBasis.lift ![t.1.σ0, t.1.σ1]) := by
        apply fundamentalGroup_hom_ext <;> simp
      ext γ
      simp only [Subgroup.mem_comap, mem_stabilizer_iff, Perm.smul_def]
      rw [hρ, MonoidHom.comp_apply]
      simp [MulAut.conj_apply, Perm.mul_apply]) c

/-- The subgroup of a representative consists of the loops fixing its marked label. -/
@[simp]
theorem subgroup_mk (t : ConnectedTriple n) (i : Fin n) :
    (mk t i).subgroup = (stabilizer (Perm (Fin n)) i).comap
      (peripheralBasis.lift ![t.1.σ0, t.1.σ1]) :=
  lift_mk _ _ t i

/-- Membership in the subgroup is the fixed-label equation in the peripheral representation. -/
theorem mem_subgroup_mk_iff (t : ConnectedTriple n) (i : Fin n)
    (γ : FundamentalGroup ThricePuncturedSphere basePt) :
    γ ∈ (mk t i).subgroup ↔ peripheralBasis.lift ![t.1.σ0, t.1.σ1] γ i = i := by
  simp [mem_stabilizer_iff, Perm.smul_def]

end MarkedIsoClass

namespace ConnectedFiberNumberedCover

/-- The subgroup of the marked monodromy triple is precisely the subgroup recovered from the
point of the cover carrying that label. -/
theorem subgroup_mk_connectedTriple (c : ConnectedFiberNumberedCover
    (X := TopCat.of ThricePuncturedSphere) basePt n) (i : Fin n) :
    (MarkedIsoClass.mk c.connectedTriple i).subgroup =
      (mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ (c.ν.symm i).2).range := by
  have hρ : peripheralBasis.lift ![c.connectedTriple.1.σ0, c.connectedTriple.1.σ1] =
      c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm basePt) := by
    apply fundamentalGroup_hom_ext <;>
      simp [coe_connectedTriple, IsCoveringMap.monodromyTriple_σ0,
        IsCoveringMap.monodromyTriple_σ1]
  rw [MarkedIsoClass.subgroup_mk, hρ,
    ← c.cover.isCoveringMap_proj.comap_stabilizer_monodromyPerm]
  ext γ
  simp [mem_stabilizer_iff, permCongr_apply, Equiv.eq_symm_apply]

end ConnectedFiberNumberedCover

namespace MarkedIsoClass

/-- Every marked class is represented by the monodromy triple of a numbered cover. -/
theorem exists_eq_mk_connectedTriple (c : MarkedIsoClass n) :
    ∃ (d : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n)
      (i : Fin n), mk d.connectedTriple i = c := by
  obtain ⟨t, i, rfl⟩ := mk_surjective c
  obtain ⟨C, hC⟩ := ConnectedFiberNumberedCoverClass.triple_surjective t
  obtain ⟨d, rfl⟩ := ConnectedFiberNumberedCoverClass.mk_surjective C
  rw [ConnectedFiberNumberedCoverClass.triple_mk] at hC
  exact ⟨d, i, congrArg (fun t ↦ mk t i) hC⟩

/-- The subgroup of a marked connected triple has index equal to its degree. -/
theorem index_subgroup (c : MarkedIsoClass n) : c.subgroup.index = n := by
  obtain ⟨d, i, rfl⟩ := c.exists_eq_mk_connectedTriple
  rw [ConnectedFiberNumberedCover.subgroup_mk_connectedTriple]
  rw [← d.cover.isCoveringMap_proj.card_fiber_eq_index (d.ν.symm i), Nat.card_congr d.ν,
    Nat.card_fin]

/-- A marked connected triple is determined up to marked relabeling by its subgroup. -/
theorem subgroup_injective : Function.Injective (subgroup : MarkedIsoClass n → _) := by
  intro c c' h
  obtain ⟨d, i, rfl⟩ := c.exists_eq_mk_connectedTriple
  obtain ⟨d', i', rfl⟩ := c'.exists_eq_mk_connectedTriple
  rw [ConnectedFiberNumberedCover.subgroup_mk_connectedTriple,
    ConnectedFiberNumberedCover.subgroup_mk_connectedTriple] at h
  have hpointed : ConnectedPointedCoverClass.mk (d.markLabel i) =
      ConnectedPointedCoverClass.mk (d'.markLabel i') :=
    -- `markLabel` exposes its cover and point, so the recovered-subgroup equality is `h`.
    ConnectedPointedCoverClass.mk_eq_mk_of_range_eq (d.markLabel i) (d'.markLabel i') h
  have hmarked := congrArg ConnectedPointedCoverClass.markedClass hpointed
  simpa only [← ConnectedFiberNumberedCoverClass.markLabel_mk,
    ConnectedFiberNumberedCoverClass.markedClass_markLabel,
    ConnectedFiberNumberedCoverClass.triple_mk] using hmarked

/-- Every subgroup of positive finite index is the subgroup of a marked connected triple. -/
theorem exists_subgroup_eq [NeZero n]
    (H : Subgroup (FundamentalGroup ThricePuncturedSphere basePt)) (hH : H.index = n) :
    ∃ c : MarkedIsoClass n, c.subgroup = H := by
  let p := UniversalCover.subgroupCover basePt H
  let e := UniversalCover.subgroupCoverBasepointFiber basePt H
  have hquot : Nat.card (UniversalCover.subgroupQuotientProj basePt H ⁻¹' {basePt}) = n := by
    calc
      _ = (mapOfEq
          ⟨UniversalCover.subgroupQuotientProj basePt H,
            UniversalCover.continuous_subgroupQuotientProj basePt H⟩
          (UniversalCover.subgroupQuotientProj_basepoint basePt H)).range.index :=
        (UniversalCover.isCoveringMap_subgroupQuotientProj basePt H).card_fiber_eq_index
          ⟨UniversalCover.SubgroupQuotient.basepoint basePt H,
            UniversalCover.subgroupQuotientProj_basepoint basePt H⟩
      _ = H.index := congrArg Subgroup.index
        (UniversalCover.range_mapOfEq_subgroupQuotientProj basePt H)
      _ = n := hH
  have hcard : Nat.card (⇑p.proj ⁻¹' {basePt}) = n :=
    (Nat.card_congr (UniversalCover.subgroupCoverFiberEquivSubgroupQuotient basePt H)).trans hquot
  have := Nat.finite_of_card_ne_zero (hcard.trans_ne (NeZero.ne n))
  let := Fintype.ofFinite (⇑p.proj ⁻¹' {basePt})
  let ν : ⇑p.proj ⁻¹' {basePt} ≃ Fin n :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans hcard)
  let d : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n := ⟨p, ν⟩
  refine ⟨mk d.connectedTriple (ν e), ?_⟩
  rw [ConnectedFiberNumberedCover.subgroup_mk_connectedTriple, ν.symm_apply_apply]
  apply (IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq p.isCoveringMap_proj
    (UniversalCover.isCoveringMap_subgroupQuotientProj basePt H) e.2
    (UniversalCover.subgroupQuotientProj_basepoint basePt H)).1
    ⟨UniversalCover.subgroupCoverTotalSpaceHomeomorph basePt H, ?_, ?_⟩ |>.trans
      (UniversalCover.range_mapOfEq_subgroupQuotientProj basePt H)
  · have he := congrArg Subtype.val
      (UniversalCover.subgroupCoverFiberEquivSubgroupQuotient_apply_basepoint basePt H)
    rw [UniversalCover.subgroupCoverFiberEquivSubgroupQuotient_apply_coe,
      UniversalCover.SubgroupQuotient.basepointFiber_coe] at he
    exact he
  · exact funext (UniversalCover.subgroupQuotientProj_subgroupCoverTotalSpaceHomeomorph basePt H)

/-- The subgroup map is a bijection onto the subgroups of index equal to the nonzero degree. -/
theorem subgroup_bijective [NeZero n] :
    Function.Bijective (fun c : MarkedIsoClass n =>
      (⟨c.subgroup, c.index_subgroup⟩ :
        {H : Subgroup (FundamentalGroup ThricePuncturedSphere basePt) // H.index = n})) := by
  refine ⟨fun _ _ h => subgroup_injective (congrArg Subtype.val h), ?_⟩
  rintro ⟨H, hH⟩
  obtain ⟨c, hc⟩ := exists_subgroup_eq H hH
  exact ⟨c, Subtype.ext hc⟩

/-- Marked connected triples of nonzero degree `n` classify the index-`n` subgroups of the
fundamental group of the thrice-punctured sphere. -/
noncomputable def subgroupEquiv [NeZero n] :
    MarkedIsoClass n ≃
      {H : Subgroup (FundamentalGroup ThricePuncturedSphere basePt) // H.index = n} :=
  Equiv.ofBijective (fun c => ⟨c.subgroup, c.index_subgroup⟩) subgroup_bijective

/-- The classification sends a marked class to its fixed-sheet subgroup. -/
@[simp]
theorem coe_subgroupEquiv_apply [NeZero n] (c : MarkedIsoClass n) :
    (subgroupEquiv c).1 = c.subgroup :=
  (rfl)

/-- The marked class assigned to an index-`n` subgroup recovers that subgroup. -/
@[simp]
theorem subgroup_subgroupEquiv_symm [NeZero n]
    (H : {H : Subgroup (FundamentalGroup ThricePuncturedSphere basePt) // H.index = n}) :
    (subgroupEquiv.symm H).subgroup = H.1 :=
  congrArg Subtype.val (subgroupEquiv.apply_symm_apply H)

end MarkedIsoClass

end TauCeti
