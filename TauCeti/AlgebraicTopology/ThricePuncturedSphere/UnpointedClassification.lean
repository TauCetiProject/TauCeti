/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.SubgroupClassification
import TauCeti.AlgebraicTopology.UniversalCover.Classification.Unpointed
public import TauCeti.Algebra.GroupAction.CosetRepresentation

/-!
# Unpointed three-point covers and conjugacy classes of subgroups

Forgetting the marked sheet of a connected triple forgets its fixed-sheet subgroup only up to
conjugacy. Consequently connected triple classes of nonzero degree `n` classify conjugation
orbits of index-`n` subgroups of the fundamental group of the thrice-punctured sphere.

We use the existing conjugation action on `Subgroup`, restricted to `Subgroup.ofIndex`, rather
than introducing another conjugacy predicate. The classification commutes with forgetting a
mark and, through monodromy, with forgetting the point of a connected cover. The topological
input is `IsCoveringMap.exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj`, combined with
`MarkedIsoClass.subgroupEquiv`; no covering space is reconstructed here.

The nonzero degree condition is essential: the trivial subgroup of this infinite fundamental
group has natural-number index zero, but there are no connected degree-zero triples.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.38.
-/

public section

open CategoryTheory Equiv MulAction FundamentalGroup
open scoped Pointwise

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

namespace MarkedIsoClass

/-- Two marked triples have the same unmarked class exactly when their fixed-sheet subgroups
are conjugate. The conjugator need not preserve either marked sheet. -/
theorem forget_eq_iff_exists_subgroup_eq_map_conj (c d : MarkedIsoClass n) :
    c.forget = d.forget ↔ ∃ γ : FundamentalGroup ThricePuncturedSphere basePt,
      d.subgroup = c.subgroup.map (MulAut.conj γ).toMonoidHom := by
  obtain ⟨a, i, rfl⟩ := c.exists_eq_mk_connectedTriple
  obtain ⟨b, j, rfl⟩ := d.exists_eq_mk_connectedTriple
  rw [ConnectedFiberNumberedCover.subgroup_mk_connectedTriple,
    ConnectedFiberNumberedCover.subgroup_mk_connectedTriple]
  have heq : (mk a.connectedTriple i).forget = (mk b.connectedTriple j).forget ↔
      ConnectedCoverClass.mk a.forgetNumbering = ConnectedCoverClass.mk b.forgetNumbering := by
    rw [← ConnectedCoverClass.isoClass_injective.eq_iff]
    simp only [← ConnectedFiberNumberedCoverClass.forgetNumbering_mk,
      ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering,
      ConnectedFiberNumberedCoverClass.triple_mk, forget_mk]
  rw [heq, ConnectedCoverClass.mk_eq_mk_iff,
    ConnectedFiberNumberedCover.forgetNumbering_cover,
    ConnectedFiberNumberedCover.forgetNumbering_cover]
  rw [← IsCoveringMap.exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj
    a.cover.isCoveringMap_proj b.cover.isCoveringMap_proj (a.ν.symm i).2 (b.ν.symm j).2]
  constructor
  · rintro ⟨f⟩
    refine ⟨TopCat.homeoOfIso ((CoveringSpace.FullSubcategory.totalSpace _ _).mapIso f), ?_⟩
    funext e
    exact ConcreteCategory.congr_hom (CoveringSpace.FullSubcategory.w f.hom) e
  · rintro ⟨f, hf⟩
    exact ⟨CoveringSpace.FullSubcategory.isoMk (TopCat.isoOfHomeo f)
      (by ext e : 1; exact congrFun hf e)⟩

/-- Forgetting a marked sheet identifies precisely the conjugation orbits of its subgroup. -/
theorem forget_eq_iff_subgroup_orbitRel (c d : MarkedIsoClass n) :
    c.forget = d.forget ↔
      orbitRel (ConjAct (FundamentalGroup ThricePuncturedSphere basePt)) _
        c.subgroup d.subgroup := by
  rw [eq_comm, forget_eq_iff_exists_subgroup_eq_map_conj, orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨ConjAct.toConjAct γ, hγ.symm⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨ConjAct.ofConjAct γ, hγ.symm⟩

end MarkedIsoClass

namespace ConnectedIsoClass

variable [NeZero n]

/-- The unmarked triple class corresponding to a subgroup of index `n`. This forgets the mark
in the pointed subgroup classification. -/
noncomputable def ofSubgroup
    (H : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    ConnectedIsoClass n :=
  (MarkedIsoClass.subgroupEquiv.symm ⟨H.1, Subgroup.mem_ofIndex.mp H.2⟩).forget

/-- Applying the subgroup construction after forgetting the marked sheet recovers the
unmarked class. -/
@[simp]
theorem ofSubgroup_subgroup (c : MarkedIsoClass n) :
    ofSubgroup ⟨c.subgroup, Subgroup.mem_ofIndex.mpr c.index_subgroup⟩ = c.forget := by
  unfold ofSubgroup
  apply congrArg MarkedIsoClass.forget
  apply MarkedIsoClass.subgroup_injective
  simp

/-- Every connected triple class comes from a subgroup of index equal to its degree. -/
theorem ofSubgroup_surjective : Function.Surjective (ofSubgroup (n := n)) := by
  intro c
  obtain ⟨d, rfl⟩ := MarkedIsoClass.forget_surjective c
  exact ⟨⟨d.subgroup, Subgroup.mem_ofIndex.mpr d.index_subgroup⟩, ofSubgroup_subgroup d⟩

/-- Index-`n` subgroups give the same unmarked triple class exactly when they belong to one
conjugation orbit. -/
theorem ofSubgroup_eq_iff
    (H K : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    ofSubgroup H = ofSubgroup K ↔
      orbitRel (ConjAct (FundamentalGroup ThricePuncturedSphere basePt)) _ H K := by
  rw [ofSubgroup, ofSubgroup, MarkedIsoClass.forget_eq_iff_subgroup_orbitRel,
    MarkedIsoClass.subgroup_subgroupEquiv_symm,
    MarkedIsoClass.subgroup_subgroupEquiv_symm]
  simp only [orbitRel_apply, mem_orbit_iff]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, Subtype.ext hg⟩,
    fun ⟨g, hg⟩ => ⟨g, congrArg Subtype.val hg⟩⟩

/-- Construct a connected triple class from a conjugation orbit of index-`n` subgroups. -/
noncomputable def ofSubgroupConjugacyClass :
    orbitRel.Quotient (ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
      (Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) →
        ConnectedIsoClass n :=
  Quotient.lift ofSubgroup fun H K h => (ofSubgroup_eq_iff H K).2 h

/-- The class constructed from a subgroup orbit is the unmarked class of that subgroup. -/
@[simp]
theorem ofSubgroupConjugacyClass_mk
    (H : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    ofSubgroupConjugacyClass (Quotient.mk'' H) = ofSubgroup H :=
  (rfl)

/-- Conjugacy classes of index-`n` subgroups classify connected triple classes. -/
theorem ofSubgroupConjugacyClass_bijective :
    Function.Bijective (ofSubgroupConjugacyClass (n := n)) := by
  refine ⟨?_, ?_⟩
  · intro H K
    induction H using Quotient.inductionOn' with | h H =>
    induction K using Quotient.inductionOn' with | h K =>
    intro h
    exact Quotient.sound ((ofSubgroup_eq_iff H K).1 h)
  · intro c
    obtain ⟨H, rfl⟩ := ofSubgroup_surjective c
    exact ⟨Quotient.mk'' H, ofSubgroupConjugacyClass_mk H⟩

/-- Connected degree-`n` triple classes classify conjugation orbits of index-`n` subgroups of
the fundamental group of the thrice-punctured sphere. -/
noncomputable def subgroupConjugacyEquiv :
    ConnectedIsoClass n ≃
      orbitRel.Quotient (ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
        (Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :=
  (Equiv.ofBijective ofSubgroupConjugacyClass ofSubgroupConjugacyClass_bijective).symm

/-- The inverse classification constructs the triple of the subgroup orbit. -/
@[simp]
theorem subgroupConjugacyEquiv_symm_apply
    (H : orbitRel.Quotient (ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
      (Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n)) :
    subgroupConjugacyEquiv.symm H = ofSubgroupConjugacyClass H :=
  (rfl)

/-- The unpointed classification is the pointed classification followed by passage to the
conjugation orbit of the subgroup. -/
@[simp]
theorem subgroupConjugacyEquiv_forget (c : MarkedIsoClass n) :
    subgroupConjugacyEquiv c.forget =
      Quotient.mk'' (⟨c.subgroup, Subgroup.mem_ofIndex.mpr c.index_subgroup⟩ :
        Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) := by
  apply subgroupConjugacyEquiv.symm.injective
  simp

end ConnectedIsoClass

namespace ConnectedCoverClass

/-- Connected degree-`n` covers of the thrice-punctured sphere, up to isomorphism over the
base, classify conjugation orbits of index-`n` subgroups. -/
noncomputable def subgroupConjugacyEquiv [NeZero n] :
    ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n ≃
      orbitRel.Quotient (ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
        (Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :=
  isoClassEquiv.trans ConnectedIsoClass.subgroupConjugacyEquiv

/-- The cover and triple classifications assign the same conjugation orbit. -/
@[simp]
theorem subgroupConjugacyEquiv_apply [NeZero n]
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    subgroupConjugacyEquiv C = ConnectedIsoClass.subgroupConjugacyEquiv C.isoClass := by
  simp [subgroupConjugacyEquiv]

end ConnectedCoverClass

end TauCeti
