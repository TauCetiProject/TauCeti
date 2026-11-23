/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.SubgroupClassification
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Index
import TauCeti.Algebra.Group.Subgroup.Conjugates

/-!
# Unpointed three-point covers and conjugacy classes of subgroups

Forgetting the marked sheet of a connected triple forgets its fixed-sheet subgroup only up to
conjugacy. Consequently connected triple classes of nonzero degree `n` classify conjugation
orbits of index-`n` subgroups of the fundamental group of the thrice-punctured sphere.

We use the existing conjugation action on `Subgroup`, restricted to `Subgroup.ofIndex`, rather
than introducing another conjugacy predicate. The classification commutes with forgetting a
mark and, through monodromy, with forgetting the point of a connected cover. The topological
input is `ConnectedPointedCoverClass.forgetPoint_eq_iff_exists_range_eq_map_conj`, combined with
`ConnectedCoverClass.subgroupConjugacyEquiv`, transported to triples by monodromy.

The nonzero degree condition is essential: the trivial subgroup of this infinite fundamental
group has natural-number index zero, but there are no connected degree-zero triples.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.38.
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

namespace MarkedIsoClass

/-- Two marked triples have the same unmarked class exactly when their fixed-sheet subgroups
are conjugate. -/
theorem forget_eq_iff_exists_subgroup_eq_map_conj (c d : MarkedIsoClass n) :
    c.forget = d.forget ↔ ∃ γ : FundamentalGroup ThricePuncturedSphere basePt,
      d.subgroup = c.subgroup.map (MulAut.conj γ).toMonoidHom := by
  obtain ⟨a, i, rfl⟩ := c.exists_eq_mk_connectedTriple
  obtain ⟨b, j, rfl⟩ := d.exists_eq_mk_connectedTriple
  rw [ConnectedFiberNumberedCover.subgroup_mk_connectedTriple,
    ConnectedFiberNumberedCover.subgroup_mk_connectedTriple]
  refine Iff.trans ?_ (ConnectedPointedCoverClass.forgetPoint_eq_iff_exists_range_eq_map_conj
    (a.markLabel i) (b.markLabel j))
  rw [← ConnectedCoverClass.isoClass_injective.eq_iff]
  simp only [← ConnectedFiberNumberedCoverClass.markLabel_mk,
    ConnectedPointedCoverClass.isoClass_forgetPoint,
    ConnectedFiberNumberedCoverClass.markedClass_markLabel,
    ConnectedFiberNumberedCoverClass.triple_mk]

/-- Forgetting a marked sheet identifies precisely the conjugation orbits of its subgroup. -/
theorem forget_eq_iff_orbitRel_subgroup (c d : MarkedIsoClass n) :
    c.forget = d.forget ↔
      orbitRel (ConjAct (FundamentalGroup ThricePuncturedSphere basePt)) _
        c.subgroup d.subgroup := by
  rw [forget_eq_iff_exists_subgroup_eq_map_conj, orbitRel_conjAct_iff]

end MarkedIsoClass

namespace ConnectedIsoClass

variable [NeZero n]

/-- Connected degree-`n` triple classes classify conjugation orbits of index-`n` subgroups of
the fundamental group of the thrice-punctured sphere. -/
noncomputable def subgroupConjugacyEquiv :
    ConnectedIsoClass n ≃
      orbitRel.Quotient (ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
        (Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :=
  ConnectedCoverClass.isoClassEquiv.symm.trans ConnectedCoverClass.subgroupConjugacyEquiv

end ConnectedIsoClass

/-- Over the thrice-punctured sphere, the cover and triple classifications assign the same
conjugation orbit. -/
theorem ConnectedCoverClass.subgroupConjugacyEquiv_apply [NeZero n]
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    subgroupConjugacyEquiv C = ConnectedIsoClass.subgroupConjugacyEquiv C.isoClass := by
  rw [ConnectedIsoClass.subgroupConjugacyEquiv, Equiv.trans_apply,
    ← isoClassEquiv_apply, Equiv.symm_apply_apply]

namespace ConnectedIsoClass

variable [NeZero n]

/-- The unpointed classification is the pointed classification followed by passage to the
conjugation orbit of the subgroup. -/
@[simp]
theorem subgroupConjugacyEquiv_forget (c : MarkedIsoClass n) :
    subgroupConjugacyEquiv c.forget =
      Quotient.mk'' (⟨c.subgroup, Subgroup.mem_ofIndex.mpr c.index_subgroup⟩ :
        Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) := by
  obtain ⟨a, i, rfl⟩ := c.exists_eq_mk_connectedTriple
  let C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n := ⟨a.cover, ⟨a.ν⟩⟩
  rw [MarkedIsoClass.forget_mk, ← ConnectedCoverClass.isoClass_mk C a.ν,
    ← ConnectedCoverClass.subgroupConjugacyEquiv_apply,
    ConnectedCoverClass.subgroupConjugacyEquiv_mk C (a.ν.symm i)]
  exact congrArg Quotient.mk'' (Subtype.ext (a.subgroup_mk_connectedTriple i).symm)

/-- The unmarked triple class corresponding to a subgroup of index `n`. This forgets the mark
in the pointed subgroup classification. -/
noncomputable def ofSubgroup
    (H : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    ConnectedIsoClass n :=
  (MarkedIsoClass.subgroupEquiv.symm ⟨H.val, Subgroup.mem_ofIndex.mp H.property⟩).forget

/-- Construct the unmarked triple class by forgetting the mark in the pointed construction. -/
theorem ofSubgroup_def
    (H : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    ofSubgroup H =
      (MarkedIsoClass.subgroupEquiv.symm ⟨H.val, Subgroup.mem_ofIndex.mp H.property⟩).forget :=
  (rfl)

/-- Applying `ofSubgroup` to a marked triple's fixed-sheet subgroup recovers its unmarked class. -/
@[simp]
theorem ofSubgroup_subgroup (c : MarkedIsoClass n) :
    ofSubgroup ⟨c.subgroup, Subgroup.mem_ofIndex.mpr c.index_subgroup⟩ = c.forget := by
  rw [ofSubgroup_def]
  apply congrArg MarkedIsoClass.forget
  apply MarkedIsoClass.subgroup_injective
  simp

/-- Every connected triple class comes from a subgroup of index equal to its degree. -/
theorem ofSubgroup_surjective : Function.Surjective (ofSubgroup (n := n)) := by
  intro c
  obtain ⟨d, rfl⟩ := MarkedIsoClass.forget_surjective c
  exact ⟨⟨d.subgroup, Subgroup.mem_ofIndex.mpr d.index_subgroup⟩, ofSubgroup_subgroup d⟩

/-- The triple constructed from a subgroup is classified by that subgroup's orbit. -/
@[simp]
theorem subgroupConjugacyEquiv_ofSubgroup
    (H : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    subgroupConjugacyEquiv (ofSubgroup H) = Quotient.mk'' H := by
  rw [ofSubgroup_def, subgroupConjugacyEquiv_forget]
  exact congrArg Quotient.mk'' (Subtype.ext (MarkedIsoClass.subgroup_subgroupEquiv_symm _))

/-- The inverse classification constructs the unmarked triple of an orbit representative. -/
@[simp]
theorem subgroupConjugacyEquiv_symm_mk
    (H : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    subgroupConjugacyEquiv.symm (Quotient.mk'' H) = ofSubgroup H := by
  rw [← subgroupConjugacyEquiv_ofSubgroup H, Equiv.symm_apply_apply]

/-- Index-`n` subgroups give the same unmarked triple class exactly when they belong to one
conjugation orbit. -/
theorem ofSubgroup_eq_iff
    (H K : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    ofSubgroup H = ofSubgroup K ↔
      orbitRel (ConjAct (FundamentalGroup ThricePuncturedSphere basePt)) _ H K := by
  rw [← subgroupConjugacyEquiv.injective.eq_iff, subgroupConjugacyEquiv_ofSubgroup,
    subgroupConjugacyEquiv_ofSubgroup, Quotient.eq'']

/-- Conjugating the subgroup does not change its unmarked triple class. -/
@[simp]
theorem ofSubgroup_smul (g : ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
    (H : Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) :
    ofSubgroup (g • H) = ofSubgroup H :=
  (ofSubgroup_eq_iff _ _).2 ⟨g, rfl⟩

/-- The orbit assigned to a triple is represented by the stabilizer of any sheet. -/
theorem subgroupConjugacyEquiv_mk (t : ConnectedTriple n) (i : Fin n) :
    subgroupConjugacyEquiv (mk t) = Quotient.mk''
      (⟨(MarkedIsoClass.mk t i).subgroup,
        Subgroup.mem_ofIndex.mpr (MarkedIsoClass.mk t i).index_subgroup⟩ :
          Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n) := by
  rw [← MarkedIsoClass.forget_mk t i, subgroupConjugacyEquiv_forget]

end ConnectedIsoClass

namespace ConnectedCoverClass

/-- Forgetting the chosen fibre point takes the subgroup of the marked triple to its orbit. -/
@[simp]
theorem subgroupConjugacyEquiv_forgetPoint [NeZero n]
    (C : ConnectedPointedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    subgroupConjugacyEquiv C.forgetPoint =
      ConnectedIsoClass.subgroupConjugacyEquiv C.markedClass.forget := by
  rw [subgroupConjugacyEquiv_apply, ConnectedPointedCoverClass.isoClass_forgetPoint]

/-- Recover the triple class of the cover associated to a subgroup orbit. -/
@[simp]
theorem isoClass_subgroupConjugacyEquiv_symm [NeZero n]
    (H : orbitRel.Quotient (ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
      (Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n)) :
    (subgroupConjugacyEquiv.symm H).isoClass = ConnectedIsoClass.subgroupConjugacyEquiv.symm H := by
  apply ConnectedIsoClass.subgroupConjugacyEquiv.injective
  rw [← subgroupConjugacyEquiv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Over the thrice-punctured sphere, the inverse classification can be computed via triples. -/
theorem subgroupConjugacyEquiv_symm_apply [NeZero n]
    (H : orbitRel.Quotient (ConjAct (FundamentalGroup ThricePuncturedSphere basePt))
      (Subgroup.ofIndex (FundamentalGroup ThricePuncturedSphere basePt) n)) :
    subgroupConjugacyEquiv.symm H =
      isoClassEquiv.symm (ConnectedIsoClass.subgroupConjugacyEquiv.symm H) := by
  apply isoClass_injective
  rw [isoClass_subgroupConjugacyEquiv_symm, isoClass_isoClassEquiv_symm]

end ConnectedCoverClass

end TauCeti
