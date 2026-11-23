/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.NumberedFiber
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.Algebra.GroupAction.CosetRepresentation
import TauCeti.Algebra.Group.Subgroup.Conjugates
import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
import TauCeti.AlgebraicTopology.UniversalCover.Classification.Unpointed

/-!
# Connected covers of fixed positive degree

Forgetting a fibre point of a connected cover passes from the recovered subgroup to its
conjugation orbit. This gives `TauCeti.ConnectedCoverClass.subgroupConjugacyEquiv` at fixed
positive degree, using `IsCoveringMap.card_fiber_eq_index` to restrict the usual covering-space
correspondence to subgroups of the specified index. The base need not be path connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.38.
-/

public section

open CategoryTheory FundamentalGroup MulAction
open scoped Pointwise

universe u

namespace TauCeti

variable {X : TopCat.{u}} {x : X} {n : ℕ}

/-- The subgroup recovered using any point over `x` has index equal to the degree. -/
theorem ConnectedCover.index_range_mapOfEq (c : ConnectedCover x n)
    [PathConnectedSpace (c.cover : TopCat)] (e : ⇑c.cover.proj ⁻¹' {x}) :
    (mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ e.property).range.index = n := by
  rw [← c.cover.isCoveringMap_proj.card_fiber_eq_index e]
  exact Nat.card_eq_of_equiv_fin c.nonempty_equiv_fin.some

variable [LocallyPathConnectedSpace X]

/-- Two pointed covers become equal as unpointed classes exactly when the recovered subgroups
are conjugate. -/
theorem ConnectedPointedCoverClass.forgetPoint_eq_iff_exists_range_eq_map_conj
    (c d : ConnectedPointedCover x n) :
    (mk c).forgetPoint = (mk d).forgetPoint ↔ ∃ γ : FundamentalGroup X x,
      (mapOfEq ⟨d.cover.proj, d.cover.isCoveringMap_proj.continuous⟩ d.e.property).range =
        (mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ c.e.property).range.map
          (MulAut.conj γ).toMonoidHom := by
  rw [forgetPoint_mk, forgetPoint_mk, ConnectedCoverClass.mk_eq_mk_iff,
    ConnectedPointedCover.forgetPoint_cover, ConnectedPointedCover.forgetPoint_cover,
    CoveringSpace.FullSubcategory.isIsomorphic_iff_exists_homeomorph]
  exact IsCoveringMap.exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj
    c.cover.isCoveringMap_proj d.cover.isCoveringMap_proj c.e.property d.e.property

namespace ConnectedCoverClass

private noncomputable def subgroupAt (c : ConnectedCover x n) (e : ⇑c.cover.proj ⁻¹' {x}) :
    Subgroup.ofIndex (FundamentalGroup X x) n :=
  ⟨(mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ e.property).range,
    Subgroup.mem_ofIndex.mpr (c.index_range_mapOfEq e)⟩

private theorem mk_eq_mk_iff_orbitRel (c d : ConnectedCover x n)
    (e : ⇑c.cover.proj ⁻¹' {x}) (f : ⇑d.cover.proj ⁻¹' {x}) :
    mk c = mk d ↔ orbitRel (ConjAct (FundamentalGroup X x)) (Subgroup.ofIndex _ n)
      (subgroupAt c e) (subgroupAt d f) := by
  let c' : ConnectedPointedCover x n := ⟨c.cover, e, c.nonempty_equiv_fin⟩
  let d' : ConnectedPointedCover x n := ⟨d.cover, f, d.nonempty_equiv_fin⟩
  have hc : c'.forgetPoint = c := ConnectedCover.ext c'.forgetPoint_cover
  have hd : d'.forgetPoint = d := ConnectedCover.ext d'.forgetPoint_cover
  rw [SubMulAction.orbitRel_of_subMul, Setoid.comap_rel, orbitRel_conjAct_iff]
  have h := ConnectedPointedCoverClass.forgetPoint_eq_iff_exists_range_eq_map_conj c' d'
  rw [ConnectedPointedCoverClass.forgetPoint_mk, ConnectedPointedCoverClass.forgetPoint_mk,
    hc, hd] at h
  simpa only [subgroupAt, c', d'] using h

variable [SemilocallySimplyConnectedSpace X] [NeZero n]

open UniversalCover in
private noncomputable def coverOfSubgroup (H : Subgroup.ofIndex (FundamentalGroup X x) n) :
    ConnectedCover x n where
  cover := subgroupCover x H.val
  nonempty_equiv_fin := by
    have hcard := (natCard_fiber_subgroupCover x H.val).trans (Subgroup.mem_ofIndex.mp H.property)
    exact ⟨(Nat.equivFinOfCardPos (hcard.trans_ne (NeZero.ne n))).trans (finCongr hcard)⟩

private theorem subgroupAt_coverOfSubgroup (H : Subgroup.ofIndex (FundamentalGroup X x) n) :
    subgroupAt (coverOfSubgroup H) (UniversalCover.subgroupCoverBasepointFiber x H.val) = H :=
  Subtype.ext (UniversalCover.range_mapOfEq_subgroupCover x H.val)

/-- The connected cover class of the quotient of the universal cover by an index-`n` subgroup. -/
noncomputable def ofSubgroup (H : Subgroup.ofIndex (FundamentalGroup X x) n) :
    ConnectedCoverClass x n :=
  mk (coverOfSubgroup H)

/-- Any representative built from the subgroup cover gives the class of that subgroup. -/
theorem ofSubgroup_eq_mk (H : Subgroup.ofIndex (FundamentalGroup X x) n)
    (c : ConnectedCover x n) (hc : c.cover = UniversalCover.subgroupCover x H.val) :
    ofSubgroup H = mk c := by
  rw [ofSubgroup]
  exact congrArg mk (ConnectedCover.ext hc.symm)

open UniversalCover in
private theorem ofSubgroup_eq_mk_iff (H : Subgroup.ofIndex (FundamentalGroup X x) n)
    (c : ConnectedCover x n) (e : ⇑c.cover.proj ⁻¹' {x}) :
    ofSubgroup H = mk c ↔
      orbitRel (ConjAct (FundamentalGroup X x)) (Subgroup.ofIndex _ n) H (subgroupAt c e) := by
  rw [ofSubgroup, mk_eq_mk_iff_orbitRel (coverOfSubgroup H) c
    (subgroupCoverBasepointFiber x H.val) e, subgroupAt_coverOfSubgroup]

private theorem ofSubgroup_eq_iff (H K : Subgroup.ofIndex (FundamentalGroup X x) n) :
    ofSubgroup H = ofSubgroup K ↔
      orbitRel (ConjAct (FundamentalGroup X x)) (Subgroup.ofIndex _ n) H K := by
  rw [ofSubgroup_eq_mk K (coverOfSubgroup K) rfl,
    ofSubgroup_eq_mk_iff H (coverOfSubgroup K) (UniversalCover.subgroupCoverBasepointFiber x K.val),
    subgroupAt_coverOfSubgroup]

/-- Connected cover classes of positive degree are in bijection with conjugation orbits of
subgroups of the corresponding index. -/
noncomputable def subgroupConjugacyEquiv : ConnectedCoverClass x n ≃
    orbitRel.Quotient (ConjAct (FundamentalGroup X x))
      (Subgroup.ofIndex (FundamentalGroup X x) n) :=
  (Equiv.ofBijective (Quotient.lift ofSubgroup (fun H K => (ofSubgroup_eq_iff H K).2))
    ⟨(Setoid.lift_injective_iff_ker_eq_of_le _).2 (Setoid.ext ofSubgroup_eq_iff),
      Quotient.lift_surjective _ _ (by
        intro C
        obtain ⟨c, rfl⟩ := mk_surjective C
        obtain ⟨ν⟩ := c.nonempty_equiv_fin
        let e := ν.symm ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
        exact ⟨subgroupAt c e, (ofSubgroup_eq_mk_iff _ c e).2
          ((orbitRel (ConjAct (FundamentalGroup X x)) _).iseqv.refl _)⟩)⟩).symm

/-- The inverse classification sends a subgroup orbit to the class of its subgroup cover. -/
@[simp]
theorem subgroupConjugacyEquiv_symm_mk (H : Subgroup.ofIndex (FundamentalGroup X x) n) :
    subgroupConjugacyEquiv.symm (Quotient.mk'' H) = ofSubgroup H :=
  (rfl)

/-- On a subgroup cover the classification recovers the original conjugation orbit. -/
@[simp]
theorem subgroupConjugacyEquiv_ofSubgroup (H : Subgroup.ofIndex (FundamentalGroup X x) n) :
    subgroupConjugacyEquiv (ofSubgroup H) = Quotient.mk'' H := by
  rw [← subgroupConjugacyEquiv_symm_mk, Equiv.apply_symm_apply]

private theorem subgroupConjugacyEquiv_mk_subgroupAt (c : ConnectedCover x n)
    (e : ⇑c.cover.proj ⁻¹' {x}) :
    subgroupConjugacyEquiv (mk c) = Quotient.mk'' (subgroupAt c e) := by
  apply subgroupConjugacyEquiv.symm.injective
  rw [Equiv.symm_apply_apply, subgroupConjugacyEquiv_symm_mk, eq_comm,
    ofSubgroup_eq_mk_iff (subgroupAt c e) c e]

/-- The orbit attached to a cover is represented by the subgroup recovered at any fibre point. -/
theorem subgroupConjugacyEquiv_mk (c : ConnectedCover x n) (e : ⇑c.cover.proj ⁻¹' {x}) :
    subgroupConjugacyEquiv (mk c) = Quotient.mk''
      (⟨(mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ e.property).range,
        Subgroup.mem_ofIndex.mpr (c.index_range_mapOfEq e)⟩ :
          Subgroup.ofIndex (FundamentalGroup X x) n) := by
  simpa only [subgroupAt] using subgroupConjugacyEquiv_mk_subgroupAt c e

end ConnectedCoverClass

end TauCeti
