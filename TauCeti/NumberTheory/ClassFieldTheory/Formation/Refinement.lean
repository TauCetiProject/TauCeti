/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic

/-!
# Refinements of a finite normal layer, and inflation

Let `V ◁ U` be a finite normal layer of a formation, the layer `K/F` in field notation. Enlarging
the top field to a bigger Galois extension `F ⊆ K ⊆ L` leaves a layer `L/F` whose top subgroup
`V' = G_L` is smaller and whose ground subgroup is unchanged. Two layers are related by a
**refinement** when they have the same ground subgroup and the top subgroup of the second lies in
the top subgroup of the first; `LayerRefinement old new` is that relation. Its **relative degree**
is `[V : V']`, the degree `[L : K]` of the new top field over the old one.

Along a refinement the Galois group of the new layer surjects onto the Galois group of the old one
(`LayerRefinement.galHom`, the quotient map `U/V' → U/V`), and the coefficient module `A^V` of the
old layer sits inside the coefficient module `A^{V'}` of the new one, equivariantly for the action
of `U/V'` through `galHom` (`LayerRefinement.repHom`). Together these induce **inflation** on
cohomology, `H^n(U/V, A^V) → H^n(U/V', A^{V'})`, in ordinary degrees and in positive Tate degrees.
Two refinements of one layer always have a common refinement, the compositum, whose top subgroup is
the intersection of the two top subgroups; this is what lets a construction made at "some
refinement" be compared across refinements.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRefinement`: the relation `new` is `old` with its top field
  enlarged.
* `TauCeti.ClassFieldTheory.LayerRefinement.relativeDegree`: the relative degree `[V : V']`.
* `TauCeti.ClassFieldTheory.LayerRefinement.galHom`: the quotient map `U/V' → U/V`.
* `TauCeti.ClassFieldTheory.LayerRefinement.quotientHom`: the induced map of abelianized Galois
  groups.
* `TauCeti.ClassFieldTheory.LayerRefinement.groundEquiv`: the identity of ground levels.
* `TauCeti.ClassFieldTheory.LayerRefinement.repHom`: the inclusion `A^V ⊆ A^{V'}` as a morphism
  of representations.
* `TauCeti.ClassFieldTheory.LayerRefinement.cohomologyInfl`, `tateInfl`: inflation on ordinary
  cohomology and on positive-degree Tate cohomology.
* `TauCeti.ClassFieldTheory.LayerRefinement.commonRefinement`: the compositum of two refinements.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRefinement.degree_mul_relativeDegree`:
  `[U : V] * [V : V'] = [U : V']`.
* `TauCeti.ClassFieldTheory.LayerRefinement.galHom_surjective`: the Galois group of the new layer
  surjects onto the Galois group of the old one.
* `TauCeti.ClassFieldTheory.LayerRefinement.ker_galHom`: the kernel of that surjection is the
  image of `V` in `U/V'`.
* `TauCeti.ClassFieldTheory.LayerRefinement.cohomologyInfl_trans`: inflation is functorial in a
  tower of top fields.
* `TauCeti.ClassFieldTheory.LayerRefinement.exists_commonRefinement`: two refinements of a layer
  have a common refinement.

## Implementation notes

Like `LayerRestriction`, a `LayerRefinement` is a relation between two layers that already exist,
so that towers of refinements compose without transporting a layer along an equality; the relative
degree is a function of the two layers that takes the refinement proof only to support the
notation `T.relativeDegree`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–2.
* J. Neukirch, *Class Field Theory*, Chapter III, §1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter I, §5 (inflation
  and the change-of-group maps).
-/

-- The signatures of `LayerRefinement`, `relativeDegree`, `galHom`, `quotientHom`, `groundEquiv`,
-- `cohomologyInfl`, `tateInfl` and `exists_commonRefinement` below follow the Tau Ceti
-- `ClassFieldTheory` blueprint, `README.md` and `Suggested.lean`.

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### Refinements -/

/-- A **refinement** of finite normal layers: `new` is `old` with its top field enlarged. In field
notation, `F ⊆ K ⊆ L` takes the layer `K/F` to the layer `L/F`, so the ground subgroup is
unchanged and the top subgroup shrinks. Compare `LayerRestriction`, which instead raises the ground
field and keeps the top field. Refinements compose via `LayerRefinement.trans` and induce inflation
on layer cohomology (`LayerRefinement.cohomologyInfl`). Shrinking an open normal subgroup gives the
basic examples (`NormalLayer.refinement_ofOpenNormal`), and two refinements of one layer always
have a common refinement, the compositum (`LayerRefinement.exists_commonRefinement`). -/
structure LayerRefinement (old new : NormalLayer G) : Prop where
  /-- a refinement does not move the ground subgroup -/
  same_ground : old.ground = new.ground
  /-- a refinement shrinks the top subgroup -/
  new_top_le : new.top ≤ old.top

namespace LayerRefinement

variable {old new : NormalLayer G}

/-- The ground subgroups of a refinement agree as subgroups of the ambient group: the field
`same_ground` in the form the `Subgroup` API takes. `T.same_ground_toSubgroup.ge` is the inclusion
`new.ground ≤ old.ground` of subgroups that `galHom` and `ker_galHom` consume. -/
theorem same_ground_toSubgroup (T : LayerRefinement old new) :
    old.ground.toSubgroup = new.ground.toSubgroup :=
  congrArg OpenSubgroup.toSubgroup T.same_ground

/-- The top subgroups of a refinement, compared as subgroups of the ambient group. -/
theorem new_top_toSubgroup_le (T : LayerRefinement old new) :
    new.top.toSubgroup ≤ old.top.toSubgroup :=
  OpenSubgroup.toSubgroup_le.2 T.new_top_le

/-- The **relative degree** `[V : V']` of a refinement, the degree of the new top field over the
old one. -/
def relativeDegree (_T : LayerRefinement old new) : ℕ :=
  new.top.toSubgroup.relIndex old.top.toSubgroup

/-- The relative degree is the relative index of the two top subgroups. -/
@[simp]
theorem relativeDegree_def (T : LayerRefinement old new) :
    T.relativeDegree = new.top.toSubgroup.relIndex old.top.toSubgroup :=
  by simp only [relativeDegree]

/-- **The degree of a layer is multiplicative along a refinement:** `[U : V] * [V : V'] =
[U : V']`. -/
theorem degree_mul_relativeDegree (T : LayerRefinement old new) :
    old.degree * T.relativeDegree = new.degree := by
  rw [NormalLayer.degree_eq_relIndex, NormalLayer.degree_eq_relIndex, relativeDegree_def,
    ← T.same_ground_toSubgroup, mul_comm]
  exact Subgroup.relIndex_mul_relIndex _ _ _ T.new_top_toSubgroup_le
    (OpenSubgroup.toSubgroup_le.2 old.top_le_ground)

/-- The relative degree of a refinement is positive: the Galois groups involved are finite. -/
theorem relativeDegree_pos (T : LayerRefinement old new) : 0 < T.relativeDegree :=
  Nat.pos_of_mul_pos_left (T.degree_mul_relativeDegree ▸ new.degree_pos)

/-- Refinements compose: a tower `F ⊆ K ⊆ L ⊆ M` of top fields. -/
theorem trans {newer : NormalLayer G} (S : LayerRefinement old new)
    (T : LayerRefinement new newer) : LayerRefinement old newer where
  same_ground := S.same_ground.trans T.same_ground
  new_top_le := T.new_top_le.trans S.new_top_le

/-- The relative degree is multiplicative in a tower of top fields. -/
theorem relativeDegree_trans {newer : NormalLayer G} (S : LayerRefinement old new)
    (T : LayerRefinement new newer) :
    (S.trans T).relativeDegree = S.relativeDegree * T.relativeDegree := by
  rw [relativeDegree_def, relativeDegree_def, relativeDegree_def, mul_comm]
  exact (Subgroup.relIndex_mul_relIndex _ _ _ T.new_top_toSubgroup_le S.new_top_toSubgroup_le).symm

/-! ### The Galois groups of a refinement -/

/-- The quotient map `U/V' → U/V` of Galois groups induced by a refinement. It is surjective
(`galHom_surjective`), with kernel the image of `V` in `U/V'` (`ker_galHom`). -/
def galHom (T : LayerRefinement old new) : new.Gal →* old.Gal :=
  @QuotientGroup.quotientMapSubgroupOfOfLe G _ new.top.toSubgroup new.ground.toSubgroup
    old.top.toSubgroup old.ground.toSubgroup new.normal old.normal
    T.new_top_toSubgroup_le T.same_ground_toSubgroup.ge

/-- The quotient map of Galois groups is induced by the identity of ground subgroups. -/
@[simp]
theorem galHom_mk (T : LayerRefinement old new) (w : new.ground) :
    T.galHom (QuotientGroup.mk w) =
      QuotientGroup.mk (Subgroup.inclusion T.same_ground_toSubgroup.ge w) :=
  @QuotientGroup.quotientMapSubgroupOfOfLe_mk G _ new.top.toSubgroup new.ground.toSubgroup
    old.top.toSubgroup old.ground.toSubgroup new.normal old.normal
    T.new_top_toSubgroup_le T.same_ground_toSubgroup.ge w

/-- **The Galois group of the new layer of a refinement surjects onto the Galois group of the old
one.** -/
theorem galHom_surjective (T : LayerRefinement old new) : Function.Surjective T.galHom := by
  intro γ
  induction γ using QuotientGroup.induction_on with
  | H u =>
    refine ⟨QuotientGroup.mk ⟨u, T.same_ground ▸ u.2⟩, ?_⟩
    rw [galHom_mk]
    rfl

/-- The kernel of the quotient map of Galois groups is the image of the old top subgroup `V` in
the new Galois group `U/V'`. -/
theorem ker_galHom (T : LayerRefinement old new) :
    T.galHom.ker =
      (old.top.toSubgroup.subgroupOf new.ground.toSubgroup).map
        (QuotientGroup.mk' new.relativeTop) := by
  refine (QuotientGroup.ker_map new.relativeTop old.relativeTop
    (Subgroup.inclusion T.same_ground_toSubgroup.ge)
    (Subgroup.comap_mono T.new_top_toSubgroup_le)).trans ?_
  -- `ker_map` gives the kernel as a `mk'`-image; the subgroup mapped is `old.relativeTop` pulled
  -- back along the ground inclusion, which is `old.top` viewed inside `new.ground` because that
  -- inclusion composed with the old ground's inclusion is the new ground's inclusion.
  refine congrArg (Subgroup.map (QuotientGroup.mk' new.relativeTop)) ?_
  rw [NormalLayer.relativeTop, ← Subgroup.comap_subtype, ← Subgroup.comap_subtype,
    Subgroup.comap_comap, Subgroup.subtype_comp_inclusion]

/-- The quotient maps of Galois groups compose along a tower of top fields. -/
theorem galHom_trans {newer : NormalLayer G} (S : LayerRefinement old new)
    (T : LayerRefinement new newer) : (S.trans T).galHom = S.galHom.comp T.galHom :=
  MonoidHom.ext fun γ ↦ QuotientGroup.induction_on γ fun w ↦ by
    rw [MonoidHom.comp_apply, galHom_mk, galHom_mk, galHom_mk]
    rfl

/-- The quotient map `(U/V')^ab → (U/V)^ab` of abelianized Galois groups, written additively. -/
def quotientHom (T : LayerRefinement old new) :
    Additive (Abelianization new.Gal) →+ Additive (Abelianization old.Gal) :=
  MonoidHom.toAdditive (Abelianization.map T.galHom)

/-- The map of abelianized Galois groups sends the class of `γ` to the class of `galHom γ`. -/
@[simp]
theorem quotientHom_ofMul_of (T : LayerRefinement old new) (γ : new.Gal) :
    T.quotientHom (Additive.ofMul (Abelianization.of γ)) =
      Additive.ofMul (Abelianization.of (T.galHom γ)) := by
  rw [quotientHom, MonoidHom.toAdditive_apply_apply, toMul_ofMul, Abelianization.map_of]

/-! ### The coefficient modules of a refinement -/

section Coefficients

/-- The identity of ground levels of a refinement, transported along `same_ground`. -/
def groundEquiv (T : LayerRefinement old new) (F : Formation G) :
    F.level old.ground ≃+ F.level new.ground :=
  (LinearEquiv.ofEq _ _ (congrArg F.level T.same_ground)).toAddEquiv

/-- The identity of ground levels moves no element of the ambient module. -/
@[simp]
theorem groundEquiv_apply_coe (T : LayerRefinement old new) (F : Formation G)
    (x : F.level old.ground) :
    ((T.groundEquiv F x : F.level new.ground) : F.toRep.V) = (x : F.toRep.V) :=
  LinearEquiv.coe_ofEq_apply (congrArg F.level T.same_ground) x

/-- The old top level sits inside the new one: a smaller subgroup fixes more. -/
theorem level_top_le_level_top (T : LayerRefinement old new) (F : Formation G) :
    F.level old.top ≤ F.level new.top :=
  F.level_antitone T.new_top_le

/-- **The coefficient module of the old layer of a refinement sits inside the coefficient module of
the new one**, equivariantly for the action of the new Galois group through `galHom`: the
inclusion `A^V ⊆ A^{V'}` as a morphism of representations. -/
def repHom (T : LayerRefinement old new) (F : Formation G) :
    Rep.res T.galHom (old.rep F) ⟶ new.rep F :=
  Rep.ofHom
    { toLinearMap := Submodule.inclusion (T.level_top_le_level_top F)
      isIntertwining' := fun γ ↦ by
        induction γ using QuotientGroup.induction_on with
        | H w =>
          ext x
          -- Expose the ambient-module coercions hidden behind the restricted representation and
          -- the inclusion before applying the public coercion lemmas.
          change
            ((Submodule.inclusion (T.level_top_le_level_top F)
                ((old.rep F).ρ (T.galHom (QuotientGroup.mk w)) x) : F.level new.top) :
                  F.toRep.V) =
              (((new.rep F).ρ (QuotientGroup.mk w)
                (Submodule.inclusion (T.level_top_le_level_top F) x) : F.level new.top) :
                  F.toRep.V)
          rw [galHom_mk, Submodule.coe_inclusion, old.rep_ρ_mk_apply_coe F, Subgroup.coe_inclusion,
            new.rep_ρ_mk_apply_coe F, Submodule.coe_inclusion] }

/-- The inclusion of coefficient modules moves no element of the ambient module. -/
@[simp]
theorem repHom_hom_apply_coe (T : LayerRefinement old new) (F : Formation G)
    (x : F.level old.top) :
    (((T.repHom F).hom x : F.level new.top) : F.toRep.V) = (x : F.toRep.V) :=
  (rfl)

end Coefficients

/-! ### Inflation -/

section Inflation

/-- **Inflation on ordinary finite-layer cohomology**, `H^n(U/V, A^V) → H^n(U/V', A^{V'})`: the
map of cohomology induced by the quotient map `galHom` of Galois groups and the inclusion `repHom`
of coefficient modules. -/
@[expose] def cohomologyInfl (T : LayerRefinement old new) (F : Formation G) (n : ℕ) :
    old.H F n →+ new.H F n :=
  (groupCohomology.map T.galHom (T.repHom F) n).hom.toAddMonoidHom

/-- Inflation on cohomology is the underlying map of `groupCohomology.map`. -/
@[simp]
theorem cohomologyInfl_apply (T : LayerRefinement old new) (F : Formation G) (n : ℕ)
    (x : old.H F n) :
    T.cohomologyInfl F n x = (groupCohomology.map T.galHom (T.repHom F) n).hom x :=
  rfl

/-- Inflation is functorial in a tower of top fields. -/
theorem cohomologyInfl_trans {newer : NormalLayer G} (S : LayerRefinement old new)
    (T : LayerRefinement new newer) (F : Formation G) (n : ℕ) (x : old.H F n) :
    (S.trans T).cohomologyInfl F n x = T.cohomologyInfl F n (S.cohomologyInfl F n x) := by
  have key : groupCohomology.map (S.trans T).galHom ((S.trans T).repHom F) n =
      groupCohomology.map S.galHom (S.repHom F) n ≫
        groupCohomology.map T.galHom (T.repHom F) n := by
    rw [← groupCohomology.map_comp]
    refine groupCohomology.map_congr (galHom_trans S T) (LinearMap.ext fun y ↦ ?_) n
    -- Both sides are the inclusion `A^V ⊆ A^{V''}`, once the composite is unfolded to its
    -- constituent inclusions.
    simp only [Rep.res_obj_ρ, Representation.IntertwiningMap.coe_toLinearMap, Rep.hom_comp,
      Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap,
      LinearMap.coe_comp, Function.comp_apply]
    exact Subtype.ext (by rw [repHom_hom_apply_coe, repHom_hom_apply_coe, repHom_hom_apply_coe])
  simp only [cohomologyInfl_apply]
  rw [key, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Inflation on the finite-layer Tate groups**, in positive degrees only: in positive degree
the Tate groups are the ordinary cohomology groups, and inflation is `cohomologyInfl` read through
that identification. -/
@[expose] def tateInfl (T : LayerRefinement old new) (F : Formation G) (r : ℕ) (hr : 0 < r) :
    old.TateH F r →+ new.TateH F r :=
  haveI : NeZero r := ⟨hr.ne'⟩
  (((TateCohomology.isoGroupCohomology r).app (old.rep F)).hom ≫
    groupCohomology.map T.galHom (T.repHom F) r ≫
    ((TateCohomology.isoGroupCohomology r).app (new.rep F)).inv).hom.toAddMonoidHom

/-- **Tate inflation is ordinary inflation read through the degree-`r` comparison isomorphisms**:
for positive `r`, `tateInfl` is `cohomologyInfl` conjugated by the isomorphisms
`TateCohomology.isoGroupCohomology r` at the old and new layers. This is the commuting square that
characterizes `tateInfl`. -/
theorem tateInfl_eq (T : LayerRefinement old new) (F : Formation G) (r : ℕ) [NeZero r]
    (x : old.TateH F r) :
    T.tateInfl F r (Nat.pos_of_ne_zero (NeZero.ne r)) x =
      ((TateCohomology.isoGroupCohomology r).app (new.rep F)).inv.hom
        (T.cohomologyInfl F r
          (((TateCohomology.isoGroupCohomology r).app (old.rep F)).hom.hom x)) :=
  rfl

end Inflation

/-! ### Common refinements -/

section CommonRefinement

variable {new₁ new₂ : NormalLayer G}

/-- **The compositum of two refinements** of a layer: the layer with the same ground subgroup
whose top subgroup is the intersection of the two top subgroups. In field language it is the
compositum `L₁ L₂` of the two top fields over the common ground field. -/
def commonRefinement (T₁ : LayerRefinement old new₁) (T₂ : LayerRefinement old new₂) :
    NormalLayer G where
  ground := old.ground
  top := new₁.top ⊓ new₂.top
  top_le_ground := inf_le_left.trans (T₁.new_top_le.trans old.top_le_ground)
  normal :=
    ⟨fun _v hv u ↦ Subgroup.mem_subgroupOf.2
      ⟨new₁.conj_mem_top (T₁.same_ground ▸ u.2) (Subgroup.mem_subgroupOf.1 hv).1,
        new₂.conj_mem_top (T₂.same_ground ▸ u.2) (Subgroup.mem_subgroupOf.1 hv).2⟩⟩

/-- The compositum has the common ground subgroup. -/
@[simp]
theorem ground_commonRefinement (T₁ : LayerRefinement old new₁)
    (T₂ : LayerRefinement old new₂) : (commonRefinement T₁ T₂).ground = old.ground :=
  (rfl)

/-- The top subgroup of the compositum is the intersection of the two top subgroups. -/
@[simp]
theorem top_commonRefinement (T₁ : LayerRefinement old new₁)
    (T₂ : LayerRefinement old new₂) : (commonRefinement T₁ T₂).top = new₁.top ⊓ new₂.top :=
  (rfl)

/-- The compositum refines the first of the two layers. -/
theorem refinement_commonRefinement_left (T₁ : LayerRefinement old new₁)
    (T₂ : LayerRefinement old new₂) : LayerRefinement new₁ (commonRefinement T₁ T₂) :=
  ⟨T₁.same_ground.symm, inf_le_left⟩

/-- The compositum refines the second of the two layers. -/
theorem refinement_commonRefinement_right (T₁ : LayerRefinement old new₁)
    (T₂ : LayerRefinement old new₂) : LayerRefinement new₂ (commonRefinement T₁ T₂) :=
  ⟨T₂.same_ground.symm, inf_le_right⟩

/-- **Two refinements of a layer have a common refinement**, the compositum. This is what lets a
construction made at "some refinement" be compared across refinements. -/
theorem exists_commonRefinement (T₁ : LayerRefinement old new₁) (T₂ : LayerRefinement old new₂) :
    ∃ newer : NormalLayer G, LayerRefinement new₁ newer ∧ LayerRefinement new₂ newer :=
  ⟨commonRefinement T₁ T₂, refinement_commonRefinement_left T₁ T₂,
    refinement_commonRefinement_right T₁ T₂⟩

end CommonRefinement

end LayerRefinement

/-! ### Refinements of the layers of open normal subgroups -/

namespace NormalLayer

/-- Shrinking an open normal subgroup refines the layer it cuts out: `W ≤ V` gives a refinement
from the layer `V ◁ ⊤` to the layer `W ◁ ⊤`. -/
theorem refinement_ofOpenNormal {V W : OpenNormalSubgroup G} (h : W ≤ V) :
    LayerRefinement (ofOpenNormal V) (ofOpenNormal W) :=
  ⟨(ground_ofOpenNormal V).trans (ground_ofOpenNormal W).symm, by
    rw [top_ofOpenNormal, top_ofOpenNormal]
    exact h⟩

end NormalLayer

end TauCeti.ClassFieldTheory
