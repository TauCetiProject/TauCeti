/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.NumberedFiber
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Intermediate
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Pointed connected covers are the subgroups of the fundamental group

Connected covers of `X` with a chosen point of the fibre over `x₀`, and maps over `X` carrying
point to point, form the category of elements `TauCeti.PointedConnectedCover x₀` of the fibre
functor over `x₀` on connected covers. There is at most one map between two objects
(`TauCeti.PointedConnectedCover.instIsThin`), by uniqueness of lifts.

A pointed connected cover `(E, e₀)` recovers the subgroup `p_* π₁(E, e₀)` of `π₁(X, x₀)`
(`TauCeti.PointedConnectedCover.subgroup`). Over a locally path-connected, semilocally simply
connected base this is an equivalence of the category of pointed connected covers with the poset
of subgroups of `π₁(X, x₀)` regarded as a category
(`TauCeti.exists_pointedConnectedCover_equivalence`): unique lifting gives faithfulness, the
lifting criterion gives fullness, and the quotient of the universal cover by a subgroup gives
essential surjectivity.

For `n ≠ 0` the same map is a bijection from the classes of pointed connected covers of degree
`n` onto the subgroups of index `n` (`TauCeti.exists_connectedPointedCoverClass_equiv_index`),
since the degree of a connected cover is the index of the subgroup it recovers
(`IsCoveringMap.card_fiber_eq_index`).

Connectedness of the total spaces is needed: over the circle, two disjoint copies of the identity
cover, pointed in the first, recover the whole fundamental group, like the identity cover, without
being isomorphic to it. The hypothesis `n ≠ 0` is needed for the slice: an infinite-index subgroup
has index `0`, while no cover of degree `0` has a point over `x₀`.

## Main definitions

* `TauCeti.PointedConnectedCover x₀`: the category of pointed connected covers.
* `TauCeti.PointedConnectedCover.subgroupFunctor x₀`: the recovered subgroup, as a functor to the
  poset of subgroups of `π₁(X, x₀)`.
* `TauCeti.ConnectedPointedCoverClass.subgroupEquiv`: the index-`n` slice.

## Main results

* `TauCeti.exists_pointedConnectedCover_equivalence`: **pointed connected covers are the subgroups
  of `π₁(X, x₀)`.**
* `TauCeti.exists_connectedPointedCoverClass_equiv_index`: **classes of pointed connected covers
  of degree `n ≠ 0` are the subgroups of index `n`.**

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.38, p. 67, with
  the partial order of covers on p. 68, and Proposition 1.32, p. 61 (the degree is the index).
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

variable {X : TopCat.{u}} (x₀ : X)

/-- **Pointed connected covers** of `X` at `x₀`: the category of elements of the fibre over `x₀`,
as a functor on connected covers. An object is a connected cover with a point of the fibre over
`x₀`; a morphism is a map over `X` carrying point to point. -/
abbrev PointedConnectedCover :=
  (ConnectedCoveringSpace.forget X ⋙ CoveringSpace.fiberActionFunctor x₀ ⋙
    Action.forget (Type u) (FundamentalGroup X x₀)).Elements

namespace PointedConnectedCover

variable {x₀}

/-- The subgroup `p_* π₁(E, e₀)` of `π₁(X, x₀)` recovered by a pointed connected cover. -/
def subgroup (c : PointedConnectedCover x₀) : Subgroup (FundamentalGroup X x₀) :=
  (FundamentalGroup.mapOfEq ⟨c.obj.proj, c.obj.isCoveringMap_proj.continuous⟩ c.val.property).range

theorem subgroup_def (c : PointedConnectedCover x₀) :
    c.subgroup =
      (FundamentalGroup.mapOfEq ⟨c.obj.proj, c.obj.isCoveringMap_proj.continuous⟩
        c.val.property).range :=
  (rfl)

/-- A map of connected covers acts on the fibre over `x₀` by restriction. -/
private theorem map_val_val {c : PointedConnectedCover x₀} {d : ConnectedCoveringSpace X}
    (f : c.obj ⟶ d) :
    ((ConnectedCoveringSpace.forget X ⋙ CoveringSpace.fiberActionFunctor x₀ ⋙
      Action.forget (Type u) (FundamentalGroup X x₀)).map f c.val).val = f.hom.left c.val.val := by
  rw [Functor.comp_map, Functor.comp_map, Action.forget_map,
    CoveringSpace.fiberActionFunctor_map_hom]
  exact Function.fiberMap_apply_coe _ _ x₀ c.val

/-- A map of pointed connected covers carries the chosen point to the chosen point. -/
@[simp]
theorem hom_left_apply {c d : PointedConnectedCover x₀} (f : c ⟶ d) :
    f.hom.hom.left c.val.val = d.val.val :=
  (map_val_val f.hom).symm.trans (congrArg Subtype.val f.map_val)

/-- A map of pointed connected covers commutes with the projections. -/
theorem proj_comp_hom_left {c d : PointedConnectedCover x₀} (f : c ⟶ d) :
    ⇑d.obj.proj ∘ ⇑f.hom.hom.left = ⇑c.obj.proj :=
  funext fun e ↦ congrArg (fun g ↦ g e) (congrArg (⇑) (CoveringSpace.FullSubcategory.w f.hom))

/-- **There is at most one map between two pointed connected covers**, by uniqueness of lifts on
the connected total space. -/
instance instIsThin : Quiver.IsThin (PointedConnectedCover x₀) := fun c d ↦ ⟨fun f f' ↦ by
  have h := d.obj.isCoveringMap_proj.eq_of_comp_eq f.hom.hom.left.hom.continuous
    f'.hom.hom.left.hom.continuous ((proj_comp_hom_left f).trans (proj_comp_hom_left f').symm)
    c.val.val ((hom_left_apply f).trans (hom_left_apply f').symm)
  ext : 2
  exact Over.OverMorphism.ext (ConcreteCategory.hom_ext _ _ (congrFun h))⟩

/-- A map of pointed connected covers exists only when the recovered subgroups are nested: this is
functoriality of `π₁`. -/
theorem subgroup_le_of_hom {c d : PointedConnectedCover x₀} (f : c ⟶ d) :
    c.subgroup ≤ d.subgroup :=
  IsCoveringMap.range_le_of_continuousMap_comp_eq c.obj.isCoveringMap_proj.continuous
    d.obj.isCoveringMap_proj.continuous c.val.property d.val.property (hom_left_apply f)
      (proj_comp_hom_left f)

variable (x₀) in
/-- The recovered subgroup, as a functor from pointed connected covers to the poset of subgroups
of `π₁(X, x₀)`. -/
def subgroupFunctor :
    PointedConnectedCover x₀ ⥤ Subgroup (FundamentalGroup X x₀) where
  obj := subgroup
  map f := homOfLE (subgroup_le_of_hom f)

@[simp]
theorem subgroupFunctor_obj (c : PointedConnectedCover x₀) :
    (subgroupFunctor x₀).obj c = c.subgroup :=
  (rfl)

instance : (subgroupFunctor x₀).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The lifting criterion: nested recovered subgroups give a map of pointed covers. -/
instance [LocallyPathConnectedSpace X] : (subgroupFunctor x₀).Full where
  map_surjective {c d} f := by
    obtain ⟨g, hg, hcomp⟩ := (IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le
      d.obj.isCoveringMap_proj c.obj.isCoveringMap_proj.continuous c.val.property
        d.val.property).mpr (leOfHom f)
    refine ⟨⟨CoveringSpace.FullSubcategory.homMk (TopCat.ofHom g)
      (ConcreteCategory.hom_ext _ _ fun e ↦ congrFun hcomp e), ?_⟩, Subsingleton.elim _ _⟩
    refine Subtype.ext ((map_val_val _).trans ?_)
    rw [CoveringSpace.FullSubcategory.homMk_hom_left]
    exact hg

end PointedConnectedCover

namespace PointedConnectedCover

variable {x₀}

/-- The cover attached to a subgroup, pointed at the class of the constant path. -/
@[expose] def ofSubgroup [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) : PointedConnectedCover x₀ :=
  Functor.elementsMk _ (UniversalCover.subgroupCover x₀ H)
    (UniversalCover.subgroupCoverBasepointFiber x₀ H)

@[simp]
theorem ofSubgroup_obj [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) :
    (ofSubgroup H).obj = UniversalCover.subgroupCover x₀ H :=
  (rfl)

@[simp]
theorem ofSubgroup_val [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) :
    (ofSubgroup H).val = UniversalCover.subgroupCoverBasepointFiber x₀ H :=
  (rfl)

/-- The pointed cover attached to a subgroup recovers it. -/
@[simp]
theorem subgroup_ofSubgroup [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) : (ofSubgroup H).subgroup = H :=
  UniversalCover.range_mapOfEq_subgroupCover x₀ H

instance [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    (subgroupFunctor x₀).EssSurj where
  mem_essImage H := ⟨ofSubgroup H, ⟨eqToIso (subgroup_ofSubgroup H)⟩⟩

instance [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    (subgroupFunctor x₀).IsEquivalence where

end PointedConnectedCover

/-- **Pointed connected covers are the subgroups of `π₁`**: over a locally path-connected,
semilocally simply connected base, the recovered subgroup is an equivalence between pointed
connected covers and the poset of subgroups of `π₁(X, x₀)`. The target is thin, so the object map
determines the equivalence up to isomorphism. -/
theorem exists_pointedConnectedCover_equivalence (X : TopCat.{u}) [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    ∃ E : PointedConnectedCover x₀ ≌ Subgroup (FundamentalGroup X x₀),
      ∀ c : PointedConnectedCover x₀, E.functor.obj c =
        (FundamentalGroup.mapOfEq ⟨c.obj.proj, c.obj.isCoveringMap_proj.continuous⟩
          c.val.property).range :=
  ⟨(PointedConnectedCover.subgroupFunctor x₀).asEquivalence, fun _ ↦ rfl⟩

/-! ### The index-`n` slice -/

namespace ConnectedPointedCover

variable {x₀} {n : ℕ}

/-- A pointed connected cover of degree `n`, as an object of the category of pointed connected
covers. -/
@[expose] def toPointed (c : ConnectedPointedCover x₀ n) : PointedConnectedCover x₀ :=
  Functor.elementsMk _ c.cover c.e

@[simp]
theorem toPointed_obj (c : ConnectedPointedCover x₀ n) : c.toPointed.obj = c.cover :=
  (rfl)

@[simp]
theorem toPointed_val (c : ConnectedPointedCover x₀ n) : c.toPointed.val = c.e :=
  (rfl)

/-- The subgroup of `π₁(X, x₀)` recovered by a pointed connected cover of degree `n`, that of the
underlying pointed connected cover. -/
def subgroup (c : ConnectedPointedCover x₀ n) : Subgroup (FundamentalGroup X x₀) :=
  c.toPointed.subgroup

theorem subgroup_def (c : ConnectedPointedCover x₀ n) :
    c.subgroup =
      (FundamentalGroup.mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩
        c.e.property).range :=
  (rfl)

/-- The subgroup recovered by a pointed connected cover of degree `n` has index `n`. -/
theorem index_subgroup [LocallyPathConnectedSpace X] (c : ConnectedPointedCover x₀ n) :
    c.subgroup.index = n :=
  (c.cover.isCoveringMap_proj.card_fiber_eq_index c.e).symm.trans
    ((Nat.card_congr c.nonempty_equiv_fin.some).trans (Nat.card_fin n))

/-- A pointed isomorphism of covers of degree `n` gives a map of pointed connected covers. -/
private def homOfIso {c c' : ConnectedPointedCover x₀ n} (f : c.cover ≅ c'.cover)
    (hf : f.hom.hom.left c.e.val = c'.e.val) : c.toPointed ⟶ c'.toPointed :=
  ⟨f.hom, Subtype.ext ((PointedConnectedCover.map_val_val (c := c.toPointed) f.hom).trans hf)⟩

/-- Pointed isomorphic covers recover the same subgroup. -/
theorem subgroup_eq_of_iso {c c' : ConnectedPointedCover x₀ n}
    (h : ConnectedPointedCoverIso c c') : c.subgroup = c'.subgroup := by
  obtain ⟨f, hf⟩ := connectedPointedCoverIso_def.mp h
  obtain ⟨f', hf'⟩ := connectedPointedCoverIso_def.mp h.symm
  exact le_antisymm (PointedConnectedCover.subgroup_le_of_hom (homOfIso f hf))
    (PointedConnectedCover.subgroup_le_of_hom (homOfIso f' hf'))

end ConnectedPointedCover

namespace ConnectedPointedCoverClass

variable {x₀} {n : ℕ}

/-- The subgroup recovered by a class of pointed connected covers of degree `n`, with its index. -/
def subgroup [LocallyPathConnectedSpace X] :
    ConnectedPointedCoverClass x₀ n → {H : Subgroup (FundamentalGroup X x₀) // H.index = n} :=
  lift (fun c ↦ ⟨c.subgroup, c.index_subgroup⟩) fun _ _ h ↦
    Subtype.ext (ConnectedPointedCover.subgroup_eq_of_iso h)

@[simp]
theorem subgroup_mk [LocallyPathConnectedSpace X] (c : ConnectedPointedCover x₀ n) :
    (subgroup (mk c)).val = c.subgroup := by
  rw [subgroup, lift_mk]

theorem subgroup_injective [LocallyPathConnectedSpace X] :
    Function.Injective (subgroup (x₀ := x₀) (n := n)) := by
  intro C C' h
  induction C using ind with | h c =>
  induction C' using ind with | h c' =>
  have h' := congrArg Subtype.val h
  rw [subgroup_mk, subgroup_mk] at h'
  exact mk_eq_mk_of_range_eq c c' h'

theorem subgroup_surjective [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    [NeZero n] : Function.Surjective (subgroup (x₀ := x₀) (n := n)) := by
  rintro ⟨H, hH⟩
  let p := UniversalCover.subgroupCover x₀ H
  let e := UniversalCover.subgroupCoverBasepointFiber x₀ H
  have hcard : Nat.card (⇑p.proj ⁻¹' {x₀}) = n := by
    rw [p.isCoveringMap_proj.card_fiber_eq_index e, UniversalCover.range_mapOfEq_subgroupCover, hH]
  have := Nat.finite_of_card_ne_zero (hcard.trans_ne (NeZero.ne n))
  refine ⟨mk ⟨p, e, ⟨Finite.equivFinOfCardEq hcard⟩⟩, Subtype.ext ?_⟩
  rw [subgroup_mk]
  exact UniversalCover.range_mapOfEq_subgroupCover x₀ H

/-- **The index-`n` slice of the classification of pointed covers**: for `n ≠ 0`, a class of
pointed connected covers of degree `n` goes to its recovered subgroup, a subgroup of index `n`,
and this is a bijection. -/
def subgroupEquiv [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] [NeZero n] :
    ConnectedPointedCoverClass x₀ n ≃ {H : Subgroup (FundamentalGroup X x₀) // H.index = n} :=
  Equiv.ofBijective subgroup ⟨subgroup_injective, subgroup_surjective⟩

@[simp]
theorem subgroupEquiv_mk [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    [NeZero n] (c : ConnectedPointedCover x₀ n) : (subgroupEquiv (mk c)).val = c.subgroup :=
  subgroup_mk c

end ConnectedPointedCoverClass

/-- **The index-`n` slice of the pointed classification of covers**: over a locally
path-connected, semilocally simply connected base, for `n ≠ 0`, the classes of pointed connected
covers of degree `n` correspond to the subgroups of index `n` of `π₁(X, x₀)`, each class going to
its recovered subgroup. -/
theorem exists_connectedPointedCoverClass_equiv_index (X : TopCat.{u})
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x₀ : X) (n : ℕ)
    [NeZero n] :
    ∃ e : ConnectedPointedCoverClass x₀ n ≃
        {H : Subgroup (FundamentalGroup X x₀) // H.index = n},
      ∀ c : ConnectedPointedCover x₀ n,
        (e (ConnectedPointedCoverClass.mk c)).val =
          (FundamentalGroup.mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩
            c.e.property).range :=
  ⟨ConnectedPointedCoverClass.subgroupEquiv, ConnectedPointedCoverClass.subgroupEquiv_mk⟩

end TauCeti
