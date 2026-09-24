/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.Combinatorics.Quiver.Arborescence
public import TauCeti.Combinatorics.Quiver.WideSubquiver

/-!
# A free basis from a spanning tree

Given an arborescence in the symmetrified generating quiver of a free groupoid, this file
constructs a basis of the vertex group at the root, indexed by directed edges outside the
underlying unoriented tree.  The finite-quiver cardinality results in
`TauCeti.Combinatorics.Quiver.Arborescence` count this basis in applications to Schreier bounds.

## Main results

* `WideSubquiver.endFreeGroupBasis`: the non-tree directed edges freely generate the vertex
  group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 3.6.3.
* The construction adapts `Mathlib.GroupTheory.FreeGroup.NielsenSchreier` by David Wärn.
-/

attribute [local implicit_reducible]
  Quiver.Symmetrify IsFreeGroupoid.Generators
  WideSubquiver WideSubquiver.toType WideSubquiver.quiver IsFreeGroupoid.quiverGenerators
  Quiver.symmetrifyQuiver Quiver.wideSubquiverSymmetrify
  IsFreeGroupoid.SpanningTree.homOfPath

open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

public section

universe u

namespace TauCeti

namespace FreeGroupBasis

/-- Mathlib does not expose the generator computation for `ofUniqueLift`; keep its single
necessary unfold behind this private bridge. -/
private theorem ofUniqueLift_apply {G : Type u} [Group G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a)
    (x : X) : FreeGroupBasis.ofUniqueLift X of h x = of x := by
  change FreeGroup.lift of (FreeGroup.of x) = _
  exact FreeGroup.lift_apply_of

end FreeGroupBasis

namespace WideSubquiver

/-- A functor that kills the tree generators kills the morphism assigned to every tree path. -/
theorem spanningTree_map_homOfPath_eq_one
    {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C] {Y : Type u} [Group Y]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators C))) [Arborescence T]
    (F' : C ⥤ CategoryTheory.SingleObj Y)
    (hTree : ∀ {a b} (e : a ⟶ b), e ∈ wideSubquiverSymmetrify T a b →
      F'.map (IsFreeGroupoid.of e) = 1)
    {a : C} (p : Path (root T) a) :
    F'.map (IsFreeGroupoid.SpanningTree.homOfPath T p) = 1 := by
  induction p with
  | nil =>
      -- `SpanningTree.root'` is private, so the endpoints are not definitionally equal
      -- at the transparency used by `rw`; make the intended root equality explicit.
      change F'.map (𝟙 (show C from root T)) = 1
      rw [F'.map_id, id_as_one]
  | cons p e ih =>
      rw [IsFreeGroupoid.SpanningTree.homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
      rcases e with ⟨e | e, eT⟩
      · have he : e ∈ wideSubquiverSymmetrify T _ _ := by
          exact (_root_.TauCeti.WideSubquiver.mem_wideSubquiverSymmetrify_iff T e).mpr
            (Or.inl eT)
        rw [hTree e he]
      · have he : e ∈ wideSubquiverSymmetrify T _ _ := by
          exact (_root_.TauCeti.WideSubquiver.mem_wideSubquiverSymmetrify_iff T e).mpr
            (Or.inr eT)
        rw [F'.map_inv, inv_as_inv, inv_eq_one, hTree e he]

/-- A functor that kills the tree generators kills every tree homomorphism. -/
theorem spanningTree_map_treeHom_eq_one
    {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C] {Y : Type u} [Group Y]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators C))) [Arborescence T]
    (F' : C ⥤ CategoryTheory.SingleObj Y)
    (hTree : ∀ {a b} (e : a ⟶ b), e ∈ wideSubquiverSymmetrify T a b →
      F'.map (IsFreeGroupoid.of e) = 1)
    (a : C) :
    F'.map (IsFreeGroupoid.SpanningTree.treeHom T a) = 1 := by
  rw [IsFreeGroupoid.SpanningTree.treeHom_eq T (default : Path (root T) a)]
  exact spanningTree_map_homOfPath_eq_one T F' hTree _

/-- A functor that kills the tree generators factors through the spanning-tree loops. -/
theorem spanningTree_loopOfHom_map_eq_map
    {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C] {Y : Type u} [Group Y]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators C))) [Arborescence T]
    (F' : C ⥤ CategoryTheory.SingleObj Y)
    (hTree : ∀ {a b} (e : a ⟶ b), e ∈ wideSubquiverSymmetrify T a b →
      F'.map (IsFreeGroupoid.of e) = 1) :
    ∀ {x y} (q : x ⟶ y),
      F'.map (IsFreeGroupoid.SpanningTree.loopOfHom T q) = (F'.map q : Y) := by
  intro x y q
  simp only [IsFreeGroupoid.SpanningTree.loopOfHom, Functor.map_comp, comp_as_mul,
    inv_as_inv, spanningTree_map_treeHom_eq_one T F' hTree, inv_one, mul_one, one_mul,
    Functor.map_inv]

/-- The loops attached to the directed edges outside an unoriented spanning tree form a free
basis of the vertex group at the root. -/
noncomputable def endFreeGroupBasis
    {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators C))) [Arborescence T] :
    FreeGroupBasis
      ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set _)
      (End (show C from root T)) := by
  classical
  let X : Set _ := (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ
  let of : X → _ := fun e =>
    IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.val.hom)
  have hUniqueLift : ∀ {H : Type u} [Group H] (f : X → H),
      ∃! F : _ →* H, ∀ a, F (of a) = f a := by
    intro Y _ f
    let f' : Labelling (IsFreeGroupoid.Generators C) Y := fun a b e =>
      if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
    rcases IsFreeGroupoid.unique_lift f' with ⟨F', hF', uF'⟩
    refine ⟨F'.mapEnd _, ?_, ?_⟩
    · suffices ∀ {x y} (q : x ⟶ y),
          F'.map (IsFreeGroupoid.SpanningTree.loopOfHom T q) = (F'.map q : Y) by
        rintro ⟨⟨a, b, e⟩, h⟩
        simp only [of]
        simp only [Functor.mapEnd, DFunLike.coe, this, hF']
        exact dite_eq_right h
      have hTree : ∀ {a b} (e : a ⟶ b),
          e ∈ wideSubquiverSymmetrify T a b → F'.map (IsFreeGroupoid.of e) = 1 := by
        intro a b e he
        rw [hF']
        exact dite_eq_left he
      exact fun {x y} q => spanningTree_loopOfHom_map_eq_map T F' hTree q
    · intro E hE
      ext x
      have hRoot :
          (IsFreeGroupoid.SpanningTree.functorOfMonoidHom T E).map x = E x := by
        simp only [IsFreeGroupoid.SpanningTree.functorOfMonoidHom_map,
          IsFreeGroupoid.SpanningTree.loopOfHom,
          IsFreeGroupoid.SpanningTree.treeHom_root, IsIso.inv_id,
          Category.id_comp, Category.comp_id]
      suffices (IsFreeGroupoid.SpanningTree.functorOfMonoidHom T E).map x = F'.map x by
        exact hRoot.symm.trans this
      congr
      apply uF'
      intro a b e
      -- Expanding the labelling exposes the tree-edge case split used in its definition.
      change E (IsFreeGroupoid.SpanningTree.loopOfHom T _) = dite _ _ _
      split_ifs with h
      · rw [IsFreeGroupoid.SpanningTree.loopOfHom_eq_id T e h,
          ← CategoryTheory.End.one_def, E.map_one]
      · exact hE ⟨⟨a, b, e⟩, h⟩
  exact FreeGroupBasis.ofUniqueLift X of hUniqueLift

/-- Applying the spanning-tree basis to a non-tree edge gives its associated loop. -/
@[simp] theorem endFreeGroupBasis_apply
    {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators C))) [Arborescence T]
    (e : ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set _)) :
    endFreeGroupBasis T e =
      IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.val.hom) := by
  unfold endFreeGroupBasis
  exact FreeGroupBasis.ofUniqueLift_apply _ _ _ e

end WideSubquiver

end TauCeti
