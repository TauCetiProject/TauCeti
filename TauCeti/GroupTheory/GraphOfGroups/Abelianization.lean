/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.PathGroup
public import TauCeti.GroupTheory.GraphOfGroups.PathGroup
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# The abelianization of the path group of a graph

The reduced path group of a connected Serre graph is free on the tree loops through the positive
darts outside a spanning tree. Hence its abelianization is free abelian on those darts. The free
coordinates of a class are the coordinates of its integral cycle class at the positive darts
outside the tree, so the free generators correspond to the fundamental cycles of the tree.

Under a change of spanning tree from `T` to `T'`, the free generator of a positive dart outside
`T` has as free coordinates relative to `T'` the coordinates of the cycle class of its `T`-loop at
the positive darts outside `T'`. The free coordinates are natural for morphisms carrying the tree
into a tree and positive darts outside the tree to positive darts outside the tree.

## Main definitions

* `TauCeti.SerreGraph.SpanningTree.abelianizationEquivFreeAbelianGroup`: the abelianized path
  group is free abelian on the positive darts outside a spanning tree.

## Main results

* `TauCeti.SerreGraph.SpanningTree.equivFinsupp_abelianizationEquivFreeAbelianGroup`: the free
  coordinates are the coordinates of the cycle class outside the tree.
* `TauCeti.SerreGraph.SpanningTree.equivFinsupp_abelianizationEquivFreeAbelianGroup_symm_of`:
  change of spanning tree in free abelian coordinates.
* `TauCeti.SerreGraph.SpanningTree.abelianizationEquivFreeAbelianGroup_map`: the free abelian
  coordinates are natural for graph morphisms carrying a spanning tree into a spanning tree.

## References

* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2, and §2.A, Theorem 2A.1.
* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
-/

public section

namespace TauCeti.SerreGraph.SpanningTree

variable {Γ : SerreGraph} (T : Γ.SpanningTree) (v : Γ.V) {O : Set Γ.E}

/-- The abelianization of the reduced path group is free abelian on the positive darts outside
a spanning tree. -/
noncomputable def abelianizationEquivFreeAbelianGroup (hO : Γ.IsOrientation O) :
    Additive (Group.Abelianization (PathGroup Γ v)) ≃+ FreeAbelianGroup ↥(O \ T.darts) :=
  (T.pathGroupEquivFreeGroup v hO).abelianizationCongr.toAdditive

/-- The class of the tree loop through a positive dart outside the tree is the free generator
of that dart. -/
@[simp] theorem abelianizationEquivFreeAbelianGroup_loop (hO : Γ.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    T.abelianizationEquivFreeAbelianGroup v hO
      (Additive.ofMul (Group.Abelianization.of (T.loop v e.1))) = FreeAbelianGroup.of e := by
  -- `FreeAbelianGroup.of e` is by definition the additive class of `FreeGroup.of e`.
  change Additive.ofMul ((T.pathGroupEquivFreeGroup v hO).abelianizationCongr
    (Group.Abelianization.of (T.loop v e.1))) =
      Additive.ofMul (Group.Abelianization.of (FreeGroup.of e))
  rw [Group.abelianizationCongr_of, pathGroupEquivFreeGroup_loop]

/-- A free generator corresponds to the class of its tree loop. -/
@[simp] theorem abelianizationEquivFreeAbelianGroup_symm_of (hO : Γ.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    (T.abelianizationEquivFreeAbelianGroup v hO).symm (FreeAbelianGroup.of e) =
      Additive.ofMul (Group.Abelianization.of (T.loop v e.1)) := by
  rw [← T.abelianizationEquivFreeAbelianGroup_loop v hO, AddEquiv.symm_apply_apply]

/-- The free coordinates of a class in the abelianized path group are the coordinates of its
cycle class at the positive darts outside the tree. -/
theorem equivFinsupp_abelianizationEquivFreeAbelianGroup (hO : Γ.IsOrientation O)
    (x : Additive (Group.Abelianization (PathGroup Γ v))) :
    FreeAbelianGroup.equivFinsupp _ (T.abelianizationEquivFreeAbelianGroup v hO x) =
      Γ.cycleChordCoordinates O T.darts ℤ (T.abelianizationEquivCycle v hO x) := by
  obtain ⟨y, rfl⟩ := (T.abelianizationEquivFreeAbelianGroup v hO).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  induction y using FreeAbelianGroup.induction_on with
  | zero => simp
  | of e => simp
  | neg _ _ => simp_all
  | add _ _ h₁ h₂ => simp_all

/-- Change of spanning tree in free abelian coordinates: relative to a spanning tree `T'`, the
free generator of a positive dart `e` outside a spanning tree `T` has as coordinates the
coordinates of the cycle class of the `T`-loop through `e` at the positive darts outside `T'`. -/
theorem equivFinsupp_abelianizationEquivFreeAbelianGroup_symm_of (T' : Γ.SpanningTree)
    (hO : Γ.IsOrientation O) (e : ↥(O \ T.darts)) :
    FreeAbelianGroup.equivFinsupp _ (T'.abelianizationEquivFreeAbelianGroup v hO
        ((T.abelianizationEquivFreeAbelianGroup v hO).symm (FreeAbelianGroup.of e))) =
      Γ.cycleChordCoordinates O T'.darts ℤ (PathGroup.cycleClass hO ℤ (T.loop v e.1)).toAdd := by
  rw [abelianizationEquivFreeAbelianGroup_symm_of, equivFinsupp_abelianizationEquivFreeAbelianGroup,
    abelianizationEquivCycle_of]

variable {Δ : SerreGraph} {O' : Set Δ.E} {v}

/-- The free abelian coordinates of the abelianized path group are natural: a morphism carrying a
spanning tree `T` into a spanning tree `T'`, and the positive darts outside `T` to positive darts
outside `T'`, acts on free abelian coordinates by the induced map of generators. -/
theorem abelianizationEquivFreeAbelianGroup_map (T' : Δ.SpanningTree) {w : Δ.V} (f : Γ.Hom Δ)
    (hO : Γ.IsOrientation O) (hO' : Δ.IsOrientation O') (hT : ∀ e ∈ T.darts, f.mapE e ∈ T'.darts)
    (hf : Set.MapsTo f.mapE (O \ T.darts) (O' \ T'.darts)) (h : f.mapV v = w)
    (x : Additive (Group.Abelianization (PathGroup Γ v))) :
    T'.abelianizationEquivFreeAbelianGroup w hO'
        ((Group.Abelianization.map (PathGroup.map f h)).toAdditive x) =
      FreeAbelianGroup.map (Set.MapsTo.restrict f.mapE _ _ hf)
        (T.abelianizationEquivFreeAbelianGroup v hO x) := by
  obtain ⟨y, rfl⟩ := (T.abelianizationEquivFreeAbelianGroup v hO).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  induction y using FreeAbelianGroup.induction_on with
  | zero => simp
  | of e =>
    simpa [T.map_loop v f T' hT h] using
      T'.abelianizationEquivFreeAbelianGroup_loop w hO' (Set.MapsTo.restrict f.mapE _ _ hf e)
  | neg _ ih => simp_all
  | add _ _ ih₁ ih₂ => simp_all

end TauCeti.SerreGraph.SpanningTree
