/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.Functoriality
public import TauCeti.GroupTheory.GraphOfGroups.PathGroup

/-!
# Naturality of the free basis of tree loops

A spanning tree `T` and an orientation `O` of a Serre graph identify its reduced path group with
the free group on the positive darts outside `T`, a generator corresponding to its tree loop.
These free coordinates are compatible with the functoriality of the reduced path group:

* they do not depend on the base vertex, once base vertices are compared along tree paths;
* a morphism of Serre graphs carrying a spanning tree into a spanning tree and positive non-tree
  darts to positive non-tree darts acts on free coordinates by the induced map of generators;
* in particular the inclusion of a subgraph containing the spanning tree is, in free
  coordinates, the inclusion of the free group on the positive non-tree darts of the subgraph.

## References

* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §6, Lemma 6.1.
-/

public section

namespace TauCeti.SerreGraph.SpanningTree

universe u w u' w'

variable {Γ : SerreGraph.{u, w}} {Δ : SerreGraph.{u', w'}} (T : Γ.SpanningTree)
  {O : Set Γ.E} (hO : Γ.IsOrientation O)

/-- The free coordinates of a reduced loop relative to a spanning tree are unchanged by moving
the base vertex along a tree path. -/
@[simp] theorem pathGroupEquivFreeGroup_mulEquivOfPath_path (v w : Γ.V) (g : PathGroup Γ v) :
    T.pathGroupEquivFreeGroup w hO (PathGroup.mulEquivOfPath (T.path v w) g) =
      T.pathGroupEquivFreeGroup v hO g := by
  have key : ((T.pathGroupEquivFreeGroup w hO).toMonoidHom.comp
      (PathGroup.mulEquivOfPath (T.path v w)).toMonoidHom).comp
        (T.pathGroupEquivFreeGroup v hO).symm.toMonoidHom = MonoidHom.id _ := by
    ext e
    simp
  simpa using DFunLike.congr_fun key (T.pathGroupEquivFreeGroup v hO g)

/-- A morphism of Serre graphs carrying a spanning tree `T` into a spanning tree `T'`, and the
positive darts outside `T` to positive darts outside `T'`, acts on free coordinates by the
induced map of free generators. -/
theorem pathGroupEquivFreeGroup_map (f : Γ.Hom Δ) (T' : Δ.SpanningTree) {O' : Set Δ.E}
    (hO' : Δ.IsOrientation O') (hT : ∀ e ∈ T.darts, f.mapE e ∈ T'.darts)
    (hf : Set.MapsTo f.mapE (O \ T.darts) (O' \ T'.darts)) {v : Γ.V} {w : Δ.V}
    (h : f.mapV v = w) (g : PathGroup Γ v) :
    T'.pathGroupEquivFreeGroup w hO' (PathGroup.map f h g) =
      FreeGroup.map (Set.MapsTo.restrict f.mapE _ _ hf) (T.pathGroupEquivFreeGroup v hO g) := by
  have key : ((T'.pathGroupEquivFreeGroup w hO').toMonoidHom.comp (PathGroup.map f h)).comp
      (T.pathGroupEquivFreeGroup v hO).symm.toMonoidHom =
        FreeGroup.map (Set.MapsTo.restrict f.mapE _ _ hf) := by
    ext e
    simpa [T.map_loop v f T' hT h] using
      T'.pathGroupEquivFreeGroup_loop w hO' (Set.MapsTo.restrict f.mapE _ _ hf e)
  simpa using DFunLike.congr_fun key (T.pathGroupEquivFreeGroup v hO g)

/-- In free coordinates, the inclusion of a subgraph containing a spanning tree is the inclusion
of the free group on the positive non-tree darts of the subgraph. -/
theorem pathGroupEquivFreeGroup_map_restrictInclusion (S : Set Γ.E)
    (hS : ∀ e ∈ S, Γ.rev e ∈ S) (hTS : T.darts ⊆ S) {O' : Set (Γ.restrict S hS).E}
    (hO' : (Γ.restrict S hS).IsOrientation O') (hOO' : ∀ e ∈ O', e.1 ∈ O) {v w : Γ.V}
    (h : (Γ.restrictInclusion S hS).mapV v = w) (g : PathGroup (Γ.restrict S hS) v) :
    T.pathGroupEquivFreeGroup w hO (PathGroup.map (Γ.restrictInclusion S hS) h g) =
      FreeGroup.map (fun e : ↥(O' \ (T.restrict S hS hTS).darts) =>
          (⟨e.1.1, hOO' e.1 e.2.1, fun he => e.2.2 ((T.mem_restrict_darts S hS hTS).mpr he)⟩ :
            ↥(O \ T.darts)))
        ((T.restrict S hS hTS).pathGroupEquivFreeGroup v hO' g) :=
  (T.restrict S hS hTS).pathGroupEquivFreeGroup_map hO' (Γ.restrictInclusion S hS) T hO
    (fun _ he => (T.mem_restrict_darts S hS hTS).mp he)
    (fun e he => ⟨hOO' e he.1, fun he' => he.2 ((T.mem_restrict_darts S hS hTS).mpr he')⟩) h g

end TauCeti.SerreGraph.SpanningTree
