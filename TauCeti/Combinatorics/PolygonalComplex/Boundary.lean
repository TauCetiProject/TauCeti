/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.SurfaceModel
public import TauCeti.Combinatorics.Quiver.StronglyConnectedComponent

/-!
# The boundary graph of a polygonal surface model

The boundary darts of a polygonal surface model are the darts whose edge lies on exactly one face
side. A vertex is a *boundary vertex* (`SurfaceModel.BoundaryVertex`) when some boundary dart
starts at it; the other vertices are the inner vertices. The boundary vertices and the boundary
darts form a Serre graph, the *boundary graph* `SurfaceModel.boundary` of the model: reversal
preserves boundary darts, and both ends of a boundary dart are boundary vertices. It is a subgraph
of the one-skeleton, through the inclusion `SurfaceModel.boundaryInclusion`.

Since the link of a boundary vertex is an interval, whose two ends are the boundary germs at that
vertex, the boundary graph is 2-regular: exactly two of its darts start at each of its vertices
(`SurfaceModel.card_boundary_src_fiber`). Hence it has twice as many darts as vertices, that is,
as many geometric edges as vertices (`SurfaceModel.card_boundary_E`).

The *boundary components* of the model (`SurfaceModel.BoundaryComponent`), the contours of
Gallier and Xu, are the path components of the boundary graph, and `SurfaceModel.boundaryClass`
sends a boundary dart to the component containing it. A dart, its reverse and the darts following
it lie in the same component, and every component contains a dart. A model has no boundary
component exactly when it has no boundary dart.

## Main definitions

* `TauCeti.SurfaceModel.BoundaryVertex`: the vertices at which a boundary dart starts.
* `TauCeti.SurfaceModel.boundary`: the Serre graph of boundary vertices and boundary darts.
* `TauCeti.SurfaceModel.boundaryInclusion`: the inclusion of the boundary graph into the
  one-skeleton.
* `TauCeti.SurfaceModel.BoundaryComponent`: the path components of the boundary graph.
* `TauCeti.SurfaceModel.boundaryClass`: the boundary component of a boundary dart.

## Main results

* `TauCeti.SurfaceModel.card_boundary_src_fiber`: exactly two boundary darts start at each
  boundary vertex.
* `TauCeti.SurfaceModel.card_boundary_E`: the boundary graph has twice as many darts as vertices.
* `TauCeti.SurfaceModel.boundaryClass_eq_boundaryClass_iff`: two boundary darts lie in the same
  boundary component exactly when a path of boundary darts joins their sources.
* `TauCeti.SurfaceModel.boundaryClass_surjective`: every boundary component contains a dart.
* `TauCeti.SurfaceModel.isEmpty_boundaryComponent_iff`: a model has no boundary component exactly
  when it has no boundary dart.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definitions 6.1, 6.2 (boundary vertices and boundary edges) and 6.4 (contours).
-/

public section

universe u v w

namespace TauCeti

namespace SurfaceModel

open Quiver (StronglyConnectedComponent)

variable (S : SurfaceModel.{u, v, w})

/-! ### The boundary graph -/

/-- The boundary vertices of a surface model: the vertices at which some boundary dart starts.
The other vertices, whose links are circles, are the inner vertices. -/
abbrev BoundaryVertex : Type u := {x : S.graph.V // (S.boundaryGerms x).Nonempty}

/-- The boundary graph of a surface model: its vertices are the boundary vertices and its darts
are the boundary darts, with the source and reversal of the one-skeleton. The vertex and dart
types are exposed, so that boundary vertices and boundary darts are vertices and darts of this
graph. -/
@[expose] def boundary : SerreGraph.{u, v} where
  V := S.BoundaryVertex
  E := S.boundaryDarts
  src e := ⟨S.graph.src e.1, e.1, mem_boundaryGerms_iff.2 ⟨e.2, rfl⟩⟩
  rev e := ⟨S.graph.rev e.1, rev_mem_boundaryDarts_iff.2 e.2⟩
  rev_rev e := Subtype.ext (S.graph.rev_rev e.1)
  rev_ne e he := S.graph.rev_ne e.1 (congrArg Subtype.val he)

variable {S}

@[simp] theorem boundary_src_val (e : S.boundary.E) :
    (S.boundary.src e).1 = S.graph.src e.1 := (rfl)

@[simp] theorem boundary_rev_val (e : S.boundary.E) :
    (S.boundary.rev e).1 = S.graph.rev e.1 := (rfl)

@[simp] theorem boundary_tgt_val (e : S.boundary.E) :
    (S.boundary.tgt e).1 = S.graph.tgt e.1 := (rfl)

variable (S)

/-- The inclusion of the boundary graph into the one-skeleton of the model. -/
@[expose] def boundaryInclusion : S.boundary.Hom S.graph where
  mapV := Subtype.val
  mapE := Subtype.val
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem boundaryInclusion_mapV (x : S.boundary.V) :
    S.boundaryInclusion.mapV x = x.1 := (rfl)

@[simp] theorem boundaryInclusion_mapE (e : S.boundary.E) :
    S.boundaryInclusion.mapE e = e.1 := (rfl)

/-- The inclusion of the boundary graph is injective on darts. -/
theorem boundaryInclusion_mapE_injective : Function.Injective S.boundaryInclusion.mapE :=
  Subtype.val_injective

/-- The boundary graph has finitely many vertices. -/
instance : Finite S.boundary.V := inferInstanceAs (Finite S.BoundaryVertex)

/-- The boundary graph has finitely many darts. -/
instance : Finite S.boundary.E := inferInstanceAs (Finite S.boundaryDarts)

/-- Every boundary vertex is the source of a boundary dart. -/
theorem boundary_src_surjective : Function.Surjective S.boundary.src := fun x => by
  obtain ⟨e, he⟩ := x.2
  rw [mem_boundaryGerms_iff] at he
  exact ⟨⟨e, he.1⟩, Subtype.ext he.2⟩

/-- The boundary darts starting at a boundary vertex are its boundary germs. -/
private def boundarySrcFiberEquiv (x : S.boundary.V) :
    {e : S.boundary.E // S.boundary.src e = x} ≃ S.boundaryGerms x.1 where
  toFun e := ⟨e.1.1, mem_boundaryGerms_iff.2 ⟨e.1.2, congrArg Subtype.val e.2⟩⟩
  invFun e := ⟨⟨e.1, (mem_boundaryGerms_iff.1 e.2).1⟩, Subtype.ext (mem_boundaryGerms_iff.1 e.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The boundary graph is 2-regular: exactly two boundary darts start at each boundary vertex,
the two ends of its interval link. -/
theorem card_boundary_src_fiber (x : S.boundary.V) :
    Nat.card {e : S.boundary.E // S.boundary.src e = x} = 2 := by
  rw [Nat.card_congr (S.boundarySrcFiberEquiv x), Nat.card_coe_set_eq]
  exact S.ncard_boundaryGerms_eq_two x.2

/-- The boundary graph has twice as many darts as vertices, hence as many geometric edges as
vertices. -/
theorem card_boundary_E : Nat.card S.boundary.E = 2 * Nat.card S.boundary.V := by
  have := Fintype.ofFinite S.boundary.V
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv S.boundary.src), Nat.card_sigma]
  simp [S.card_boundary_src_fiber, mul_comm]

/-- A surface model has no boundary vertex exactly when it has no boundary dart. -/
theorem isEmpty_boundary_V_iff : IsEmpty S.boundary.V ↔ S.boundaryDarts = ∅ := by
  refine ⟨fun _ => Set.isEmpty_coe_sort.1 (Function.isEmpty S.boundary.src), fun h => ⟨fun x => ?_⟩⟩
  obtain ⟨e, -⟩ := S.boundary_src_surjective x
  exact (Set.isEmpty_coe_sort.2 h).false e

/-! ### Boundary components -/

/-- The boundary components of a surface model: the classes of boundary vertices joined by a path
of boundary darts, that is, the strongly connected components of the boundary graph. -/
abbrev BoundaryComponent : Type u := StronglyConnectedComponent S.boundary.V

/-- The boundary component containing a boundary dart: the component of its source. -/
def boundaryClass (e : S.boundary.E) : S.BoundaryComponent :=
  StronglyConnectedComponent.mk (S.boundary.src e)

variable {S}

theorem boundaryClass_def (e : S.boundary.E) :
    S.boundaryClass e = StronglyConnectedComponent.mk (S.boundary.src e) := (rfl)

/-- Two boundary darts lie in the same boundary component exactly when a path of boundary darts
joins their sources. -/
theorem boundaryClass_eq_boundaryClass_iff {e e' : S.boundary.E} :
    S.boundaryClass e = S.boundaryClass e' ↔
      Nonempty (S.boundary.Path (S.boundary.src e) (S.boundary.src e')) :=
  StronglyConnectedComponent.mk_eq_mk_iff_nonempty_path

/-- A boundary dart lies in the boundary component of its target. -/
theorem boundaryClass_eq_mk_tgt (e : S.boundary.E) :
    S.boundaryClass e = StronglyConnectedComponent.mk (S.boundary.tgt e) :=
  StronglyConnectedComponent.mk_eq_mk_iff_nonempty_path.2 ⟨(S.boundary.dart e).toPath⟩

/-- A boundary dart and its reverse lie in the same boundary component. -/
@[simp] theorem boundaryClass_rev (e : S.boundary.E) :
    S.boundaryClass (S.boundary.rev e) = S.boundaryClass e := by
  rw [boundaryClass_eq_mk_tgt e, boundaryClass_def, SerreGraph.src_rev]

/-- A boundary dart and a boundary dart starting where it ends lie in the same boundary
component. -/
theorem boundaryClass_eq_of_tgt_eq_src {e e' : S.boundary.E}
    (h : S.boundary.tgt e = S.boundary.src e') : S.boundaryClass e = S.boundaryClass e' := by
  rw [boundaryClass_eq_mk_tgt, h, boundaryClass_def]

variable (S)

/-- Every boundary component contains a boundary dart. -/
theorem boundaryClass_surjective : Function.Surjective S.boundaryClass :=
  StronglyConnectedComponent.mk_surjective.comp S.boundary_src_surjective

/-- A surface model has no boundary component exactly when it has no boundary dart. -/
theorem isEmpty_boundaryComponent_iff : IsEmpty S.BoundaryComponent ↔ S.boundaryDarts = ∅ :=
  Quiver.isEmpty_stronglyConnectedComponent_iff.trans S.isEmpty_boundary_V_iff

end SurfaceModel

end TauCeti
