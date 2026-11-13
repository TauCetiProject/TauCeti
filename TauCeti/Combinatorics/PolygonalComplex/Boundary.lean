/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Circuit
public import TauCeti.Combinatorics.PolygonalComplex.SurfaceModel
public import TauCeti.Combinatorics.Quiver.StronglyConnectedComponent

import Mathlib.Data.List.NodupEquivFin

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

Every boundary component is traversed by a circuit. A *boundary circuit* of a component `b`
(`SurfaceModel.BoundaryCircuit`) is a closed path of boundary darts traversing every geometric edge
of `b` exactly once, in one of its two directions; it is nonempty and cyclically reduced, and its
length is the number of edges of `b`. Every boundary component has one
(`SurfaceModel.boundaryCircuit_exists`), since the boundary graph is finite and 2-regular.

## Main definitions

* `TauCeti.SurfaceModel.BoundaryVertex`: the vertices at which a boundary dart starts.
* `TauCeti.SurfaceModel.boundary`: the Serre graph of boundary vertices and boundary darts.
* `TauCeti.SurfaceModel.boundaryInclusion`: the inclusion of the boundary graph into the
  one-skeleton.
* `TauCeti.SurfaceModel.BoundaryComponent`: the path components of the boundary graph.
* `TauCeti.SurfaceModel.boundaryClass`: the boundary component of a boundary dart.
* `TauCeti.SurfaceModel.BoundaryCircuit`: a closed path traversing every edge of a boundary
  component exactly once.

## Main results

* `TauCeti.SurfaceModel.card_boundary_src_fiber`: exactly two boundary darts start at each
  boundary vertex.
* `TauCeti.SurfaceModel.card_boundary_E`: the boundary graph has twice as many darts as vertices.
* `TauCeti.SurfaceModel.boundaryClass_eq_boundaryClass_iff`: two boundary darts lie in the same
  boundary component exactly when a path of boundary darts joins their sources.
* `TauCeti.SurfaceModel.boundaryClass_surjective`: every boundary component contains a dart.
* `TauCeti.SurfaceModel.isEmpty_boundaryComponent_iff`: a model has no boundary component exactly
  when it has no boundary dart.
* `TauCeti.SurfaceModel.boundaryCircuit_exists`: every boundary component is traversed by a
  boundary circuit.
* `TauCeti.SurfaceModel.BoundaryCircuit.two_mul_length`: a boundary circuit traverses one dart for
  each edge of its component.

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

/-! ### Boundary circuits -/

/-- A boundary circuit of the boundary component `b`: a closed path of boundary darts which
traverses every geometric edge of `b` exactly once, in one of its two directions. It is a based,
oriented traversal of the contour `b`: the base vertex and the direction are part of the data. Its
base vertex lies in `b` (`BoundaryCircuit.mk_base`), and the circuit is nonempty and cyclically
reduced (`BoundaryCircuit.length_pos`, `BoundaryCircuit.isCyclicallyReduced`). -/
structure BoundaryCircuit (b : S.BoundaryComponent) where
  /-- The vertex at which the circuit starts and ends. -/
  base : S.boundary.V
  /-- The closed path of boundary darts. -/
  path : S.boundary.Path base base
  /-- The circuit traverses each geometric edge at most once. -/
  nodup_map_toGeomEdge_darts : ((SerreGraph.Path.darts _ path).map S.boundary.toGeomEdge).Nodup
  /-- The circuit traverses every geometric edge of the component `b`. -/
  toGeomEdge_mem_map_darts : ∀ e, S.boundaryClass e = b →
    S.boundary.toGeomEdge e ∈ (SerreGraph.Path.darts _ path).map S.boundary.toGeomEdge

namespace BoundaryCircuit

variable {S} {b : S.BoundaryComponent} (c : S.BoundaryCircuit b)

/-- A boundary circuit traverses each dart at most once. -/
theorem nodup_darts : (SerreGraph.Path.darts _ c.path).Nodup :=
  c.nodup_map_toGeomEdge_darts.of_map _

private theorem boundaryClass_eq_mk_base {e : S.boundary.E}
    (he : e ∈ SerreGraph.Path.darts _ c.path) :
    S.boundaryClass e = StronglyConnectedComponent.mk c.base := by
  obtain ⟨q, -, -⟩ := SerreGraph.Path.exists_eq_cons_comp_of_mem_darts _ c.path he
  rw [boundaryClass_def, StronglyConnectedComponent.mk_eq_mk_iff_nonempty_path]
  exact ⟨q.reverse⟩

/-- A boundary circuit of `b` traverses every edge of `b`, in one of its two directions. -/
theorem mem_darts_or_rev_mem_darts {e : S.boundary.E} (he : S.boundaryClass e = b) :
    e ∈ SerreGraph.Path.darts _ c.path ∨ S.boundary.rev e ∈ SerreGraph.Path.darts _ c.path := by
  obtain ⟨d, hd, hde⟩ := List.mem_map.1 (c.toGeomEdge_mem_map_darts e he)
  rcases S.boundary.toGeomEdge_eq_toGeomEdge_iff.1 hde with rfl | rfl
  · exact .inl hd
  · exact .inr (by rwa [SerreGraph.rev_rev])

/-- A boundary circuit of `b` starts in `b`. -/
theorem mk_base : StronglyConnectedComponent.mk c.base = b := by
  obtain ⟨e, he⟩ := S.boundaryClass_surjective b
  rcases c.mem_darts_or_rev_mem_darts he with h | h
  · exact (c.boundaryClass_eq_mk_base h).symm.trans he
  · exact (c.boundaryClass_eq_mk_base h).symm.trans ((boundaryClass_rev e).trans he)

/-- Every dart of a boundary circuit of `b` lies in `b`. -/
theorem boundaryClass_eq_of_mem_darts {e : S.boundary.E}
    (he : e ∈ SerreGraph.Path.darts _ c.path) : S.boundaryClass e = b :=
  (c.boundaryClass_eq_mk_base he).trans c.mk_base

/-- A boundary circuit never traverses both directions of an edge. -/
theorem rev_notMem_darts {e : S.boundary.E} (he : e ∈ SerreGraph.Path.darts _ c.path) :
    S.boundary.rev e ∉ SerreGraph.Path.darts _ c.path := fun hr =>
  S.boundary.rev_ne e <|
    List.inj_on_of_nodup_map c.nodup_map_toGeomEdge_darts hr he (S.boundary.toGeomEdge_rev e)

/-- A boundary circuit of `b` traverses exactly one of the two directions of each edge of `b`. -/
theorem rev_mem_darts_iff {e : S.boundary.E} (he : S.boundaryClass e = b) :
    S.boundary.rev e ∈ SerreGraph.Path.darts _ c.path ↔ e ∉ SerreGraph.Path.darts _ c.path :=
  ⟨fun hr hm => c.rev_notMem_darts hm hr, (c.mem_darts_or_rev_mem_darts he).resolve_left⟩

/-- A boundary circuit of `b` traverses every edge of `b` exactly once, in one of its two
directions. -/
theorem count_add_count_rev_eq_one [DecidableEq S.boundary.E] {e : S.boundary.E}
    (he : S.boundaryClass e = b) :
    (SerreGraph.Path.darts _ c.path).count e +
      (SerreGraph.Path.darts _ c.path).count (S.boundary.rev e) = 1 := by
  by_cases hm : e ∈ SerreGraph.Path.darts _ c.path
  · rw [List.count_eq_one_of_mem c.nodup_darts hm,
      List.count_eq_zero_of_not_mem (c.rev_notMem_darts hm)]
  · rw [List.count_eq_zero_of_not_mem hm,
      List.count_eq_one_of_mem c.nodup_darts ((c.rev_mem_darts_iff he).2 hm)]

/-- A boundary circuit is cyclically reduced. -/
theorem isCyclicallyReduced : SerreGraph.Path.IsCyclicallyReduced _ c.path :=
  SerreGraph.Path.isCyclicallyReduced_of_nodup_map_toGeomEdge_darts _ c.nodup_map_toGeomEdge_darts

/-- A boundary circuit of `b` traverses one dart for each edge of `b`: its length is half the
number of boundary darts in `b`. -/
theorem two_mul_length :
    2 * c.path.length = Nat.card {e : S.boundary.E // S.boundaryClass e = b} := by
  classical
  -- The darts of `b` are the darts of the circuit and their reverses.
  let f : {d // d ∈ SerreGraph.Path.darts _ c.path} ⊕ {d // d ∈ SerreGraph.Path.darts _ c.path} →
      {e : S.boundary.E // S.boundaryClass e = b} :=
    Sum.elim (fun d => ⟨d, c.boundaryClass_eq_of_mem_darts d.2⟩)
      (fun d => ⟨S.boundary.rev d, by rw [boundaryClass_rev, c.boundaryClass_eq_of_mem_darts d.2]⟩)
  have hf : Function.Bijective f := by
    refine ⟨Function.Injective.sumElim (fun d d' h => Subtype.ext (Subtype.mk.inj h))
      (fun d d' h => Subtype.ext (S.boundary.rev_injective (Subtype.mk.inj h)))
      fun d d' h => c.rev_notMem_darts d'.2 ?_, fun e => ?_⟩
    · rw [← Subtype.mk.inj h]
      exact d.2
    · rcases c.mem_darts_or_rev_mem_darts e.2 with h | h
      · exact ⟨.inl ⟨e, h⟩, rfl⟩
      · exact ⟨.inr ⟨_, h⟩, Subtype.ext (S.boundary.rev_rev e)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum,
    ← Nat.card_congr c.nodup_darts.getEquiv, Nat.card_fin, SerreGraph.Path.length_darts, two_mul]

/-- A boundary circuit is a nonempty path. -/
theorem length_pos : 0 < c.path.length := by
  obtain ⟨e, he⟩ := S.boundary_src_surjective c.base
  have := c.toGeomEdge_mem_map_darts e (by rw [boundaryClass_def, he, c.mk_base])
  rw [← SerreGraph.Path.length_darts, ← List.length_map (f := S.boundary.toGeomEdge)]
  exact List.length_pos_of_mem this

end BoundaryCircuit

/-- Every boundary component of a surface model has a boundary circuit: a closed path traversing
each of its edges exactly once. -/
theorem boundaryCircuit_exists (b : S.BoundaryComponent) : Nonempty (S.BoundaryCircuit b) := by
  obtain ⟨x, rfl⟩ := StronglyConnectedComponent.mk_surjective b
  obtain ⟨p, hnodup, hmem⟩ :=
    SerreGraph.exists_path_nodup_map_toGeomEdge_darts_and_mem S.card_boundary_src_fiber x
  refine ⟨⟨x, p, hnodup, fun e he => hmem e ?_⟩⟩
  rw [boundaryClass_def] at he
  obtain ⟨q⟩ := StronglyConnectedComponent.mk_eq_mk_iff_nonempty_path.1 he
  exact ⟨q.reverse⟩

end SurfaceModel

end TauCeti
