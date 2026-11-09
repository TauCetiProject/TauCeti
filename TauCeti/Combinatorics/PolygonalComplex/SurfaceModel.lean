/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Basic
public import Mathlib.Data.Set.Card

/-!
# Polygonal surface models

A polygonal surface model is a polygonal complex with finitely many faces, a nonempty connected
one-skeleton, and a surface link at every vertex: the link of each vertex is a finite circle or
a finite interval. Its realization is then a compact connected surface, possibly with boundary;
this file works only with the combinatorial incidence data and uses no topology.

The local link condition has global consequences for the incidence of faces and edges. Since the
degree of a germ `e` in its link counts the face sides along `e` or its reverse, every geometric
edge lies on one or two face sides (`SurfaceModel.sideCount_rev_add_sideCount_eq_one_or_two`).
The darts whose edge lies on a single face side are the boundary darts
(`SurfaceModel.boundaryDarts`), and they are exactly the germs of degree one in the links.
Consequently every vertex meeting the boundary has exactly two boundary germs, the two ends of
its interval link (`SurfaceModel.ncard_boundaryGerms_eq_two`). Finiteness of the faces also gives
finiteness of the darts and of the vertices, since each of them occurs on a face.

## Main definitions

* `TauCeti.SurfaceModel`: a finite connected polygonal complex with surface links.
* `TauCeti.SurfaceModel.boundaryDarts`: the darts whose edge lies on exactly one face side.
* `TauCeti.SurfaceModel.boundaryGerms`: the boundary darts starting at a vertex.

## Main results

* `TauCeti.SurfaceModel.sideCount_rev_add_sideCount_eq_one_or_two`: every geometric edge lies on
  one or two face sides.
* `TauCeti.SurfaceModel.notMem_boundaryDarts_iff`: an edge not on the boundary lies on exactly two
  face sides.
* `TauCeti.SurfaceModel.linkDegree_eq_one_iff_mem_boundaryDarts`: boundary darts are the germs of
  degree one.
* `TauCeti.SurfaceModel.ncard_boundaryGerms_eq_two`: every boundary vertex has exactly two
  boundary germs.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definitions 6.1, 6.2 and 6.4.
-/

public section

universe u v w

namespace TauCeti

/-- A polygonal surface model: a polygonal complex with finitely many faces whose one-skeleton is
nonempty and connected, and in which the link of every vertex is a finite circle or a finite
interval. The vertices and darts are then finite as well (`SurfaceModel.instFiniteE`,
`SurfaceModel.instFiniteV`). -/
structure SurfaceModel extends PolygonalComplex.{u, v, w} where
  /-- There are finitely many faces. -/
  [finite_face : Finite Face]
  /-- The one-skeleton is nonempty and connected. -/
  connected : graph.Connected
  /-- The link of every vertex is a finite circle or a finite interval. -/
  hasSurfaceLink : ∀ v, toPolygonalComplex.HasSurfaceLink v

namespace SurfaceModel

attribute [instance] finite_face

variable (S : SurfaceModel.{u, v, w})

/-- Every germ of a surface model has degree one or two in its link. -/
theorem linkDegree_eq_one_or_two (e : S.graph.E) : S.linkDegree e = 1 ∨ S.linkDegree e = 2 :=
  (S.hasSurfaceLink _).linkDegree_eq_one_or_two

/-- Every geometric edge of a surface model lies on one or two face sides. -/
theorem sideCount_rev_add_sideCount_eq_one_or_two (e : S.graph.E) :
    S.sideCount (S.graph.rev e) + S.sideCount e = 1 ∨
      S.sideCount (S.graph.rev e) + S.sideCount e = 2 := by
  rw [← S.linkDegree_eq_sideCount_rev_add_sideCount]
  exact S.linkDegree_eq_one_or_two e

/-- Every dart of a surface model, or its reverse, is attached to a face side. -/
theorem exists_outgoing_eq (e : S.graph.E) :
    ∃ c : S.Corner, S.outgoing c = e ∨ S.outgoing c = S.graph.rev e := by
  have h := S.sideCount_rev_add_sideCount_eq_one_or_two e
  rcases Nat.eq_zero_or_pos (S.sideCount e) with he | he
  · have hpos : 0 < S.sideCount (S.graph.rev e) := by omega
    obtain ⟨c, hc⟩ := S.sideCount_pos_iff.1 hpos
    exact ⟨c, .inr hc⟩
  · obtain ⟨c, hc⟩ := S.sideCount_pos_iff.1 he
    exact ⟨c, .inl hc⟩

/-- A surface model has finitely many darts: each of them lies, up to reversal, on a face side. -/
instance instFiniteE : Finite S.graph.E :=
  Finite.of_surjective
    (fun p : S.Corner × Bool => cond p.2 (S.outgoing p.1) (S.graph.rev (S.outgoing p.1)))
    fun e => by
      obtain ⟨c, hc | hc⟩ := S.exists_outgoing_eq e
      · exact ⟨(c, true), by simp [hc]⟩
      · exact ⟨(c, false), by simp [hc]⟩

/-- A surface model has finitely many vertices: each of them has a nonempty link, hence is the
source of a dart. -/
instance instFiniteV : Finite S.graph.V :=
  Finite.of_surjective S.graph.src fun v => by
    obtain ⟨-, hconn, -⟩ := (S.hasSurfaceLink_iff v).1 (S.hasSurfaceLink v)
    obtain ⟨⟨⟨e, he⟩⟩, -⟩ := ((S.vertexLink v).connected_iff).1 hconn
    exact ⟨e, he⟩

/-! ### Boundary darts -/

/-- The boundary darts of a surface model: the darts whose geometric edge lies on exactly one face
side. -/
def boundaryDarts : Set S.graph.E := {e | S.sideCount (S.graph.rev e) + S.sideCount e = 1}

variable {S} in
theorem mem_boundaryDarts_iff {e : S.graph.E} :
    e ∈ S.boundaryDarts ↔ S.sideCount (S.graph.rev e) + S.sideCount e = 1 :=
  Iff.rfl

variable {S} in
/-- An edge of a surface model that is not on the boundary lies on exactly two face sides. -/
theorem notMem_boundaryDarts_iff {e : S.graph.E} :
    e ∉ S.boundaryDarts ↔ S.sideCount (S.graph.rev e) + S.sideCount e = 2 := by
  have := S.sideCount_rev_add_sideCount_eq_one_or_two e
  rw [mem_boundaryDarts_iff]
  omega

variable {S} in
@[simp] theorem rev_mem_boundaryDarts_iff {e : S.graph.E} :
    S.graph.rev e ∈ S.boundaryDarts ↔ e ∈ S.boundaryDarts := by
  rw [mem_boundaryDarts_iff, mem_boundaryDarts_iff, SerreGraph.rev_rev, add_comm]

variable {S} in
/-- The boundary darts are exactly the germs of degree one in their links. -/
theorem linkDegree_eq_one_iff_mem_boundaryDarts {e : S.graph.E} :
    S.linkDegree e = 1 ↔ e ∈ S.boundaryDarts := by
  rw [mem_boundaryDarts_iff, S.linkDegree_eq_sideCount_rev_add_sideCount]

variable {S} in
/-- A dart which is not on the boundary has degree two in its link. -/
theorem linkDegree_eq_two_iff_notMem_boundaryDarts {e : S.graph.E} :
    S.linkDegree e = 2 ↔ e ∉ S.boundaryDarts := by
  rw [notMem_boundaryDarts_iff, S.linkDegree_eq_sideCount_rev_add_sideCount]

/-- The boundary germs at a vertex `v`: the boundary darts starting at `v`. -/
def boundaryGerms (v : S.graph.V) : Set S.graph.E := {e ∈ S.boundaryDarts | S.graph.src e = v}

variable {S} in
@[simp] theorem mem_boundaryGerms_iff {v : S.graph.V} {e : S.graph.E} :
    e ∈ S.boundaryGerms v ↔ e ∈ S.boundaryDarts ∧ S.graph.src e = v :=
  Iff.rfl

/-- Every vertex of a surface model that meets the boundary has exactly two boundary germs: the
two ends of its interval link. -/
theorem ncard_boundaryGerms_eq_two {v : S.graph.V} (h : (S.boundaryGerms v).Nonempty) :
    (S.boundaryGerms v).ncard = 2 := by
  have hset : S.boundaryGerms v = {e | S.graph.src e = v ∧ S.linkDegree e = 1} := by
    ext e
    rw [mem_boundaryGerms_iff, ← linkDegree_eq_one_iff_mem_boundaryDarts, and_comm]
    rfl
  rw [hset]
  rcases (S.hasSurfaceLink v).eq_empty_or_eq_pair with hempty | ⟨e₁, e₂, hne, heq⟩
  · rw [hset, hempty] at h
    exact absurd h Set.not_nonempty_empty
  · rw [heq, Set.ncard_pair hne]

end SurfaceModel

end TauCeti
