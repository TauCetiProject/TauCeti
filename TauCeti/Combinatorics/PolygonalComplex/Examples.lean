/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.SingleFace
public import TauCeti.Combinatorics.PolygonalComplex.SurfaceModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Basic polygonal surface models

This file builds the standard surface models from the single-face complexes of
`TauCeti.Combinatorics.PolygonalComplex.SingleFace`: the disc `a`, the torus `a b a⁻¹ b⁻¹` and the
projective plane `a a`, each a one-vertex polygon `PolygonalComplex.polygon w`. The sphere is the
digon `a a⁻¹` on the segment, with two vertices. For each model the file checks the surface links
and the Euler characteristic. It also separates the disc from the closed models by their boundary
darts, and the torus from the projective plane by orientability.

It also records how the surface-link condition fails at a pinched vertex. On the one-petal rose,
any family of faces `a a⁻¹` (`PolygonalComplex.digons`) has a disconnected vertex link: every
corner is a loop at `a` or at `a⁻¹`. For one face this is the sphere with two points identified.
For infinitely many faces the link is moreover infinite, and every germ then has
`Nat.card`-degree zero.

## Main definitions

* `TauCeti.PolygonalComplex.digons`: a family of faces `a a⁻¹` on the one-petal rose.
* `TauCeti.SurfaceModel.disc`, `TauCeti.SurfaceModel.torus`,
  `TauCeti.SurfaceModel.projectivePlane`, `TauCeti.SurfaceModel.sphere`: the standard models.

## Main results

* `TauCeti.SurfaceModel.eulerChar_disc`, `TauCeti.SurfaceModel.eulerChar_torus`,
  `TauCeti.SurfaceModel.eulerChar_projectivePlane`, `TauCeti.SurfaceModel.eulerChar_sphere`: the
  Euler characteristics `1`, `0`, `1` and `2`.
* `TauCeti.SurfaceModel.isOrientable_torus`,
  `TauCeti.SurfaceModel.not_isOrientable_projectivePlane`: the torus is orientable and the
  projective plane is not.
* `TauCeti.SurfaceModel.boundaryDarts_disc`, `TauCeti.SurfaceModel.boundaryDarts_torus`,
  `TauCeti.SurfaceModel.boundaryDarts_projectivePlane`, `TauCeti.SurfaceModel.boundaryDarts_sphere`:
  both darts of the disc are boundary darts, while the closed models have no boundary.
* `TauCeti.PolygonalComplex.not_hasSurfaceLink_digons`: the vertex of any family of faces `a a⁻¹` on
  the one-petal rose has no surface link (for example, the sphere with two points identified).

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6.
-/

public section

universe u v

namespace TauCeti

namespace PolygonalComplex

/-! ### Pinched vertices -/

/-- A family of faces `a a⁻¹`, indexed by `ι`, on the one-petal rose `a`. -/
abbrev digons (ι : Type u) : PolygonalComplex.{0, 0, u} where
  graph := SerreGraph.rose Unit
  Face := ι
  sides _ := 2
  sides_pos _ := two_pos
  side _ i := [((), true), ((), false)][i]
  tgt_side _ _ := rfl

/-- The link of the vertex of `digons ι` consists of loops only: every corner has equal germs. -/
private theorem digons_src_eq_src_rev (ι : Type u) {v : (digons ι).graph.V}
    (d : ((digons ι).vertexLink v).E) :
    (((digons ι).vertexLink v).src d).1 = (((digons ι).vertexLink v).src (d.1, !d.2)).1 := by
  obtain ⟨⟨⟨f, k⟩, -⟩, b⟩ := d
  fin_cases k <;> cases b <;> simp only [vertexLink_src_true, vertexLink_src_false,
    Bool.not_true, Bool.not_false, outgoing_def, incoming_def] <;> rfl

/-- On the one-petal rose, faces `a a⁻¹` never give a surface link: the link of the vertex consists
of loops at `a` and at `a⁻¹`, so it is not connected. This includes the sphere with two points
identified, for a single face, and also an empty family. -/
theorem not_hasSurfaceLink_digons (ι : Type u) (v : (digons ι).graph.V) :
    ¬(digons ι).HasSurfaceLink v := fun h => by
  obtain ⟨-, hconn, -⟩ := ((digons ι).hasSurfaceLink_iff v).1 h
  obtain ⟨-, hpre⟩ := ((digons ι).vertexLink v).connected_iff.1 hconn
  obtain ⟨p⟩ := ((digons ι).vertexLink v).preconnected_iff.1 hpre ⟨((), true), rfl⟩
    ⟨((), false), rfl⟩
  have := SerreGraph.eq_of_path_of_forall_src_eq_tgt _
    (fun d => Subtype.ext (digons_src_eq_src_rev ι d)) p
  exact (SerreGraph.rose Unit).rev_ne ((), true) (congrArg Subtype.val this).symm

/-- For infinitely many faces the vertex link of `digons ι` is infinite. -/
theorem not_finite_vertexLink_digons (ι : Type u) [Infinite ι] (v : (digons ι).graph.V) :
    ¬Finite ((digons ι).vertexLink v).E := by
  rw [not_finite_iff_infinite]
  exact Infinite.of_injective (fun f : ι => (⟨⟨f, 0⟩, rfl⟩, true))
    fun f f' h => congrArg (fun d => d.1.1.1) h

/-- For infinitely many faces, every germ of `digons ι` has infinitely many link darts, so its
`Nat.card`-degree is zero. -/
theorem linkDegree_digons (ι : Type u) [Infinite ι] (e : (digons ι).graph.E) :
    (digons ι).linkDegree e = 0 := by
  rw [linkDegree_def]
  have : Infinite {d : ((digons ι).vertexLink ((digons ι).graph.src e)).E //
      (((digons ι).vertexLink _).src d).1 = e} := by
    obtain ⟨⟨⟩, _ | _⟩ := e
    · exact Infinite.of_injective
        (fun f : ι => ⟨(⟨⟨f, 1⟩, rfl⟩, true), (vertexLink_src_true _ _).trans (outgoing_def _ _)⟩)
        fun f f' h => congrArg (fun d => d.1.1.1.1) h
    · exact Infinite.of_injective
        (fun f : ι => ⟨(⟨⟨f, 0⟩, rfl⟩, true), (vertexLink_src_true _ _).trans (outgoing_def _ _)⟩)
        fun f f' h => congrArg (fun d => d.1.1.1.1) h
  exact Nat.card_eq_zero_of_infinite

end PolygonalComplex

open PolygonalComplex

namespace SurfaceModel

/-! The models below are plain definitions. The proofs about their darts apply the `polygon` and
`singleFace` lemmas directly, unfolding each model to its underlying complex: the dart type
`S.graph.E` depends on the complex, which blocks rewriting along `disc_toPolygonalComplex` and its
analogues. -/

/-! ### The disc -/

/-- The disc: one petal `a` and a single face attached along `a`. -/
def disc : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := polygon [((), true)] (List.cons_ne_nil _ _)
  connected := SerreGraph.rose_connected Unit
  hasSurfaceLink := hasSurfaceLink_polygon ((), true)
    (fun ⟨⟨⟩, b⟩ => by
      cases b
      · exact nonempty_vertexLink_path_polygon ⟨((), false), rfl⟩ ⟨0, by decide⟩ rfl rfl ⟨.nil⟩
      · exact ⟨.nil⟩)
    (.inr ⟨((), true), ((), false), by decide, by decide, by decide, by decide⟩)

theorem disc_toPolygonalComplex :
    disc.toPolygonalComplex = polygon [((), true)] (List.cons_ne_nil _ _) := (rfl)

/-- The disc has Euler characteristic `1`: one vertex, one edge and one face. -/
theorem eulerChar_disc : disc.eulerChar = 1 := by
  rw [disc_toPolygonalComplex, eulerChar_polygon, Nat.card_unique]
  norm_num

/-- Both darts of the disc are boundary darts: its single edge lies on one face side. -/
theorem boundaryDarts_disc : disc.boundaryDarts = Set.univ :=
  Set.eq_univ_of_forall fun e => linkDegree_eq_one_iff_mem_boundaryDarts.1 <|
    (linkDegree_polygon (α := Unit) [((), true)] (List.cons_ne_nil _ _) e).trans <| by
      obtain ⟨⟨⟩, _ | _⟩ := e <;> decide

/-! ### The torus -/

/-- The torus: two petals `a`, `b` and a single face attached along `a b a⁻¹ b⁻¹`. -/
def torus : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := polygon (α := Fin 2) [(0, true), (1, true), (0, false), (1, false)]
    (List.cons_ne_nil _ _)
  connected := SerreGraph.rose_connected (Fin 2)
  hasSurfaceLink := hasSurfaceLink_polygon (0, true)
    (fun ⟨i, b⟩ => by
      -- The link is the cycle `a, b, a⁻¹, b⁻¹`, through the corners at positions `0, 1, 2`.
      fin_cases i <;> cases b
      · exact nonempty_vertexLink_path_polygon ⟨(1, true), rfl⟩ ⟨0, by decide⟩ rfl rfl <|
          nonempty_vertexLink_path_polygon ⟨(0, false), rfl⟩ ⟨1, by decide⟩ rfl rfl ⟨.nil⟩
      · exact ⟨.nil⟩
      · exact nonempty_vertexLink_path_polygon ⟨(1, true), rfl⟩ ⟨0, by decide⟩ rfl rfl <|
          nonempty_vertexLink_path_polygon ⟨(0, false), rfl⟩ ⟨1, by decide⟩ rfl rfl <|
          nonempty_vertexLink_path_polygon ⟨(1, false), rfl⟩ ⟨2, by decide⟩ rfl rfl ⟨.nil⟩
      · exact nonempty_vertexLink_path_polygon ⟨(1, true), rfl⟩ ⟨0, by decide⟩ rfl rfl ⟨.nil⟩)
    (.inl fun ⟨i, b⟩ => by fin_cases i <;> cases b <;> decide)

theorem torus_toPolygonalComplex :
    torus.toPolygonalComplex =
      polygon (α := Fin 2) [(0, true), (1, true), (0, false), (1, false)] (List.cons_ne_nil _ _) :=
  (rfl)

/-- The torus has Euler characteristic `0`: one vertex, two edges and one face. -/
theorem eulerChar_torus : torus.eulerChar = 0 := by
  rw [torus_toPolygonalComplex, eulerChar_polygon, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

/-- The torus has no boundary: each of its two edges lies on two face sides. -/
theorem boundaryDarts_torus : torus.boundaryDarts = ∅ :=
  Set.eq_empty_of_forall_notMem fun e => linkDegree_eq_two_iff_notMem_boundaryDarts.1 <|
    (linkDegree_polygon (α := Fin 2) [(0, true), (1, true), (0, false), (1, false)]
      (List.cons_ne_nil _ _) e).trans <| by
      obtain ⟨i, b⟩ := e
      fin_cases i <;> cases b <;> decide

/-- The torus is orientable: with its face kept as given, the two sides along each edge traverse
it in opposite directions. -/
theorem isOrientable_torus : torus.IsOrientable :=
  isOrientable_polygon (hw := List.cons_ne_nil _ _) (by decide)

/-! ### The projective plane -/

/-- The projective plane: one petal `a` and a single face attached along `a a`. -/
def projectivePlane : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := polygon [((), true), ((), true)] (List.cons_ne_nil _ _)
  connected := SerreGraph.rose_connected Unit
  hasSurfaceLink := hasSurfaceLink_polygon ((), true)
    (fun ⟨⟨⟩, b⟩ => by
      cases b
      · exact nonempty_vertexLink_path_polygon ⟨((), false), rfl⟩ ⟨0, by decide⟩ rfl rfl ⟨.nil⟩
      · exact ⟨.nil⟩)
    (.inl fun ⟨⟨⟩, b⟩ => by cases b <;> decide)

theorem projectivePlane_toPolygonalComplex :
    projectivePlane.toPolygonalComplex = polygon [((), true), ((), true)] (List.cons_ne_nil _ _) :=
  (rfl)

/-- The projective plane has Euler characteristic `1`: one vertex, one edge and one face. -/
theorem eulerChar_projectivePlane : projectivePlane.eulerChar = 1 := by
  rw [projectivePlane_toPolygonalComplex, eulerChar_polygon, Nat.card_unique]
  norm_num

/-- The projective plane has no boundary: its edge lies on both face sides. -/
theorem boundaryDarts_projectivePlane : projectivePlane.boundaryDarts = ∅ :=
  Set.eq_empty_of_forall_notMem fun e => linkDegree_eq_two_iff_notMem_boundaryDarts.1 <|
    (linkDegree_polygon (α := Unit) [((), true), ((), true)] (List.cons_ne_nil _ _) e).trans <| by
      obtain ⟨⟨⟩, _ | _⟩ := e <;> decide

/-- The projective plane is not orientable: its two sides traverse the same dart, and orienting
the single face reverses both of them. -/
theorem not_isOrientable_projectivePlane : ¬projectivePlane.IsOrientable := by
  rw [isOrientable_iff]
  rintro ⟨σ, hσ⟩
  have h := hσ ⟨(), ⟨1, one_lt_two⟩⟩ ⟨(), ⟨0, two_pos⟩⟩
    (fun hc => Nat.one_ne_zero (congrArg (fun c => (c.2 : ℕ)) hc))
    (by rw [outgoing_def, outgoing_def]; rfl)
  cases hs : σ ()
  · rw [orientedSide_of_eq_false _ hs, orientedSide_of_eq_false _ hs, SerreGraph.rev_rev,
      outgoing_def, outgoing_def] at h
    exact (SerreGraph.rose Unit).rev_ne ((), true) h
  · rw [orientedSide_of_eq_true _ hs, orientedSide_of_eq_true _ hs, outgoing_def,
      outgoing_def] at h
    exact (SerreGraph.rose Unit).rev_ne ((), true) h.symm

/-! ### The sphere -/

/-- The sphere: the segment with its two darts, and a single face attached along the digon
`a a⁻¹`. -/
def sphere : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := singleFace SerreGraph.segment [false, true] (List.cons_ne_nil _ _)
    (by intro i; fin_cases i <;> rfl)
  connected := (SerreGraph.connected_iff _).2
    ⟨⟨false⟩, SerreGraph.preconnected_of_forall_nonempty_path _ false fun b => by
      cases b
      · exact ⟨.nil⟩
      · exact ⟨(SerreGraph.segment.dart false).toPath⟩⟩
  hasSurfaceLink v := by
    refine (PolygonalComplex.hasSurfaceLink_iff _ v).2 ⟨inferInstance,
      (SerreGraph.connected_iff _).2 ⟨⟨⟨v, rfl⟩⟩,
        SerreGraph.preconnected_of_forall_nonempty_path _ ⟨v, rfl⟩ fun ⟨e, he⟩ => ?_⟩,
      .inl fun e _ => ?_⟩
    · obtain rfl : e = v := (SerreGraph.segment_src e).symm.trans he
      exact ⟨.nil⟩
    · let _ : DecidableEq SerreGraph.segment.E := inferInstanceAs (DecidableEq Bool)
      refine (linkDegree_singleFace e).trans ?_
      cases e <;> decide

theorem sphere_toPolygonalComplex :
    sphere.toPolygonalComplex =
      singleFace SerreGraph.segment [false, true] (List.cons_ne_nil _ _)
        (by intro i; fin_cases i <;> rfl) := (rfl)

/-- The sphere has Euler characteristic `2`: two vertices, one edge and one face. -/
theorem eulerChar_sphere : sphere.eulerChar = 2 := by
  rw [sphere_toPolygonalComplex, eulerChar_singleFace,
    Nat.card_unique (α := SerreGraph.segment.GeomEdge), Nat.card_congr SerreGraph.segmentVEquiv,
    Nat.card_eq_fintype_card, Fintype.card_bool]
  norm_num

/-- The sphere has no boundary: its edge lies on both sides of the digon. -/
theorem boundaryDarts_sphere : sphere.boundaryDarts = ∅ :=
  Set.eq_empty_of_forall_notMem fun e => linkDegree_eq_two_iff_notMem_boundaryDarts.1 <| by
    let _ : DecidableEq SerreGraph.segment.E := inferInstanceAs (DecidableEq Bool)
    refine (linkDegree_singleFace (Γ := SerreGraph.segment) (w := [false, true])
      (hw := List.cons_ne_nil _ _) e).trans ?_
    cases e <;> decide

end SurfaceModel

end TauCeti
