/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Boundary
import Mathlib.Tactic.FinCases

/-!
# A triangulated disc

This file builds a triangulated disc as a polygonal surface model: three triangles around an inner
vertex, the centre, which is the cell complex of Figure 6.6 of Gallier and Xu (a tetrahedron with
one face omitted). The centre `none` is joined to the three rim vertices `some i` by the spokes
`sᵢ` (darts `(.inl i, true)`), and the rim edge `bᵢ` (darts `(.inr i, true)`) runs from `some i`
to `some (i + 1)`. The face `f` is the triangle `s_f b_f s_{f+1}⁻¹`.

The checks are those of a triangulated disc. Each spoke lies on two triangles and each rim edge on
one, so the boundary darts are the rim darts. The centre has no boundary germ, so its link is a
circle, and each rim vertex has exactly the two boundary germs `bᵢ` and `b_{i-1}⁻¹`, the ends of
its interval link. The boundary forms a single component, and the Euler characteristic is
`4 - 6 + 3 = 1`.

## Main definitions

* `TauCeti.PolygonalComplex.triangulatedDiscGraph`: the one-skeleton, a centre joined to the
  three vertices of a triangle.
* `TauCeti.PolygonalComplex.triangulatedDisc`: the three triangles around the centre.
* `TauCeti.SurfaceModel.triangulatedDisc`: the triangulated disc as a surface model.

## Main results

* `TauCeti.PolygonalComplex.linkDegree_triangulatedDisc_inl`,
  `TauCeti.PolygonalComplex.linkDegree_triangulatedDisc_inr`: each spoke lies on two triangles
  and each rim edge on one.
* `TauCeti.SurfaceModel.boundaryGerms_triangulatedDisc_none`,
  `TauCeti.SurfaceModel.boundaryGerms_triangulatedDisc_some`: the centre has a circle link and the
  rim vertices have interval links.
* `TauCeti.SurfaceModel.card_boundaryComponent_triangulatedDisc`: the triangulated disc has one
  boundary component.
* `TauCeti.SurfaceModel.eulerChar_triangulatedDisc`: the triangulated disc has Euler
  characteristic `1`.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definitions 6.1 and 6.2 and Figure 6.6.
-/

public section

namespace TauCeti

namespace PolygonalComplex

/-! ### The one-skeleton -/

/-- The one-skeleton of the triangulated disc: the centre `none` and the rim vertices `some i`.
The spoke `sᵢ`, with darts `(.inl i, true)` and its reverse `(.inl i, false)`, runs from the
centre to `some i`, and the rim edge `bᵢ`, with darts `(.inr i, true)` and its reverse
`(.inr i, false)`, runs from `some i` to `some (i + 1)`. The vertex and dart types are exposed, so
that vertices are options and darts are pairs. -/
@[expose] def triangulatedDiscGraph : SerreGraph.{0, 0} where
  V := Option (Fin 3)
  E := (Fin 3 ⊕ Fin 3) × Bool
  src e := e.1.elim (fun i => cond e.2 none (some i)) fun i => cond e.2 (some i) (some (i + 1))
  rev e := (e.1, !e.2)
  rev_rev e := by simp
  rev_ne e := by simp [Prod.ext_iff]

/-- The darts of the one-skeleton of the triangulated disc, being pairs, have decidable
equality. -/
instance : DecidableEq triangulatedDiscGraph.E :=
  inferInstanceAs (DecidableEq ((Fin 3 ⊕ Fin 3) × Bool))

/-- The spoke `sᵢ` starts at the centre and its reverse at the rim vertex `some i`. -/
@[simp] theorem triangulatedDiscGraph_src_inl (i : Fin 3) (b : Bool) :
    triangulatedDiscGraph.src (.inl i, b) = cond b none (some i) := (rfl)

/-- The rim edge `bᵢ` starts at `some i` and its reverse at `some (i + 1)`. -/
@[simp] theorem triangulatedDiscGraph_src_inr (i : Fin 3) (b : Bool) :
    triangulatedDiscGraph.src (.inr i, b) = cond b (some i) (some (i + 1)) := (rfl)

@[simp] theorem triangulatedDiscGraph_rev (x : Fin 3 ⊕ Fin 3) (b : Bool) :
    triangulatedDiscGraph.rev (x, b) = (x, !b) := (rfl)

/-- The one-skeleton of the triangulated disc has six geometric edges: three spokes and three rim
edges. -/
theorem card_geomEdge_triangulatedDiscGraph : Nat.card triangulatedDiscGraph.GeomEdge = 6 := by
  have hO : triangulatedDiscGraph.IsOrientation {e | e.2 = true} := by
    refine (triangulatedDiscGraph.isOrientation_iff _).2 fun ⟨_, b⟩ => ?_
    -- The darts are pairs, and reversal flips their second component.
    change (b = true) ↔ ¬(!b = true)
    cases b <;> decide
  calc Nat.card triangulatedDiscGraph.GeomEdge
      = Nat.card {e : triangulatedDiscGraph.E | e.2 = true} :=
        (Nat.card_congr (Equiv.ofBijective _ hO.bijective_toGeomEdge)).symm
    _ = Nat.card (Fin 3 ⊕ Fin 3) := Nat.card_congr
        ⟨fun e => e.1.1, fun x => ⟨(x, true), rfl⟩, fun ⟨⟨_, _⟩, h⟩ => by cases h; rfl,
          fun _ => rfl⟩
    _ = 6 := by simp

/-! ### The three triangles -/

/-- The three triangles around the centre: the face `f` is attached along `s_f b_f s_{f+1}⁻¹`,
from the centre to `some f`, to `some (f + 1)` and back. It is reducible, so that its faces are
seen to be `Fin 3` and its darts pairs. -/
abbrev triangulatedDisc : PolygonalComplex.{0, 0, 0} where
  graph := triangulatedDiscGraph
  Face := Fin 3
  sides _ := 3
  sides_pos _ := by decide
  side f k := [(.inl f, true), (.inr f, true), (.inl (f + 1), false)][k]
  tgt_side f k := by fin_cases f <;> fin_cases k <;> rfl

/-- The number of sides of the three triangles attached along a dart: one for a spoke in either
direction and for a rim edge in its own direction, none for the reverse of a rim edge. -/
private theorem card_side_eq : ∀ e : (Fin 3 ⊕ Fin 3) × Bool,
    (Finset.univ.filter fun c : Σ _ : Fin 3, Fin 3 =>
      ([(.inl c.1, true), (.inr c.1, true), (.inl (c.1 + 1), false)] :
        List ((Fin 3 ⊕ Fin 3) × Bool))[c.2] = e).card =
      cond e.2 1 (e.1.elim (fun _ => 1) fun _ => 0) := by
  decide

private theorem sideCount_triangulatedDisc (e : triangulatedDiscGraph.E) :
    triangulatedDisc.sideCount e = cond e.2 1 (e.1.elim (fun _ => 1) fun _ => 0) := by
  rw [sideCount_def, Nat.card_congr (Equiv.subtypeEquivRight fun c => by rw [outgoing_def]),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_side_eq e

/-- Each spoke of the triangulated disc lies on two triangles. -/
theorem linkDegree_triangulatedDisc_inl (i : Fin 3) (b : Bool) :
    triangulatedDisc.linkDegree (.inl i, b) = 2 := by
  cases b <;> exact (linkDegree_eq_sideCount_rev_add_sideCount _ _).trans
    (congrArg₂ (· + ·) (sideCount_triangulatedDisc _) (sideCount_triangulatedDisc _))

/-- Each rim edge of the triangulated disc lies on a single triangle. -/
theorem linkDegree_triangulatedDisc_inr (i : Fin 3) (b : Bool) :
    triangulatedDisc.linkDegree (.inr i, b) = 1 := by
  cases b <;> exact (linkDegree_eq_sideCount_rev_add_sideCount _ _).trans
    (congrArg₂ (· + ·) (sideCount_triangulatedDisc _) (sideCount_triangulatedDisc _))

/-- In the link of `x`, the corner `c` joins its outgoing side to the reverse of its incoming
side. -/
private theorem nonempty_path_of_corner {x : triangulatedDiscGraph.V}
    {a y : (triangulatedDisc.vertexLink x).V} (b : (triangulatedDisc.vertexLink x).V)
    (c : triangulatedDisc.Corner) (ha : a.1 = triangulatedDisc.side c.1 c.2)
    (hb : b.1 = triangulatedDiscGraph.rev (triangulatedDisc.side c.1 ((finRotate 3).symm c.2)))
    (h : Nonempty ((triangulatedDisc.vertexLink x).Path b y)) :
    Nonempty ((triangulatedDisc.vertexLink x).Path a y) :=
  Quiver.Reachable.trans (triangulatedDisc.nonempty_vertexLink_path_of_corner c
    (ha.trans (outgoing_def _ _).symm) (hb.trans (congrArg _ (incoming_def _ _).symm))) h

private theorem finite_vertexLink_triangulatedDisc (v : triangulatedDiscGraph.V) :
    Finite (triangulatedDisc.vertexLink v).E :=
  inferInstance

/-- The link of the centre is the circle `s₀, s₁, s₂` through the corners of the three triangles
at the centre. -/
private theorem hasSurfaceLink_triangulatedDisc_none :
    triangulatedDisc.HasSurfaceLink (none : triangulatedDiscGraph.V) := by
  refine (triangulatedDisc.hasSurfaceLink_iff _).2 ⟨finite_vertexLink_triangulatedDisc _,
    (triangulatedDisc.vertexLink _).connected_iff.2 ⟨⟨⟨(.inl 0, true), rfl⟩⟩,
      SerreGraph.preconnected_of_forall_nonempty_path _ ⟨(.inl 0, true), rfl⟩ ?_⟩, .inl ?_⟩
  · rintro ⟨⟨i | i, _ | _⟩, hb⟩
    · cases hb
    · fin_cases i
      · exact ⟨.nil⟩
      · exact nonempty_path_of_corner ⟨(.inl 1, true), rfl⟩ ⟨0, 0⟩ rfl rfl ⟨.nil⟩
      · exact nonempty_path_of_corner ⟨(.inl 1, true), rfl⟩ ⟨0, 0⟩ rfl rfl <|
          nonempty_path_of_corner ⟨(.inl 2, true), rfl⟩ ⟨1, 0⟩ rfl rfl ⟨.nil⟩
    · cases hb
    · cases hb
  · rintro ⟨i | i, _ | _⟩ he
    · cases he
    · exact linkDegree_triangulatedDisc_inl i true
    · cases he
    · cases he

/-- In the link of the rim vertex `some i`, every germ is joined to `bᵢ` along the interval
`bᵢ, sᵢ⁻¹, b_{i-1}⁻¹`. -/
private theorem nonempty_vertexLink_path_triangulatedDisc_some (i : Fin 3)
    (e : triangulatedDiscGraph.E) (he : triangulatedDiscGraph.src e = some i) :
    Nonempty ((triangulatedDisc.vertexLink (some i)).Path ⟨(.inr i, true), rfl⟩ ⟨e, he⟩) := by
  obtain ⟨k | k, _ | _⟩ := e
  · cases he
    fin_cases i
    · exact nonempty_path_of_corner ⟨(.inl 0, false), rfl⟩ ⟨0, 1⟩ rfl rfl ⟨.nil⟩
    · exact nonempty_path_of_corner ⟨(.inl 1, false), rfl⟩ ⟨1, 1⟩ rfl rfl ⟨.nil⟩
    · exact nonempty_path_of_corner ⟨(.inl 2, false), rfl⟩ ⟨2, 1⟩ rfl rfl ⟨.nil⟩
  · cases he
  · cases he
    fin_cases k
    · exact nonempty_path_of_corner ⟨(.inl 1, false), rfl⟩ ⟨1, 1⟩ rfl rfl <|
        nonempty_path_of_corner ⟨(.inr 0, false), rfl⟩ ⟨0, 2⟩ rfl rfl ⟨.nil⟩
    · exact nonempty_path_of_corner ⟨(.inl 2, false), rfl⟩ ⟨2, 1⟩ rfl rfl <|
        nonempty_path_of_corner ⟨(.inr 1, false), rfl⟩ ⟨1, 2⟩ rfl rfl ⟨.nil⟩
    · exact nonempty_path_of_corner ⟨(.inl 0, false), rfl⟩ ⟨0, 1⟩ rfl rfl <|
        nonempty_path_of_corner ⟨(.inr 2, false), rfl⟩ ⟨2, 2⟩ rfl rfl ⟨.nil⟩
  · cases he
    exact ⟨.nil⟩

/-- The link of the rim vertex `some i` is the interval `bᵢ, sᵢ⁻¹, b_{i-1}⁻¹` through the corners
of the two triangles at `some i`. -/
private theorem hasSurfaceLink_triangulatedDisc_some (i : Fin 3) :
    triangulatedDisc.HasSurfaceLink (some i : triangulatedDiscGraph.V) := by
  refine (triangulatedDisc.hasSurfaceLink_iff _).2 ⟨finite_vertexLink_triangulatedDisc _,
    (triangulatedDisc.vertexLink _).connected_iff.2 ⟨⟨⟨(.inr i, true), rfl⟩⟩,
      SerreGraph.preconnected_of_forall_nonempty_path _ ⟨(.inr i, true), rfl⟩
        fun ⟨e, he⟩ => nonempty_vertexLink_path_triangulatedDisc_some i e he⟩,
    .inr ⟨(.inr i, true), (.inr (i - 1), false), fun h => Bool.noConfusion (congrArg Prod.snd h),
      rfl, by fin_cases i <;> rfl, linkDegree_triangulatedDisc_inr i true,
      linkDegree_triangulatedDisc_inr (i - 1) false, ?_⟩⟩
  rintro ⟨k | k, _ | _⟩ he h₁ h₂
  · cases he
    exact linkDegree_triangulatedDisc_inl _ false
  · cases he
  · cases he
    fin_cases k <;> exact absurd rfl h₂
  · cases he
    exact absurd rfl h₁

end PolygonalComplex

namespace SurfaceModel

/-! ### The triangulated disc -/

/-- The triangulated disc: three triangles around an inner vertex. It is reducible, so that its
vertices, darts and faces are seen to be those of `PolygonalComplex.triangulatedDisc`. -/
abbrev triangulatedDisc : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := PolygonalComplex.triangulatedDisc
  connected := (PolygonalComplex.triangulatedDiscGraph.connected_iff).2 ⟨⟨none⟩,
    SerreGraph.preconnected_of_forall_nonempty_path _ none fun
      | none => ⟨.nil⟩
      | some i => ⟨(PolygonalComplex.triangulatedDiscGraph.dart (.inl i, true)).toPath⟩⟩
  hasSurfaceLink
    | none => by exact PolygonalComplex.hasSurfaceLink_triangulatedDisc_none
    | some i => by exact PolygonalComplex.hasSurfaceLink_triangulatedDisc_some i

/-- The rim darts are boundary darts of the triangulated disc. -/
@[simp] theorem inr_mem_boundaryDarts_triangulatedDisc (i : Fin 3) (b : Bool) :
    ((.inr i, b) : triangulatedDisc.graph.E) ∈ triangulatedDisc.boundaryDarts :=
  linkDegree_eq_one_iff_mem_boundaryDarts.1 <|
    PolygonalComplex.linkDegree_triangulatedDisc_inr i b

/-- The spokes are interior: they are not boundary darts of the triangulated disc. -/
@[simp] theorem inl_notMem_boundaryDarts_triangulatedDisc (i : Fin 3) (b : Bool) :
    ((.inl i, b) : triangulatedDisc.graph.E) ∉ triangulatedDisc.boundaryDarts :=
  linkDegree_eq_two_iff_notMem_boundaryDarts.1 <|
    PolygonalComplex.linkDegree_triangulatedDisc_inl i b

/-- The centre of the triangulated disc is an inner vertex: it has no boundary germ, so its link is
a circle. -/
theorem boundaryGerms_triangulatedDisc_none : triangulatedDisc.boundaryGerms none = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun e he => ?_
  obtain ⟨hb, hs⟩ := mem_boundaryGerms_iff.1 he
  obtain ⟨i | i, _ | _⟩ := e
  · cases hs
  · exact inl_notMem_boundaryDarts_triangulatedDisc i true hb
  · cases hs
  · cases hs

/-- The rim vertex `some i` of the triangulated disc is a boundary vertex: its boundary germs, the
two ends of its interval link, are the rim dart `bᵢ` and the reverse of `b_{i-1}`. -/
theorem boundaryGerms_triangulatedDisc_some (i : Fin 3) :
    triangulatedDisc.boundaryGerms (some i) = {(.inr i, true), (.inr (i - 1), false)} := by
  ext e
  refine ⟨fun he => ?_, fun he => ?_⟩
  · obtain ⟨hb, hs⟩ := mem_boundaryGerms_iff.1 he
    obtain ⟨k | k, _ | _⟩ := e
    · exact absurd hb (inl_notMem_boundaryDarts_triangulatedDisc k false)
    · cases hs
    · cases hs
      exact .inr (by fin_cases k <;> rfl)
    · cases hs
      exact .inl rfl
  · rcases he with rfl | rfl
    · exact mem_boundaryGerms_iff.2 ⟨inr_mem_boundaryDarts_triangulatedDisc i true, rfl⟩
    · exact mem_boundaryGerms_iff.2 ⟨inr_mem_boundaryDarts_triangulatedDisc (i - 1) false,
        by fin_cases i <;> rfl⟩

/-- The rim edges `b₀, b₁, b₂` follow one another around the rim, so they lie in the boundary
component of `b₀`. -/
private theorem boundaryClass_triangulatedDisc_inr (k : Fin 3) :
    triangulatedDisc.boundaryClass ⟨(.inr k, true), inr_mem_boundaryDarts_triangulatedDisc k true⟩ =
      triangulatedDisc.boundaryClass
        ⟨(.inr 0, true), inr_mem_boundaryDarts_triangulatedDisc 0 true⟩ := by
  have h (k : Fin 3) : triangulatedDisc.boundaryClass ⟨(.inr k, true),
      inr_mem_boundaryDarts_triangulatedDisc k true⟩ = triangulatedDisc.boundaryClass
        ⟨(.inr (k + 1), true), inr_mem_boundaryDarts_triangulatedDisc (k + 1) true⟩ :=
    boundaryClass_eq_of_tgt_eq_src (Subtype.ext rfl)
  fin_cases k
  · rfl
  · exact (h 0).symm
  · exact ((h 0).trans (h 1)).symm

/-- Every boundary dart of the triangulated disc lies in the boundary component of `b₀`. -/
private theorem boundaryClass_triangulatedDisc (e : triangulatedDisc.boundary.E) :
    triangulatedDisc.boundaryClass e = triangulatedDisc.boundaryClass
      ⟨(.inr 0, true), inr_mem_boundaryDarts_triangulatedDisc 0 true⟩ := by
  obtain ⟨⟨k | k, b⟩, he⟩ := e
  · exact absurd he (inl_notMem_boundaryDarts_triangulatedDisc k b)
  · cases b
    · exact (boundaryClass_rev (S := triangulatedDisc)
        ⟨(.inr k, true), inr_mem_boundaryDarts_triangulatedDisc k true⟩).trans
          (boundaryClass_triangulatedDisc_inr k)
    · exact boundaryClass_triangulatedDisc_inr k

/-- The triangulated disc has a single boundary component, formed by its three rim edges. -/
theorem card_boundaryComponent_triangulatedDisc :
    Nat.card triangulatedDisc.BoundaryComponent = 1 := by
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun b b' => ?_⟩, ⟨triangulatedDisc.boundaryClass
    ⟨(.inr 0, true), inr_mem_boundaryDarts_triangulatedDisc 0 true⟩⟩⟩
  obtain ⟨e, rfl⟩ := triangulatedDisc.boundaryClass_surjective b
  obtain ⟨e', rfl⟩ := triangulatedDisc.boundaryClass_surjective b'
  rw [boundaryClass_triangulatedDisc e, boundaryClass_triangulatedDisc e']

/-- The triangulated disc has Euler characteristic `1`: four vertices, six edges and three
faces. -/
theorem eulerChar_triangulatedDisc : triangulatedDisc.eulerChar = 1 := by
  rw [PolygonalComplex.eulerChar_def, PolygonalComplex.card_geomEdge_triangulatedDiscGraph]
  -- The vertices of the triangulated disc are `Option (Fin 3)` and its faces `Fin 3`.
  change ((Nat.card (Option (Fin 3)) : ℕ) : ℤ) - (6 : ℕ) + (Nat.card (Fin 3) : ℕ) = 1
  simp

end SurfaceModel

end TauCeti
