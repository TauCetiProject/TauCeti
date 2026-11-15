/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Boundary
public import TauCeti.Combinatorics.PolygonalComplex.SingleFace
import Mathlib.Tactic.FinCases

/-!
# The pair of pants as a polygonal surface model

The pair of pants is the sphere with three holes. Its canonical cell complex in the sense of
Gallier and Xu (normal form (I) with no handle and three holes) has a single face, attached along
the word `c₀ h₀ c₀⁻¹ c₁ h₁ c₁⁻¹ c₂ h₂ c₂⁻¹` (`PolygonalComplex.pantsWord`). The arc `cᵢ` runs from
an inner vertex, the centre, to the `i`-th hole vertex, and `hᵢ` is a loop at that hole vertex.

The one-skeleton `PolygonalComplex.pantsGraph centre hole` places the centre and the three hole
vertices at arbitrary points of a vertex type, so that `PolygonalComplex.pantsPolygon centre hole`
covers both the pair of pants itself, whose vertices are exactly four distinct points
(`SurfaceModel.pants`), and the complexes obtained from it by identifying vertices. Whatever the
identification, every arc lies on two face sides and every loop on one
(`PolygonalComplex.linkDegree_pantsPolygon_inl`, `PolygonalComplex.linkDegree_pantsPolygon_inr`).
The pair of pants has the three loops `hᵢ` as its boundary, three boundary components and Euler
characteristic `-1`.

Identifying two of the hole vertices, which lie on different boundary components, is rejected by
the surface-link condition: the corners at a hole vertex `hole i` only join germs along the arc
`cᵢ` and the loop `hᵢ`, so the germs coming from two different holes lie in different components
of its link (`PolygonalComplex.not_connected_vertexLink_pantsPolygon`). The identified vertex is a
pinched point, with no disc or half-disc neighbourhood.

## Main definitions

* `TauCeti.PolygonalComplex.pantsGraph`: the one-skeleton of the pants polygon, with a centre,
  three hole vertices, three arcs and three loops.
* `TauCeti.PolygonalComplex.pantsWord`: the word `c₀ h₀ c₀⁻¹ c₁ h₁ c₁⁻¹ c₂ h₂ c₂⁻¹`.
* `TauCeti.PolygonalComplex.pantsPolygon`: the complex with one face attached along this word.
* `TauCeti.SurfaceModel.pants`: the pair of pants.
* `TauCeti.SurfaceModel.pantsBoundaryComponentEquiv`: the boundary components of the pair of pants
  are indexed by its three holes.

## Main results

* `TauCeti.PolygonalComplex.linkDegree_pantsPolygon_inl`,
  `TauCeti.PolygonalComplex.linkDegree_pantsPolygon_inr`: every arc lies on two face sides and
  every loop on one, whichever vertices are identified.
* `TauCeti.PolygonalComplex.eulerChar_pantsPolygon`: the Euler characteristic is `|V| - 5`.
* `TauCeti.PolygonalComplex.not_connected_vertexLink_pantsPolygon`,
  `TauCeti.PolygonalComplex.not_hasSurfaceLink_pantsPolygon`: identifying two distinct hole
  vertices disconnects the link of the identified vertex, which therefore has no surface link.
* `TauCeti.SurfaceModel.eulerChar_pants`: the pair of pants has Euler characteristic `-1`.
* `TauCeti.SurfaceModel.boundaryGerms_pants_none`, `TauCeti.SurfaceModel.boundaryGerms_pants_some`:
  the centre is an inner vertex and the boundary germs at a hole vertex are the two darts of its
  loop.
* `TauCeti.SurfaceModel.card_boundaryComponent_pants`: the pair of pants has three boundary
  components.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definitions 6.1 and 6.2 (cell complexes, inner and boundary vertices) and
  Definition 6.5 (normal forms).
-/

public section

universe u

namespace TauCeti

namespace PolygonalComplex

/-! ### The pants graph -/

/-- The one-skeleton of the pants polygon, with vertices in `V`: the arc `cᵢ` runs from `centre` to
`hole i`, with darts `(.inl i, true)` and its reverse `(.inl i, false)`, and the loop `hᵢ` at
`hole i` has the darts `(.inr i, true)` and `(.inr i, false)`. The vertex and dart types are
exposed, so that vertices are points of `V` and darts are pairs. -/
@[expose] def pantsGraph {V : Type u} (centre : V) (hole : Fin 3 → V) : SerreGraph.{u, 0} where
  V := V
  E := (Fin 3 ⊕ Fin 3) × Bool
  src e := e.1.elim (fun i => cond e.2 centre (hole i)) hole
  rev e := (e.1, !e.2)
  rev_rev e := by simp
  rev_ne e := by simp [Prod.ext_iff]

variable {V : Type u} (centre : V) (hole : Fin 3 → V)

/-- The darts of the pants graph, being pairs, have decidable equality. -/
instance : DecidableEq (pantsGraph centre hole).E :=
  inferInstanceAs (DecidableEq ((Fin 3 ⊕ Fin 3) × Bool))

/-- The pants graph has twelve darts: the two directions of three arcs and three loops. -/
instance : Fintype (pantsGraph centre hole).E :=
  inferInstanceAs (Fintype ((Fin 3 ⊕ Fin 3) × Bool))

/-- The vertices of the pants graph are the points of `V`. -/
instance [DecidableEq V] : DecidableEq (pantsGraph centre hole).V := inferInstanceAs (DecidableEq V)

/-- The vertices of the pants graph are the points of `V`. -/
instance [Fintype V] : Fintype (pantsGraph centre hole).V := inferInstanceAs (Fintype V)

/-- The vertices of the pants graph are the points of `V`. -/
instance [Finite V] : Finite (pantsGraph centre hole).V := inferInstanceAs (Finite V)

/-- The arc `cᵢ` starts at the centre and its reverse at the `i`-th hole vertex. -/
@[simp] theorem pantsGraph_src_inl (i : Fin 3) (b : Bool) :
    (pantsGraph centre hole).src (.inl i, b) = cond b centre (hole i) := (rfl)

/-- Both darts of the loop `hᵢ` start at the `i`-th hole vertex. -/
@[simp] theorem pantsGraph_src_inr (i : Fin 3) (b : Bool) :
    (pantsGraph centre hole).src (.inr i, b) = hole i := (rfl)

@[simp] theorem pantsGraph_rev (x : Fin 3 ⊕ Fin 3) (b : Bool) :
    (pantsGraph centre hole).rev (x, b) = (x, !b) := (rfl)

/-- The arc `cᵢ` ends at the `i`-th hole vertex and its reverse at the centre. -/
@[simp] theorem pantsGraph_tgt_inl (i : Fin 3) (b : Bool) :
    (pantsGraph centre hole).tgt (.inl i, b) = cond b (hole i) centre := by
  cases b <;> rfl

/-- Both darts of the loop `hᵢ` end at the `i`-th hole vertex. -/
@[simp] theorem pantsGraph_tgt_inr (i : Fin 3) (b : Bool) :
    (pantsGraph centre hole).tgt (.inr i, b) = hole i := (rfl)

/-- The pants graph has six geometric edges, the three arcs and the three loops: its darts and
their reversal are those of the rose with six petals. -/
@[simp] theorem card_geomEdge_pantsGraph : Nat.card (pantsGraph centre hole).GeomEdge = 6 := by
  rw [Nat.card_congr ((SerreGraph.GeomEdge.congr (pantsGraph centre hole)
    (Δ := SerreGraph.rose (Fin 3 ⊕ Fin 3)) (Equiv.refl _) fun _ => rfl).trans
      (SerreGraph.roseGeomEdgeEquiv _))]
  simp

/-! ### The pants polygon -/

/-- The word `c₀ h₀ c₀⁻¹ c₁ h₁ c₁⁻¹ c₂ h₂ c₂⁻¹` in the darts of the pants graph: each hole is
reached from the centre along its arc, traversed once along its loop and left along the arc. -/
@[expose] def pantsWord : List ((Fin 3 ⊕ Fin 3) × Bool) :=
  [(.inl 0, true), (.inr 0, true), (.inl 0, false), (.inl 1, true), (.inr 1, true),
    (.inl 1, false), (.inl 2, true), (.inr 2, true), (.inl 2, false)]

/-- The pants polygon: the complex with one-skeleton `pantsGraph centre hole` and a single face
attached along `pantsWord`. When `V` consists of exactly the four distinct points `centre`,
`hole 0`, `hole 1` and `hole 2` it is the pair of pants (`SurfaceModel.pants`); otherwise it is
obtained from the pair of pants by identifying vertices or adding isolated ones. It is reducible,
so that it is seen to be a single-face complex. -/
abbrev pantsPolygon : PolygonalComplex.{u, 0, 0} :=
  singleFace (pantsGraph centre hole) pantsWord (List.cons_ne_nil _ _)
    (by intro i; fin_cases i <;> rfl)

/-- Each arc occurs once in each direction in the pants word, and each loop once, in its own
direction. -/
private theorem count_pantsWord : ∀ e : (Fin 3 ⊕ Fin 3) × Bool,
    @List.count _ instBEqOfDecidableEq e pantsWord =
      e.1.elim (fun _ => 1) fun _ => cond e.2 1 0 := by
  decide

/-- Each letter of the pants word occurs, together with its reverse, twice if it is an arc and
once if it is a loop. -/
private theorem count_rev_add_count_pantsWord : ∀ e : (Fin 3 ⊕ Fin 3) × Bool,
    @List.count _ instBEqOfDecidableEq (e.1, !e.2) pantsWord +
      @List.count _ instBEqOfDecidableEq e pantsWord = e.1.elim (fun _ => 2) fun _ => 1 := by
  decide

/-- Each direction of each arc is one side of the face of the pants polygon. -/
@[simp] theorem sideCount_pantsPolygon_inl (i : Fin 3) (b : Bool) :
    (pantsPolygon centre hole).sideCount (.inl i, b) = 1 :=
  (sideCount_singleFace _).trans (count_pantsWord (.inl i, b))

/-- Each loop is one side of the face of the pants polygon, traversed in its own direction. -/
@[simp] theorem sideCount_pantsPolygon_inr (i : Fin 3) (b : Bool) :
    (pantsPolygon centre hole).sideCount (.inr i, b) = cond b 1 0 :=
  (sideCount_singleFace _).trans (count_pantsWord (.inr i, b))

/-- Each arc lies on two face sides of the pants polygon, whichever vertices are identified. -/
@[simp] theorem linkDegree_pantsPolygon_inl (i : Fin 3) (b : Bool) :
    (pantsPolygon centre hole).linkDegree (.inl i, b) = 2 :=
  (linkDegree_singleFace _).trans (count_rev_add_count_pantsWord (.inl i, b))

/-- Each loop lies on a single face side of the pants polygon, whichever vertices are
identified. -/
@[simp] theorem linkDegree_pantsPolygon_inr (i : Fin 3) (b : Bool) :
    (pantsPolygon centre hole).linkDegree (.inr i, b) = 1 :=
  (linkDegree_singleFace _).trans (count_rev_add_count_pantsWord (.inr i, b))

/-- The pants polygon has Euler characteristic `|V| - 6 + 1`: six edges and one face. -/
theorem eulerChar_pantsPolygon : (pantsPolygon centre hole).eulerChar = Nat.card V - 5 := by
  refine eulerChar_singleFace.trans ?_
  rw [card_geomEdge_pantsGraph]
  -- The vertices of `pantsGraph centre hole` are the points of `V`.
  change (Nat.card V : ℤ) - (6 : ℕ) + 1 = Nat.card V - 5
  omega

/-- Whichever vertices are identified, each corner of the pants polygon joins two germs that start
at the same vertex of the pair of pants `pantsGraph none some`, whose vertices are the centre and
the holes. -/
private theorem src_outgoing_pantsPolygon (c : (pantsPolygon centre hole).Corner) :
    (pantsGraph (none : Option (Fin 3)) some).src ((pantsPolygon centre hole).outgoing c) =
      (pantsGraph (none : Option (Fin 3)) some).src
        ((pantsGraph centre hole).rev ((pantsPolygon centre hole).incoming c)) := by
  obtain ⟨⟨⟩, k⟩ := c
  have h := ((pantsPolygon (none : Option (Fin 3)) some).src_outgoing ⟨(), k⟩).trans
    ((pantsPolygon (none : Option (Fin 3)) some).tgt_incoming ⟨(), k⟩).symm
  rw [outgoing_def, incoming_def] at h ⊢
  exact h

/-- The two ends of a link dart of the pants polygon start at the same vertex of the pair of
pants. -/
private theorem src_src_eq_src_tgt {x : (pantsGraph centre hole).V}
    (d : ((pantsPolygon centre hole).vertexLink x).E) :
    (pantsGraph (none : Option (Fin 3)) some).src
        (((pantsPolygon centre hole).vertexLink x).src d).1 =
      (pantsGraph (none : Option (Fin 3)) some).src
        (((pantsPolygon centre hole).vertexLink x).tgt d).1 := by
  obtain ⟨c, _ | _⟩ := d
  · exact (congrArg (pantsGraph (none : Option (Fin 3)) some).src (vertexLink_src_false _ c)).trans
      ((src_outgoing_pantsPolygon centre hole c.1).symm.trans
        (congrArg (pantsGraph (none : Option (Fin 3)) some).src (vertexLink_src_true _ c)).symm)
  · exact (congrArg (pantsGraph (none : Option (Fin 3)) some).src (vertexLink_src_true _ c)).trans
      ((src_outgoing_pantsPolygon centre hole c.1).trans
        (congrArg (pantsGraph (none : Option (Fin 3)) some).src (vertexLink_src_false _ c)).symm)

/-- Germs joined by a path in a vertex link of the pants polygon start at the same vertex of the
pair of pants. -/
private theorem src_eq_of_path {x : (pantsGraph centre hole).V}
    {a b : ((pantsPolygon centre hole).vertexLink x).V}
    (p : ((pantsPolygon centre hole).vertexLink x).Path a b) :
    (pantsGraph (none : Option (Fin 3)) some).src a.1 =
      (pantsGraph (none : Option (Fin 3)) some).src b.1 := by
  induction p with
  | nil => rfl
  | cons _ d ih =>
    exact ih.trans ((congrArg (fun y => (pantsGraph (none : Option (Fin 3)) some).src y.1)
      d.2.1).symm.trans ((src_src_eq_src_tgt centre hole d.1).trans
        (congrArg (fun y => (pantsGraph (none : Option (Fin 3)) some).src y.1) d.2.2)))

variable {centre hole}

/-- Identifying two distinct hole vertices of the pants polygon disconnects the link of the
identified vertex: the germs along the loops of the two holes lie in different components. -/
theorem not_connected_vertexLink_pantsPolygon {i j : Fin 3} (hij : i ≠ j) (h : hole i = hole j) :
    ¬((pantsPolygon centre hole).vertexLink (hole i)).Connected := fun hconn => by
  obtain ⟨-, hpre⟩ := ((pantsPolygon centre hole).vertexLink _).connected_iff.1 hconn
  obtain ⟨p⟩ := ((pantsPolygon centre hole).vertexLink _).preconnected_iff.1 hpre
    ⟨(.inr i, true), rfl⟩ ⟨(.inr j, true), h.symm⟩
  exact hij (Option.some_injective _ (src_eq_of_path centre hole p))

/-- Identifying two distinct hole vertices of the pants polygon is rejected by the surface-link
condition, although every edge still lies on one or two face sides: the identified vertex is a
pinched point. -/
theorem not_hasSurfaceLink_pantsPolygon {i j : Fin 3} (hij : i ≠ j) (h : hole i = hole j) :
    ¬(pantsPolygon centre hole).HasSurfaceLink (hole i) := fun hs =>
  not_connected_vertexLink_pantsPolygon hij h
    (((pantsPolygon centre hole).hasSurfaceLink_iff _).1 hs).2.1

end PolygonalComplex

open PolygonalComplex

namespace SurfaceModel

/-! ### The pair of pants -/

/-- The link of the centre of the pair of pants is the circle `c₀, c₂, c₁` through the corners at
the starts of the three blocks `cᵢ hᵢ cᵢ⁻¹`. -/
private theorem hasSurfaceLink_pants_none :
    (pantsPolygon (none : Option (Fin 3)) some).HasSurfaceLink
      (none : (pantsGraph (none : Option (Fin 3)) some).V) := by
  refine hasSurfaceLink_singleFace (Γ := pantsGraph (none : Option (Fin 3)) some) none
    (.inl 0, true) rfl ?_ (.inl ?_)
  · rintro ⟨i | i, _ | _⟩ hb
    · cases hb
    · fin_cases i
      · exact ⟨.nil⟩
      · exact nonempty_vertexLink_path_singleFace ⟨(.inl 2, true), rfl⟩ ⟨0, by decide⟩ rfl rfl
          rfl <| nonempty_vertexLink_path_singleFace ⟨(.inl 1, true), rfl⟩ ⟨6, by decide⟩ rfl rfl
          rfl ⟨.nil⟩
      · exact nonempty_vertexLink_path_singleFace ⟨(.inl 2, true), rfl⟩ ⟨0, by decide⟩ rfl rfl
          rfl ⟨.nil⟩
    · cases hb
    · cases hb
  · rintro ⟨i | i, _ | _⟩ he
    · cases he
    · exact count_rev_add_count_pantsWord (.inl i, true)
    · cases he
    · cases he

/-- In the link of the hole vertex `some i` of the pair of pants, every germ is joined to `hᵢ`
along the interval `hᵢ, cᵢ⁻¹, hᵢ⁻¹`. -/
private theorem nonempty_vertexLink_path_pants_some (i : Fin 3)
    (e : (pantsGraph (none : Option (Fin 3)) some).E)
    (he : (pantsGraph (none : Option (Fin 3)) some).src e = some i) :
    Nonempty (((pantsPolygon (none : Option (Fin 3)) some).vertexLink (some i)).Path
      ⟨(.inr i, true), rfl⟩ ⟨e, he⟩) := by
  -- The corner at position `3 i + 1` joins `hᵢ` to `cᵢ⁻¹`, the next one `cᵢ⁻¹` to `hᵢ⁻¹`.
  have h₁ : Nonempty (((pantsPolygon (none : Option (Fin 3)) some).vertexLink (some i)).Path
      ⟨(.inr i, true), rfl⟩ ⟨(.inl i, false), rfl⟩) := by
    fin_cases i
    · exact nonempty_vertexLink_path_singleFace _ ⟨1, by decide⟩ rfl rfl rfl ⟨.nil⟩
    · exact nonempty_vertexLink_path_singleFace _ ⟨4, by decide⟩ rfl rfl rfl ⟨.nil⟩
    · exact nonempty_vertexLink_path_singleFace _ ⟨7, by decide⟩ rfl rfl rfl ⟨.nil⟩
  have h₂ : Nonempty (((pantsPolygon (none : Option (Fin 3)) some).vertexLink (some i)).Path
      ⟨(.inl i, false), rfl⟩ ⟨(.inr i, false), rfl⟩) := by
    fin_cases i
    · exact nonempty_vertexLink_path_singleFace _ ⟨2, by decide⟩ rfl rfl rfl ⟨.nil⟩
    · exact nonempty_vertexLink_path_singleFace _ ⟨5, by decide⟩ rfl rfl rfl ⟨.nil⟩
    · exact nonempty_vertexLink_path_singleFace _ ⟨8, by decide⟩ rfl rfl rfl ⟨.nil⟩
  obtain ⟨k | k, _ | _⟩ := e <;> cases he
  · exact h₁
  · exact Quiver.Reachable.trans h₁ h₂
  · exact ⟨.nil⟩

/-- The link of the hole vertex `some i` of the pair of pants is the interval
`hᵢ, cᵢ⁻¹, hᵢ⁻¹`. -/
private theorem hasSurfaceLink_pants_some (i : Fin 3) :
    (pantsPolygon (none : Option (Fin 3)) some).HasSurfaceLink
      (some i : (pantsGraph (none : Option (Fin 3)) some).V) := by
  refine hasSurfaceLink_singleFace (Γ := pantsGraph (none : Option (Fin 3)) some) (some i)
    (.inr i, true) rfl (nonempty_vertexLink_path_pants_some i) (.inr ⟨(.inr i, true),
      (.inr i, false), fun h => Bool.noConfusion (congrArg Prod.snd h), rfl, rfl,
      count_rev_add_count_pantsWord (.inr i, true), count_rev_add_count_pantsWord (.inr i, false),
      ?_⟩)
  rintro ⟨k | k, _ | _⟩ he h₁ h₂
  · cases he
    exact count_rev_add_count_pantsWord (.inl i, false)
  · cases he
  · cases he
    exact absurd rfl h₂
  · cases he
    exact absurd rfl h₁

/-- The pair of pants: the pants polygon on four distinct vertices, the centre `none` and the hole
vertices `some i`. It is reducible, so that its vertices, darts and faces are seen to be those of
the pants polygon. -/
abbrev pants : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := pantsPolygon (none : Option (Fin 3)) some
  connected := ((pantsGraph (none : Option (Fin 3)) some).connected_iff).2 ⟨⟨none⟩,
    SerreGraph.preconnected_of_forall_nonempty_path _ none fun
      | none => ⟨.nil⟩
      | some i => ⟨((pantsGraph (none : Option (Fin 3)) some).dart (.inl i, true)).toPath⟩⟩
  hasSurfaceLink
    | none => by exact hasSurfaceLink_pants_none
    | some i => by exact hasSurfaceLink_pants_some i

/-- The loops `hᵢ` are boundary darts of the pair of pants. -/
@[simp] theorem inr_mem_boundaryDarts_pants (i : Fin 3) (b : Bool) :
    ((.inr i, b) : pants.graph.E) ∈ pants.boundaryDarts :=
  linkDegree_eq_one_iff_mem_boundaryDarts.1 (linkDegree_pantsPolygon_inr _ _ i b)

/-- The arcs `cᵢ` are interior: they are not boundary darts of the pair of pants. -/
@[simp] theorem inl_notMem_boundaryDarts_pants (i : Fin 3) (b : Bool) :
    ((.inl i, b) : pants.graph.E) ∉ pants.boundaryDarts :=
  linkDegree_eq_two_iff_notMem_boundaryDarts.1 (linkDegree_pantsPolygon_inl _ _ i b)

/-- The pair of pants has Euler characteristic `-1`: four vertices, six edges and one face. -/
theorem eulerChar_pants : pants.eulerChar = -1 := by
  rw [eulerChar_pantsPolygon (none : Option (Fin 3)) some]
  simp

/-- The centre of the pair of pants is an inner vertex: it has no boundary germ. -/
@[simp] theorem boundaryGerms_pants_none : pants.boundaryGerms none = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun e he => ?_
  obtain ⟨hb, hs⟩ := mem_boundaryGerms_iff.1 he
  obtain ⟨i | i, _ | _⟩ := e <;> cases hs
  exact inl_notMem_boundaryDarts_pants i true hb

/-- The hole vertex `some i` of the pair of pants is a boundary vertex: its boundary germs, the two
ends of its interval link, are the two darts of the loop `hᵢ`. -/
@[simp] theorem boundaryGerms_pants_some (i : Fin 3) :
    pants.boundaryGerms (some i) = {((.inr i, true) : pants.graph.E), (.inr i, false)} := by
  have hsub : {((.inr i, true) : pants.graph.E), (.inr i, false)} ⊆
      pants.boundaryGerms (some i) :=
    Set.pair_subset_iff.2 ⟨mem_boundaryGerms_iff.2 ⟨inr_mem_boundaryDarts_pants i true, rfl⟩,
      mem_boundaryGerms_iff.2 ⟨inr_mem_boundaryDarts_pants i false, rfl⟩⟩
  refine (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  exact ((ncard_boundaryGerms_eq_two _ ⟨_, hsub (.inl rfl)⟩).trans
    (Set.ncard_pair fun h => Bool.noConfusion (congrArg Prod.snd h)).symm).le

/-- Every boundary dart of the pair of pants is a loop. -/
private theorem boundary_src_eq_tgt_pants (e : pants.boundary.E) :
    pants.boundary.src e = pants.boundary.tgt e := by
  obtain ⟨⟨i | i, b⟩, he⟩ := e
  · exact absurd he (inl_notMem_boundaryDarts_pants i b)
  · cases b <;> rfl

/-- Both darts of the loop `hᵢ` lie in the same boundary component. -/
private theorem boundaryClass_pants_inr (i : Fin 3) (b : Bool)
    (h : ((.inr i, b) : pants.graph.E) ∈ pants.boundaryDarts) :
    pants.boundaryClass ⟨(.inr i, b), h⟩ =
      pants.boundaryClass ⟨(.inr i, true), inr_mem_boundaryDarts_pants i true⟩ := by
  cases b
  · exact boundaryClass_rev (S := pants) ⟨(.inr i, true), inr_mem_boundaryDarts_pants i true⟩
  · rfl

/-- The boundary components of the pair of pants are indexed by its holes: the component of the
hole `i` is the loop `hᵢ`. -/
noncomputable def pantsBoundaryComponentEquiv : pants.BoundaryComponent ≃ Fin 3 :=
  (Equiv.ofBijective
    (fun i => pants.boundaryClass ⟨(.inr i, true), inr_mem_boundaryDarts_pants i true⟩)
    ⟨fun i j h => Option.some_injective _ (congrArg Subtype.val
      (SerreGraph.eq_of_path_of_forall_src_eq_tgt _ boundary_src_eq_tgt_pants
        (boundaryClass_eq_boundaryClass_iff.1 h).some)), fun x => by
      obtain ⟨⟨⟨i | i, b⟩, he⟩, rfl⟩ := pants.boundaryClass_surjective x
      · exact absurd he (inl_notMem_boundaryDarts_pants i b)
      · exact ⟨i, (boundaryClass_pants_inr i b he).symm⟩⟩).symm

/-- The boundary component of the hole `i` of the pair of pants is the class of the loop `hᵢ`. -/
@[simp] theorem pantsBoundaryComponentEquiv_symm_apply (i : Fin 3) :
    pantsBoundaryComponentEquiv.symm i =
      pants.boundaryClass ⟨(.inr i, true), inr_mem_boundaryDarts_pants i true⟩ :=
  (rfl)

/-- Either dart of the loop `hᵢ` lies in the boundary component of the hole `i`. -/
@[simp] theorem pantsBoundaryComponentEquiv_boundaryClass_inr (i : Fin 3) (b : Bool)
    (h : ((.inr i, b) : pants.graph.E) ∈ pants.boundaryDarts) :
    pantsBoundaryComponentEquiv (pants.boundaryClass ⟨(.inr i, b), h⟩) = i :=
  (Equiv.eq_symm_apply _).1 (boundaryClass_pants_inr i b h)

/-- The pair of pants has three boundary components, the loops `h₀`, `h₁` and `h₂`. -/
theorem card_boundaryComponent_pants : Nat.card pants.BoundaryComponent = 3 :=
  (Nat.card_congr pantsBoundaryComponentEquiv).trans (Nat.card_fin 3)

end SurfaceModel

end TauCeti
