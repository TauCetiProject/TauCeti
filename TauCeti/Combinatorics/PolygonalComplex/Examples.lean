/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.SurfaceModel
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Basic polygonal surface models

This file supplies polygonal complexes with a single face (`PolygonalComplex.singleFace`), in
particular the one-vertex polygons `PolygonalComplex.polygon w` whose face is attached along a word
`w` in a rose, and the standard surface models built from them: the disc `a`, the torus
`a b a⁻¹ b⁻¹` and the projective plane `a a`. The sphere is the digon `a a⁻¹` on the segment, with
two vertices. For each model the file checks the surface links and the Euler characteristic. It
also separates the disc from the closed models by their boundary darts, and the torus from the
projective plane by orientability.

It also records how the surface-link condition fails at a pinched vertex. On the one-petal rose,
any family of faces `a a⁻¹` (`PolygonalComplex.digons`) has a disconnected vertex link: every
corner is a loop at `a` or at `a⁻¹`. For one face this is the sphere with two points identified.
For infinitely many faces the link is moreover infinite, and every germ then has
`Nat.card`-degree zero.

## Main definitions

* `TauCeti.PolygonalComplex.singleFace`: a complex with one face attached along a closed word.
* `TauCeti.PolygonalComplex.polygon`: the one-vertex complex with one face attached along a word.
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
* `TauCeti.SurfaceModel.boundaryDarts_disc`, `TauCeti.SurfaceModel.boundaryDarts_torus`: both darts
  of the disc are boundary darts, while the torus has no boundary.
* `TauCeti.PolygonalComplex.not_hasSurfaceLink_digons`: a pinched vertex has no surface link.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6.
-/

public section

universe u v

namespace TauCeti

namespace PolygonalComplex

/-! ### Complexes with a single face -/

/-- The polygonal complex with one-skeleton `Γ` and a single face, attached along the nonempty
closed dart sequence `w`. It is reducible, so that its faces, corners and darts are seen to be
`Unit`, positions in `w` and darts of `Γ`. -/
abbrev singleFace (Γ : SerreGraph.{u, v}) (w : List Γ.E) (hw : w ≠ [])
    (hclosed : ∀ i, Γ.tgt w[i] = Γ.src w[finRotate w.length i]) : PolygonalComplex.{u, v, 0} where
  graph := Γ
  Face := Unit
  sides _ := w.length
  sides_pos _ := List.length_pos_iff.2 hw
  side _ i := w[i]
  tgt_side _ := hclosed

section singleFace

variable {Γ : SerreGraph.{u, v}} {w : List Γ.E} {hw : w ≠ []}
  {hclosed : ∀ i, Γ.tgt w[i] = Γ.src w[finRotate w.length i]}

theorem singleFace_outgoing (k : Fin w.length) :
    (singleFace Γ w hw hclosed).outgoing ⟨(), k⟩ = w[k] :=
  outgoing_def _ _

theorem singleFace_incoming (k : Fin w.length) :
    (singleFace Γ w hw hclosed).incoming ⟨(), k⟩ = w[(finRotate w.length).symm k] :=
  incoming_def _ _

/-- The number of sides of a single face attached along a dart `e` is the number of occurrences of
`e` in its word. -/
theorem singleFace_sideCount [DecidableEq Γ.E] (e : Γ.E) :
    (singleFace Γ w hw hclosed).sideCount e = w.count e := by
  let eq : {c : (singleFace Γ w hw hclosed).Corner // (singleFace Γ w hw hclosed).outgoing c = e}
      ≃ {i : Fin w.length // w[i] = e} :=
    { toFun c := ⟨c.1.2, (outgoing_def _ _).symm.trans c.2⟩
      invFun i := ⟨⟨(), i.1⟩, (outgoing_def _ _).trans i.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [sideCount_def, Nat.card_congr eq, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.count_ofFn]
  congr 1
  exact List.ext_getElem (by simp) fun i _ _ => by simp

/-- The link degree of a dart in a single-face complex counts its occurrences and those of its
reverse in the word. -/
theorem singleFace_linkDegree [DecidableEq Γ.E] (e : Γ.E) :
    (singleFace Γ w hw hclosed).linkDegree e = w.count (Γ.rev e) + w.count e := by
  rw [linkDegree_eq_sideCount_rev_add_sideCount, singleFace_sideCount, singleFace_sideCount]

theorem singleFace_eulerChar :
    (singleFace Γ w hw hclosed).eulerChar = Nat.card Γ.V - Nat.card Γ.GeomEdge + 1 := by
  rw [eulerChar_def, Nat.card_unique (α := Unit), Nat.cast_one]

/-- In the link of a vertex of a single-face complex, the corner at position `k` joins the germ
`w[k]` to the reverse of the preceding dart. -/
private theorem singleFace_link_step {x : Γ.V}
    {a y : ((singleFace Γ w hw hclosed).vertexLink x).V}
    (b : ((singleFace Γ w hw hclosed).vertexLink x).V) (k : Fin w.length)
    (hk : Γ.src w[k] = x) (ha : a.1 = w[k]) (hb : b.1 = Γ.rev w[(finRotate w.length).symm k])
    (h : Nonempty (((singleFace Γ w hw hclosed).vertexLink x).Path b y)) :
    Nonempty (((singleFace Γ w hw hclosed).vertexLink x).Path a y) := by
  obtain ⟨p⟩ := (singleFace Γ w hw hclosed).nonempty_vertexLink_path ⟨⟨(), k⟩,
    ((src_outgoing _ _).symm.trans (congrArg Γ.src (singleFace_outgoing k))).trans hk⟩
    (ha.trans (singleFace_outgoing k).symm)
    (hb.trans (congrArg Γ.rev (singleFace_incoming k).symm))
  obtain ⟨q⟩ := h
  exact ⟨p.comp q⟩

end singleFace

/-- The one-vertex polygonal complex whose one-skeleton is the rose on `α` and which has a single
face, attached along the nonempty word `w`. -/
abbrev polygon {α : Type u} (w : List (α × Bool)) (hw : w ≠ []) : PolygonalComplex.{0, u, 0} :=
  singleFace (SerreGraph.rose α) w hw (by intro; rfl)

/-- The link degree of a dart in `polygon w` counts its occurrences and those of its reverse in
`w`. -/
theorem polygon_linkDegree {α : Type u} [DecidableEq α] (w : List (α × Bool)) (hw : w ≠ [])
    (e : α × Bool) : (polygon w hw).linkDegree e = w.count (e.1, !e.2) + w.count e := by
  let _ : DecidableEq (SerreGraph.rose α).E := inferInstanceAs (DecidableEq (α × Bool))
  exact singleFace_linkDegree (Γ := SerreGraph.rose α) e

theorem polygon_eulerChar {α : Type u} (w : List (α × Bool)) (hw : w ≠ []) :
    (polygon w hw).eulerChar = 2 - Nat.card α := by
  refine (singleFace_eulerChar (Γ := SerreGraph.rose α) (w := w) (hw := hw)).trans ?_
  rw [Nat.card_congr (SerreGraph.roseGeomEdgeEquiv α)]
  -- The rose has a single vertex.
  rw [show Nat.card (SerreGraph.rose α).V = 1 from Nat.card_unique (α := PUnit)]
  ring

/-- In the link of the vertex of `polygon w`, the corner at position `k` joins the germ `w[k]` to
the reverse of the preceding letter. -/
private theorem polygon_link_step {α : Type u} {w : List (α × Bool)} {hw : w ≠ []}
    {a y : ((polygon w hw).vertexLink PUnit.unit).V} (b : ((polygon w hw).vertexLink PUnit.unit).V)
    (k : Fin w.length) (ha : a.1 = w[k])
    (hb : b.1 = (w[(finRotate w.length).symm k].1, !w[(finRotate w.length).symm k].2))
    (h : Nonempty (((polygon w hw).vertexLink PUnit.unit).Path b y)) :
    Nonempty (((polygon w hw).vertexLink PUnit.unit).Path a y) :=
  singleFace_link_step b k rfl ha hb h

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

/-- A polygon whose link is joined from one germ to every germ, and whose letter counts give a
circle or an interval, has surface links. -/
private theorem polygon_hasSurfaceLink {α : Type u} [DecidableEq α] {w : List (α × Bool)}
    {hw : w ≠ []} (a : α × Bool)
    (hpath : ∀ b : α × Bool,
      Nonempty (((polygon w hw).vertexLink PUnit.unit).Path ⟨a, rfl⟩ ⟨b, rfl⟩))
    (hdeg : (∀ e : α × Bool, w.count (e.1, !e.2) + w.count e = 2) ∨
      ∃ e₁ e₂ : α × Bool, e₁ ≠ e₂ ∧ w.count (e₁.1, !e₁.2) + w.count e₁ = 1 ∧
        w.count (e₂.1, !e₂.2) + w.count e₂ = 1 ∧
          ∀ e : α × Bool, e ≠ e₁ → e ≠ e₂ → w.count (e.1, !e.2) + w.count e = 2)
    (v : (polygon w hw).graph.V) : (polygon w hw).HasSurfaceLink v := by
  refine ((polygon w hw).hasSurfaceLink_iff v).2 ⟨inferInstance,
    ((polygon w hw).vertexLink v).connected_iff.2 ⟨⟨⟨a, rfl⟩⟩,
      SerreGraph.preconnected_of_forall_nonempty_path _ ⟨a, rfl⟩ fun ⟨b, _⟩ => hpath b⟩, ?_⟩
  rcases hdeg with hcirc | ⟨e₁, e₂, hne, h₁, h₂, h⟩
  · exact .inl fun e _ => (polygon_linkDegree w hw e).trans (hcirc e)
  · exact .inr ⟨e₁, e₂, hne, rfl, rfl, (polygon_linkDegree w hw e₁).trans h₁,
      (polygon_linkDegree w hw e₂).trans h₂,
      fun e _ he₁ he₂ => (polygon_linkDegree w hw e).trans (h e he₁ he₂)⟩

/-- A polygon is orientable, keeping its face as given, when any two distinct occurrences of the
same edge in its word are mutually reverse letters. -/
private theorem polygon_isOrientable_of_forall {α : Type u} {w : List (α × Bool)} {hw : w ≠ []}
    (h : ∀ k k' : Fin w.length, k ≠ k' → (w[k'] = w[k] ∨ w[k'] = (w[k].1, !w[k].2)) →
      w[k'] = (w[k].1, !w[k].2)) :
    (polygon w hw).IsOrientable := by
  refine ((polygon w hw).isOrientable_iff).2 ⟨fun _ => true, fun ⟨⟨⟩, k⟩ ⟨⟨⟩, k'⟩ hne hk => ?_⟩
  rw [orientedSide_of_eq_true _ rfl, orientedSide_of_eq_true _ rfl, outgoing_def, outgoing_def]
  rw [outgoing_def, outgoing_def, SerreGraph.toGeomEdge_eq_toGeomEdge_iff] at hk
  exact h k k' (fun hkk => hne (hkk ▸ rfl)) hk

/-! ### The disc -/

/-- The disc: one petal `a` and a single face attached along `a`. -/
def disc : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := polygon [((), true)] (List.cons_ne_nil _ _)
  connected := SerreGraph.rose_connected Unit
  hasSurfaceLink := polygon_hasSurfaceLink ((), true)
    (fun ⟨⟨⟩, b⟩ => by
      cases b
      · exact polygon_link_step ⟨((), false), rfl⟩ ⟨0, by decide⟩ rfl rfl ⟨.nil⟩
      · exact ⟨.nil⟩)
    (.inr ⟨((), true), ((), false), by decide, by decide, by decide, by decide⟩)

theorem disc_toPolygonalComplex :
    disc.toPolygonalComplex = polygon [((), true)] (List.cons_ne_nil _ _) := (rfl)

theorem eulerChar_disc : disc.eulerChar = 1 := by
  rw [disc_toPolygonalComplex, polygon_eulerChar, Nat.card_unique]
  rfl

/-- Both darts of the disc are boundary darts: its single edge lies on one face side. -/
theorem boundaryDarts_disc : disc.boundaryDarts = Set.univ :=
  Set.eq_univ_of_forall fun e => linkDegree_eq_one_iff_mem_boundaryDarts.1 <|
    (polygon_linkDegree (α := Unit) [((), true)] (List.cons_ne_nil _ _) e).trans <| by
      obtain ⟨⟨⟩, _ | _⟩ := e <;> rfl

/-! ### The torus -/

/-- The torus: two petals `a`, `b` and a single face attached along `a b a⁻¹ b⁻¹`. -/
def torus : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := polygon (α := Fin 2) [(0, true), (1, true), (0, false), (1, false)]
    (List.cons_ne_nil _ _)
  connected := SerreGraph.rose_connected (Fin 2)
  hasSurfaceLink := polygon_hasSurfaceLink (0, true)
    (fun ⟨i, b⟩ => by
      -- The link is the cycle `a, b, a⁻¹, b⁻¹`, through the corners at positions `0, 1, 2`.
      fin_cases i <;> cases b
      · exact polygon_link_step ⟨(1, true), rfl⟩ ⟨0, by decide⟩ rfl rfl <|
          polygon_link_step ⟨(0, false), rfl⟩ ⟨1, by decide⟩ rfl rfl ⟨.nil⟩
      · exact ⟨.nil⟩
      · exact polygon_link_step ⟨(1, true), rfl⟩ ⟨0, by decide⟩ rfl rfl <|
          polygon_link_step ⟨(0, false), rfl⟩ ⟨1, by decide⟩ rfl rfl <|
          polygon_link_step ⟨(1, false), rfl⟩ ⟨2, by decide⟩ rfl rfl ⟨.nil⟩
      · exact polygon_link_step ⟨(1, true), rfl⟩ ⟨0, by decide⟩ rfl rfl ⟨.nil⟩)
    (.inl fun ⟨i, b⟩ => by fin_cases i <;> cases b <;> decide)

theorem torus_toPolygonalComplex :
    torus.toPolygonalComplex =
      polygon (α := Fin 2) [(0, true), (1, true), (0, false), (1, false)] (List.cons_ne_nil _ _) :=
  (rfl)

theorem eulerChar_torus : torus.eulerChar = 0 := by
  rw [torus_toPolygonalComplex, polygon_eulerChar, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

/-- The torus has no boundary: each of its two edges lies on two face sides. -/
theorem boundaryDarts_torus : torus.boundaryDarts = ∅ :=
  Set.eq_empty_of_forall_notMem fun e => linkDegree_eq_two_iff_notMem_boundaryDarts.1 <|
    (polygon_linkDegree (α := Fin 2) [(0, true), (1, true), (0, false), (1, false)]
      (List.cons_ne_nil _ _) e).trans <| by
      obtain ⟨i, b⟩ := e
      fin_cases i <;> cases b <;> rfl

/-- The torus is orientable: with its face kept as given, the two sides along each edge traverse
it in opposite directions. -/
theorem isOrientable_torus : torus.IsOrientable :=
  polygon_isOrientable_of_forall (hw := List.cons_ne_nil _ _) (by decide)

/-! ### The projective plane -/

/-- The projective plane: one petal `a` and a single face attached along `a a`. -/
def projectivePlane : SurfaceModel.{0, 0, 0} where
  toPolygonalComplex := polygon [((), true), ((), true)] (List.cons_ne_nil _ _)
  connected := SerreGraph.rose_connected Unit
  hasSurfaceLink := polygon_hasSurfaceLink ((), true)
    (fun ⟨⟨⟩, b⟩ => by
      cases b
      · exact polygon_link_step ⟨((), false), rfl⟩ ⟨0, by decide⟩ rfl rfl ⟨.nil⟩
      · exact ⟨.nil⟩)
    (.inl fun ⟨⟨⟩, b⟩ => by cases b <;> decide)

theorem projectivePlane_toPolygonalComplex :
    projectivePlane.toPolygonalComplex = polygon [((), true), ((), true)] (List.cons_ne_nil _ _) :=
  (rfl)

theorem eulerChar_projectivePlane : projectivePlane.eulerChar = 1 := by
  rw [projectivePlane_toPolygonalComplex, polygon_eulerChar, Nat.card_unique]
  rfl

/-- The projective plane has no boundary: its edge lies on both face sides. -/
theorem boundaryDarts_projectivePlane : projectivePlane.boundaryDarts = ∅ :=
  Set.eq_empty_of_forall_notMem fun e => linkDegree_eq_two_iff_notMem_boundaryDarts.1 <|
    (polygon_linkDegree (α := Unit) [((), true), ((), true)] (List.cons_ne_nil _ _) e).trans <| by
      obtain ⟨⟨⟩, _ | _⟩ := e <;> rfl

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
    · obtain rfl : e = v := he
      exact ⟨.nil⟩
    · let _ : DecidableEq SerreGraph.segment.E := inferInstanceAs (DecidableEq Bool)
      refine (singleFace_linkDegree e).trans ?_
      cases e <;> rfl

theorem sphere_toPolygonalComplex :
    sphere.toPolygonalComplex =
      singleFace SerreGraph.segment [false, true] (List.cons_ne_nil _ _)
        (by intro i; fin_cases i <;> rfl) := (rfl)

theorem eulerChar_sphere : sphere.eulerChar = 2 := by
  rw [sphere_toPolygonalComplex, singleFace_eulerChar,
    Nat.card_unique (α := SerreGraph.segment.GeomEdge)]
  -- The vertices of the segment are the two Booleans.
  rw [show Nat.card SerreGraph.segment.V = 2 from
    (Nat.card_eq_fintype_card (α := Bool)).trans Fintype.card_bool]
  rfl

end SurfaceModel

end TauCeti
