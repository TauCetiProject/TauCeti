/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Basic
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring

/-!
# Polygonal complexes with a single face

This file supplies polygonal complexes with a single face (`PolygonalComplex.singleFace`),
attached along a closed dart sequence in a Serre graph, and in particular the one-vertex polygons
`PolygonalComplex.polygon w` whose face is attached along a word `w` in a rose. Side counts and
link degrees of a single face are letter counts in its word, and the corners of the face give the
paths in its vertex links.

## Main definitions

* `TauCeti.PolygonalComplex.singleFace`: a complex with one face attached along a closed word.
* `TauCeti.PolygonalComplex.polygon`: the one-vertex complex with one face attached along a word.

## Main results

* `TauCeti.PolygonalComplex.linkDegree_singleFace`, `TauCeti.PolygonalComplex.linkDegree_polygon`:
  link degrees count occurrences of a dart and of its reverse in the word.
* `TauCeti.PolygonalComplex.eulerChar_singleFace`, `TauCeti.PolygonalComplex.eulerChar_polygon`:
  the Euler characteristic of a single-face complex.
* `TauCeti.PolygonalComplex.hasSurfaceLink_singleFace`,
  `TauCeti.PolygonalComplex.isOrientable_singleFace`: sufficient conditions for a single-face
  complex to have a surface link (link connectivity plus letter counts of its word) and to be
  orientable (distinct occurrences of an edge are mutually reverse darts), with the special cases
  `TauCeti.PolygonalComplex.hasSurfaceLink_polygon` and
  `TauCeti.PolygonalComplex.isOrientable_polygon`.

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

theorem outgoing_singleFace (k : Fin w.length) :
    (singleFace Γ w hw hclosed).outgoing ⟨(), k⟩ = w[k] :=
  outgoing_def _ _

theorem incoming_singleFace (k : Fin w.length) :
    (singleFace Γ w hw hclosed).incoming ⟨(), k⟩ = w[(finRotate w.length).symm k] :=
  incoming_def _ _

/-- The number of sides of a single face attached along a dart `e` is the number of occurrences of
`e` in its word. -/
theorem sideCount_singleFace [DecidableEq Γ.E] (e : Γ.E) :
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
theorem linkDegree_singleFace [DecidableEq Γ.E] (e : Γ.E) :
    (singleFace Γ w hw hclosed).linkDegree e = w.count (Γ.rev e) + w.count e := by
  rw [linkDegree_eq_sideCount_rev_add_sideCount, sideCount_singleFace, sideCount_singleFace]

theorem eulerChar_singleFace :
    (singleFace Γ w hw hclosed).eulerChar = Nat.card Γ.V - Nat.card Γ.GeomEdge + 1 := by
  rw [eulerChar_def, Nat.card_unique (α := Unit), Nat.cast_one]

/-- In the link of a vertex of a single-face complex, the corner at position `k` joins the germ
`w[k]` to the reverse of the preceding dart. -/
theorem nonempty_vertexLink_path_singleFace {x : Γ.V}
    {a y : ((singleFace Γ w hw hclosed).vertexLink x).V}
    (b : ((singleFace Γ w hw hclosed).vertexLink x).V) (k : Fin w.length)
    (hk : Γ.src w[k] = x) (ha : a.1 = w[k]) (hb : b.1 = Γ.rev w[(finRotate w.length).symm k])
    (h : Nonempty (((singleFace Γ w hw hclosed).vertexLink x).Path b y)) :
    Nonempty (((singleFace Γ w hw hclosed).vertexLink x).Path a y) := by
  obtain ⟨p⟩ := (singleFace Γ w hw hclosed).nonempty_vertexLink_path ⟨⟨(), k⟩,
    ((src_outgoing _ _).symm.trans (congrArg Γ.src (outgoing_singleFace k))).trans hk⟩
    (ha.trans (outgoing_singleFace k).symm)
    (hb.trans (congrArg Γ.rev (incoming_singleFace k).symm))
  obtain ⟨q⟩ := h
  exact ⟨p.comp q⟩

/-- A single-face complex has a surface link at `v` when its link at `v` is joined from one germ
to every germ, and the letter counts of its word at the germs of `v` give a circle or an
interval. -/
theorem hasSurfaceLink_singleFace [DecidableEq Γ.E] (v : Γ.V) (a : Γ.E) (ha : Γ.src a = v)
    (hpath : ∀ (b : Γ.E) (hb : Γ.src b = v),
      Nonempty (((singleFace Γ w hw hclosed).vertexLink v).Path ⟨a, ha⟩ ⟨b, hb⟩))
    (hdeg : (∀ e, Γ.src e = v → w.count (Γ.rev e) + w.count e = 2) ∨
      ∃ e₁ e₂, e₁ ≠ e₂ ∧ Γ.src e₁ = v ∧ Γ.src e₂ = v ∧ w.count (Γ.rev e₁) + w.count e₁ = 1 ∧
        w.count (Γ.rev e₂) + w.count e₂ = 1 ∧
          ∀ e, Γ.src e = v → e ≠ e₁ → e ≠ e₂ → w.count (Γ.rev e) + w.count e = 2) :
    (singleFace Γ w hw hclosed).HasSurfaceLink v := by
  refine ((singleFace Γ w hw hclosed).hasSurfaceLink_iff v).2 ⟨inferInstance,
    ((singleFace Γ w hw hclosed).vertexLink v).connected_iff.2 ⟨⟨⟨a, ha⟩⟩,
      SerreGraph.preconnected_of_forall_nonempty_path _ ⟨a, ha⟩ fun ⟨b, hb⟩ => hpath b hb⟩, ?_⟩
  rcases hdeg with hcirc | ⟨e₁, e₂, hne, he₁, he₂, h₁, h₂, h⟩
  · exact .inl fun e he => (linkDegree_singleFace e).trans (hcirc e he)
  · exact .inr ⟨e₁, e₂, hne, he₁, he₂, (linkDegree_singleFace e₁).trans h₁,
      (linkDegree_singleFace e₂).trans h₂,
      fun e he he₁ he₂ => (linkDegree_singleFace e).trans (h e he he₁ he₂)⟩

/-- A single-face complex is orientable, keeping its face as given, when any two distinct
occurrences of the same edge in its word are mutually reverse darts. -/
theorem isOrientable_singleFace
    (h : ∀ k k' : Fin w.length, k ≠ k' → (w[k'] = w[k] ∨ w[k'] = Γ.rev w[k]) →
      w[k'] = Γ.rev w[k]) :
    (singleFace Γ w hw hclosed).IsOrientable := by
  refine ((singleFace Γ w hw hclosed).isOrientable_iff).2
    ⟨fun _ => true, fun ⟨⟨⟩, k⟩ ⟨⟨⟩, k'⟩ hne hk => ?_⟩
  rw [orientedSide_of_eq_true _ rfl, orientedSide_of_eq_true _ rfl, outgoing_def, outgoing_def]
  rw [outgoing_def, outgoing_def, SerreGraph.toGeomEdge_eq_toGeomEdge_iff] at hk
  exact h k k' (fun hkk => hne (hkk ▸ rfl)) hk

end singleFace

/-- The one-vertex polygonal complex whose one-skeleton is the rose on `α` and which has a single
face, attached along the nonempty word `w`. -/
abbrev polygon {α : Type u} (w : List (α × Bool)) (hw : w ≠ []) : PolygonalComplex.{0, u, 0} :=
  singleFace (SerreGraph.rose α) w hw (by intro; rfl)

/-- The link degree of a dart in `polygon w` counts its occurrences and those of its reverse in
`w`. -/
theorem linkDegree_polygon {α : Type u} [DecidableEq α] (w : List (α × Bool)) (hw : w ≠ [])
    (e : α × Bool) : (polygon w hw).linkDegree e = w.count (e.1, !e.2) + w.count e := by
  let _ : DecidableEq (SerreGraph.rose α).E := inferInstanceAs (DecidableEq (α × Bool))
  exact linkDegree_singleFace (Γ := SerreGraph.rose α) e

theorem eulerChar_polygon {α : Type u} (w : List (α × Bool)) (hw : w ≠ []) :
    (polygon w hw).eulerChar = 2 - Nat.card α := by
  refine (eulerChar_singleFace (Γ := SerreGraph.rose α) (w := w) (hw := hw)).trans ?_
  rw [Nat.card_congr (SerreGraph.roseGeomEdgeEquiv α),
    Nat.card_unique (α := (SerreGraph.rose α).V)]
  ring

/-- In the link of the vertex of `polygon w`, the corner at position `k` joins the germ `w[k]` to
the reverse of the preceding letter. -/
theorem nonempty_vertexLink_path_polygon {α : Type u} {w : List (α × Bool)} {hw : w ≠ []}
    {a y : ((polygon w hw).vertexLink PUnit.unit).V} (b : ((polygon w hw).vertexLink PUnit.unit).V)
    (k : Fin w.length) (ha : a.1 = w[k])
    (hb : b.1 = (w[(finRotate w.length).symm k].1, !w[(finRotate w.length).symm k].2))
    (h : Nonempty (((polygon w hw).vertexLink PUnit.unit).Path b y)) :
    Nonempty (((polygon w hw).vertexLink PUnit.unit).Path a y) :=
  nonempty_vertexLink_path_singleFace b k rfl ha hb h

/-- A polygon whose link is joined from one germ to every germ, and whose letter counts give a
circle or an interval, has surface links. -/
theorem hasSurfaceLink_polygon {α : Type u} [DecidableEq α] {w : List (α × Bool)}
    {hw : w ≠ []} (a : α × Bool)
    (hpath : ∀ b : α × Bool,
      Nonempty (((polygon w hw).vertexLink PUnit.unit).Path ⟨a, rfl⟩ ⟨b, rfl⟩))
    (hdeg : (∀ e : α × Bool, w.count (e.1, !e.2) + w.count e = 2) ∨
      ∃ e₁ e₂ : α × Bool, e₁ ≠ e₂ ∧ w.count (e₁.1, !e₁.2) + w.count e₁ = 1 ∧
        w.count (e₂.1, !e₂.2) + w.count e₂ = 1 ∧
          ∀ e : α × Bool, e ≠ e₁ → e ≠ e₂ → w.count (e.1, !e.2) + w.count e = 2)
    (v : (polygon w hw).graph.V) : (polygon w hw).HasSurfaceLink v := by
  let _ : DecidableEq (SerreGraph.rose α).E := inferInstanceAs (DecidableEq (α × Bool))
  refine hasSurfaceLink_singleFace (Γ := SerreGraph.rose α) v a rfl (fun b _ => hpath b) ?_
  rcases hdeg with hcirc | ⟨e₁, e₂, hne, h₁, h₂, h⟩
  · exact .inl fun e _ => hcirc e
  · exact .inr ⟨e₁, e₂, hne, rfl, rfl, h₁, h₂, fun e _ => h e⟩

/-- A polygon is orientable, keeping its face as given, when any two distinct occurrences of the
same edge in its word are mutually reverse letters. -/
theorem isOrientable_polygon {α : Type u} {w : List (α × Bool)} {hw : w ≠ []}
    (h : ∀ k k' : Fin w.length, k ≠ k' → (w[k'] = w[k] ∨ w[k'] = (w[k].1, !w[k].2)) →
      w[k'] = (w[k].1, !w[k].2)) :
    (polygon w hw).IsOrientable :=
  isOrientable_singleFace (Γ := SerreGraph.rose α) h

end PolygonalComplex

end TauCeti
