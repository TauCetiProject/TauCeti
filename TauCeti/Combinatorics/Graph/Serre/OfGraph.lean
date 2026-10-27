/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import TauCeti.Combinatorics.Graph.EdgeEnds
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic

/-!
# Darts of a multigraph

Every actual edge of a Mathlib multigraph gives two distinct Serre darts, including when the
edge is a loop. The endpoints of an edge are unordered, so an arbitrary order is chosen once
for its two darts. Reversing a dart exchanges these endpoints. This construction preserves
parallel edge identities and supplies the directed paths needed for graph path groups.

## Main declarations

* `Graph.toSerreGraph`: the Serre graph of the actual vertices and edges of a multigraph.
* `Graph.toSerreGraph_isLink`: its dart incidence agrees with multigraph incidence.
* `Graph.Walk.toSerrePath`: a multigraph walk lifted to a Serre path.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

namespace Graph

variable {V : Type*} {E : Type*} (G : Graph V E)

/-- The Serre graph of a multigraph. Its darts are an actual edge and a Boolean direction.
The choice of direction uses an arbitrary ordering of each edge's two endpoints. -/
@[expose] noncomputable def toSerreGraph : TauCeti.SerreGraph where
  V := G.vertexSet
  E := G.edgeSet × Bool
  src := fun e => if e.2 then (G.edgeEnds e.1).out.1 else (G.edgeEnds e.1).out.2
  rev := fun e => (e.1, !e.2)
  rev_rev := by intro ⟨e, b⟩; cases b <;> rfl
  rev_ne := by intro ⟨e, b⟩; cases b <;> simp

@[simp] theorem toSerreGraph_rev (e : G.edgeSet × Bool) :
    G.toSerreGraph.rev e = (e.1, !e.2) := rfl

@[simp] theorem toSerreGraph_src_pos (e : G.edgeSet) :
    G.toSerreGraph.src (e, true) = (G.edgeEnds e).out.1 := rfl

@[simp] theorem toSerreGraph_src_neg (e : G.edgeSet) :
    G.toSerreGraph.src (e, false) = (G.edgeEnds e).out.2 := rfl

@[simp] theorem toSerreGraph_tgt_pos (e : G.edgeSet) :
    G.toSerreGraph.tgt (e, true) = (G.edgeEnds e).out.2 := by
  calc
    _ = G.toSerreGraph.src (G.toSerreGraph.rev (e, true)) :=
      G.toSerreGraph.tgt_def _
    _ = _ := by simpa only [toSerreGraph_rev, Bool.not_true] using G.toSerreGraph_src_neg e

@[simp] theorem toSerreGraph_tgt_neg (e : G.edgeSet) :
    G.toSerreGraph.tgt (e, false) = (G.edgeEnds e).out.1 := by
  calc
    _ = G.toSerreGraph.src (G.toSerreGraph.rev (e, false)) :=
      G.toSerreGraph.tgt_def _
    _ = _ := by simpa only [toSerreGraph_rev, Bool.not_false] using G.toSerreGraph_src_pos e

/-- The endpoints of either dart of an actual edge are exactly that edge's unordered ends. -/
theorem toSerreGraph_edgeEnds (d : G.toSerreGraph.E) :
    s(G.toSerreGraph.src d, G.toSerreGraph.tgt d) = G.edgeEnds d.1 := by
  obtain ⟨e, b⟩ := d
  cases b
  · rw [toSerreGraph_src_neg, toSerreGraph_tgt_neg]
    -- Unfold the adapter to identify its vertex subtype with the graph's actual vertices.
    change s((G.edgeEnds e).out.2, (G.edgeEnds e).out.1) = G.edgeEnds e
    exact (Sym2.eq_swap).trans (Sym2.mk_fst_out_snd_out (G.edgeEnds e))
  · rw [toSerreGraph_src_pos, toSerreGraph_tgt_pos]
    -- Unfold the adapter to identify its vertex subtype with the graph's actual vertices.
    change s((G.edgeEnds e).out.1, (G.edgeEnds e).out.2) = G.edgeEnds e
    exact Sym2.mk_fst_out_snd_out (G.edgeEnds e)

/-- A directed edge of `toSerreGraph` has precisely the incidence of its underlying edge. -/
theorem toSerreGraph_isLink (d : G.toSerreGraph.E) (x y : G.vertexSet) :
    G.IsLink d.1.1 x.1 y.1 ↔
      (G.toSerreGraph.src d = x ∧ G.toSerreGraph.tgt d = y) ∨
        (G.toSerreGraph.src d = y ∧ G.toSerreGraph.tgt d = x) := by
  obtain ⟨e, b⟩ := d
  cases b
  · simp only [toSerreGraph_src_neg, toSerreGraph_tgt_neg]
    -- Align the adapter's vertex subtype with the actual vertices before applying `Sym2.eq_iff`.
    change G.IsLink e.1 x.1 y.1 ↔
      ((G.edgeEnds e).out.2 = x ∧ (G.edgeEnds e).out.1 = y) ∨
        ((G.edgeEnds e).out.2 = y ∧ (G.edgeEnds e).out.1 = x)
    rw [← G.edgeEnds_eq_iff_isLink e x y]
    conv_lhs => rw [← Sym2.mk_fst_out_snd_out (G.edgeEnds e)]
    rw [Sym2.eq_iff]
    tauto
  · simp only [toSerreGraph_src_pos, toSerreGraph_tgt_pos]
    -- Align the adapter's vertex subtype with the actual vertices before applying `Sym2.eq_iff`.
    change G.IsLink e.1 x.1 y.1 ↔
      ((G.edgeEnds e).out.1 = x ∧ (G.edgeEnds e).out.2 = y) ∨
        ((G.edgeEnds e).out.1 = y ∧ (G.edgeEnds e).out.2 = x)
    rw [← G.edgeEnds_eq_iff_isLink e x y]
    conv_lhs => rw [← Sym2.mk_fst_out_snd_out (G.edgeEnds e)]
    rw [Sym2.eq_iff]

/-- The positive Boolean darts choose exactly one direction of every multigraph edge. -/
theorem toSerreGraph_isOrientation :
    G.toSerreGraph.IsOrientation {d | d.2 = true} := by
  apply (TauCeti.SerreGraph.isOrientation_iff G.toSerreGraph _).2
  intro ⟨e, b⟩
  cases b
  · simp only [toSerreGraph_rev]
    -- Membership in the chosen orientation is the Boolean direction test.
    change (false = true ↔ ¬(!false = true))
    decide
  · simp only [toSerreGraph_rev]
    -- Membership in the chosen orientation is the Boolean direction test.
    change (true = true ↔ ¬(!true = true))
    decide

/-- A multigraph edge is a loop exactly when either of its Serre darts is a loop. -/
theorem toSerreGraph_isLoopAt_iff (e : G.edgeSet) (x : G.vertexSet) :
    G.IsLoopAt e.1 x.1 ↔
      G.toSerreGraph.src (e, true) = x ∧ G.toSerreGraph.tgt (e, true) = x := by
  simpa only [Graph.IsLoopAt, or_self] using (G.toSerreGraph_isLink (e, true) x x)

private theorem exists_toSerreGraph_dart (e : G.edgeSet) (x y : G.vertexSet)
    (h : G.IsLink e.1 x.1 y.1) :
    ∃ d : G.toSerreGraph.E,
      d.1 = e ∧ G.toSerreGraph.src d = x ∧ G.toSerreGraph.tgt d = y := by
  obtain ⟨hs, ht⟩ | ⟨hs, ht⟩ := (G.toSerreGraph_isLink (e, true) x y).mp h
  · exact ⟨(e, true), rfl, hs, ht⟩
  · refine ⟨(e, false), rfl, ?_, ?_⟩
    · simpa only [toSerreGraph_src_neg, toSerreGraph_tgt_pos] using ht
    · simpa only [toSerreGraph_tgt_neg, toSerreGraph_src_pos] using hs

/-- A directed Serre dart over a link of a multigraph. For a loop either direction is valid;
the choice is arbitrary, and the underlying edge is unchanged. -/
noncomputable def toSerreGraphArrow (e : G.edgeSet) (x y : G.vertexSet)
    (h : G.IsLink e.1 x.1 y.1) :
    Quiver.Hom (V := G.toSerreGraph.V) x y :=
  let d := Classical.choose (G.exists_toSerreGraph_dart e x y h)
  ⟨d, (Classical.choose_spec (G.exists_toSerreGraph_dart e x y h)).2⟩

@[simp] theorem toSerreGraphArrow_edge (e : G.edgeSet) (x y : G.vertexSet)
    (h : G.IsLink e.1 x.1 y.1) :
    (G.toSerreGraphArrow e x y h).1.1 = e :=
  (Classical.choose_spec (G.exists_toSerreGraph_dart e x y h)).1

namespace Walk

variable {G}

/-- Lift a multigraph walk with actual endpoints to a directed path in its Serre graph.
Each traversal keeps its edge identity; a loop traversal chooses one of the two directions. -/
noncomputable def toSerrePath {x y : V} (p : G.Walk x y)
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) :
    G.toSerreGraph.Path ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction p with
  | nil => exact .nil
  | cons e h p ih =>
    exact (G.toSerreGraphArrow ⟨e, h.edge_mem⟩ ⟨_, hx⟩
      ⟨_, h.right_mem⟩ h).toPath.comp (ih h.right_mem hy)

@[simp] theorem toSerrePath_nil {x : V} (hx hy : x ∈ G.vertexSet) :
    toSerrePath (Graph.Walk.nil : G.Walk x x) hx hy = Quiver.Path.nil := by
  simp [toSerrePath]

@[simp] theorem toSerrePath_cons {x y z : V} (e : E) (h : G.IsLink e x y)
    (p : G.Walk y z) (hx : x ∈ G.vertexSet) (hz : z ∈ G.vertexSet) :
    toSerrePath (.cons e h p) hx hz =
      (G.toSerreGraphArrow ⟨e, h.edge_mem⟩ ⟨x, hx⟩
        ⟨y, h.right_mem⟩ h).toPath.comp (toSerrePath p h.right_mem hz) := by
  simp [toSerrePath]

end Walk

end Graph
