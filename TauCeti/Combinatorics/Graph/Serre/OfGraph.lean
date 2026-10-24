/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import TauCeti.Combinatorics.Graph.Connectivity.Component
public import TauCeti.Combinatorics.Graph.EdgeEnds
public import TauCeti.Combinatorics.Graph.Serre.Basic

/-!
# The Serre graph of a multigraph

`Graph.toSerreGraph` replaces each actual edge of a multigraph by two darts, including for
loops, and uses only its actual vertices. An ordering chosen for each unordered endpoint pair
determines the source of each dart. Parallel edges retain their original identities.

`Graph.serrePathToWalk` forgets dart directions and retains the sequence of edge identities.
Every native walk between actual vertices lifts, so this comparison also preserves reachability
and nonempty connectedness. In particular, the two directions of a loop can project to the same
walk; no injectivity assertion is made.

The construction uses Mathlib's `Graph` incidence and `Quiver.Path` APIs, with endpoint choices
provided by `Graph.edgeEnds` and `Sym2.out`.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.1–2.2.
-/

public section

universe u v

namespace Graph

variable {V : Type u} {E : Type v} (G : Graph V E)

/-- The Serre graph on the actual vertices and edges of a multigraph. Each edge has two
distinct darts, even when it is a loop. The structure assembly is exposed to identify its
vertex and dart carriers; the endpoint choice remains in `Graph.edgeEnds`. -/
@[expose, instance_reducible] noncomputable def toSerreGraph : TauCeti.SerreGraph.{u, v} where
  V := G.vertexSet
  E := G.edgeSet × Bool
  src := fun d => if d.2 then (G.edgeEnds d.1).out.2 else (G.edgeEnds d.1).out.1
  rev := fun d => (d.1, !d.2)
  rev_rev := by intro ⟨e, b⟩; cases b <;> rfl
  rev_ne := by intro ⟨e, b⟩; cases b <;> simp

/-- The sign selects one of the two chosen endpoints. -/
@[simp] theorem toSerreGraph_src (d : G.edgeSet × Bool) :
    G.toSerreGraph.src d =
      if d.2 then (G.edgeEnds d.1).out.2 else (G.edgeEnds d.1).out.1 := (rfl)

/-- Reversal changes only the sign, retaining the edge identity. -/
@[simp] theorem toSerreGraph_rev (d : G.edgeSet × Bool) :
    G.toSerreGraph.rev d = (d.1, !d.2) := (rfl)

/-- The target is the other chosen endpoint. -/
@[simp] theorem toSerreGraph_tgt (d : G.edgeSet × Bool) :
    G.toSerreGraph.tgt d =
      if d.2 then (G.edgeEnds d.1).out.1 else (G.edgeEnds d.1).out.2 := by
  rw [TauCeti.SerreGraph.tgt_def, toSerreGraph_rev, toSerreGraph_src]
  cases d.2 <;> rfl

/-- Each dart traverses its original multigraph edge. -/
theorem toSerreGraph_isLink (d : G.edgeSet × Bool) :
    G.IsLink d.1.1 (G.toSerreGraph.src d).1 (G.toSerreGraph.tgt d).1 := by
  have h := (G.edgeEnds_eq_iff_isLink d.1
    (G.edgeEnds d.1).out.1 (G.edgeEnds d.1).out.2).mp
      (Sym2.mk_fst_out_snd_out (G.edgeEnds d.1)).symm
  cases d with
  | mk e b => cases b <;> simp only [toSerreGraph_src, toSerreGraph_tgt] <;>
      first | exact h | exact h.symm

/-- Incidence with an original edge means being a source or target of either of its darts. -/
theorem toSerreGraph_inc_iff (d : G.edgeSet × Bool) (x : G.vertexSet) :
    G.Inc d.1.1 x.1 ↔ x = G.toSerreGraph.src d ∨ x = G.toSerreGraph.tgt d := by
  rw [← G.mem_edgeEnds_iff]
  rw [← Sym2.mk_fst_out_snd_out (G.edgeEnds d.1), Sym2.mem_iff]
  rcases d with ⟨e, b⟩
  cases b <;> simp [or_comm]

/-- Every traversal of an actual edge is represented by a dart with those ordered endpoints. -/
theorem toSerreGraph_exists_dart_iff (e : G.edgeSet) (x y : G.vertexSet) :
    (∃ b : Bool, G.toSerreGraph.src (e, b) = x ∧ G.toSerreGraph.tgt (e, b) = y) ↔
      G.IsLink e.1 x.1 y.1 := by
  constructor
  · rintro ⟨b, hx, hy⟩
    simpa only [hx, hy] using G.toSerreGraph_isLink (e, b)
  · intro h
    have he := (G.edgeEnds_eq_iff_isLink e x y).mpr h
    have ho := (Sym2.mk_fst_out_snd_out (G.edgeEnds e)).trans he
    rcases Sym2.eq_iff.mp ho with hxy | hyx
    · exact ⟨false, by simpa using hxy.1, by simpa using hxy.2⟩
    · exact ⟨true, by simpa using hyx.2, by simpa using hyx.1⟩

/-- The multigraph incidence carried by an arrow of the associated quiver. -/
theorem toSerreGraph_hom_isLink {x y : G.vertexSet}
    (f : @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver x y) :
    G.IsLink f.1.1.1 x.1 y.1 := by
  simpa only [f.2.1, f.2.2] using G.toSerreGraph_isLink f.1

/-- Forget dart directions in an indexed Serre path, keeping each original edge identity. -/
def serrePathToWalk {x : G.vertexSet} :
    ∀ {y : G.vertexSet}, G.toSerreGraph.Path x y → G.Walk x.1 y.1
  | _, .nil => .nil
  | _, .cons p f => (serrePathToWalk p).append (G.toSerreGraph_hom_isLink f).toWalk

@[simp] theorem serrePathToWalk_nil (x : G.vertexSet) :
    G.serrePathToWalk (Quiver.Path.nil : G.toSerreGraph.Path x x) = .nil := (rfl)

/-- Appending a dart appends the one-edge native walk. -/
@[simp] theorem serrePathToWalk_cons {x y z : G.vertexSet}
    (p : G.toSerreGraph.Path x y)
    (f : @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver y z) :
    G.serrePathToWalk (p.cons f) =
      (G.serrePathToWalk p).append (G.toSerreGraph_hom_isLink f).toWalk := (rfl)

/-- Path composition projects to native walk concatenation. -/
@[simp] theorem serrePathToWalk_comp {x y z : G.vertexSet}
    (p : G.toSerreGraph.Path x y) (q : G.toSerreGraph.Path y z) :
    G.serrePathToWalk (p.comp q) =
      (G.serrePathToWalk p).append (G.serrePathToWalk q) := by
  induction q with
  | nil => simp [serrePathToWalk]
  | cons q f ih => simp [serrePathToWalk, ih, Walk.append_assoc]

/-- Reversing a Serre path reverses its native walk. The original edge identity is unchanged
when a dart is reversed, including for loops. -/
@[simp] theorem serrePathToWalk_reverse {x y : G.vertexSet}
    (p : G.toSerreGraph.Path x y) :
    G.serrePathToWalk p.reverse = (G.serrePathToWalk p).reverse := by
  let := G.toSerreGraph.toQuiver
  let := G.toSerreGraph.toQuiverHasInvolutiveReverse
  induction p with
  | nil => simp [serrePathToWalk]
  | cons p f ih =>
    rw [Quiver.Path.reverse, serrePathToWalk_comp]
    have he : (Quiver.reverse f).1.1.1 = f.1.1.1 := by
      rw [G.toSerreGraph.reverse_val f, toSerreGraph_rev]
    simp [serrePathToWalk, Quiver.Hom.toPath, ih, he, IsLink.reverse_toWalk]

/-- Projection preserves the number of traversals, including loops. -/
@[simp] theorem length_serrePathToWalk {x y : G.vertexSet}
    (p : G.toSerreGraph.Path x y) : (G.serrePathToWalk p).length = p.length := by
  induction p with
  | nil => simp [serrePathToWalk]
  | cons p f ih => simp [serrePathToWalk, ih]

/-- The edge sequence of the projected walk is the path's ordered word of original edges.
The free-monoid weight forgets only the dart signs. -/
theorem edges_serrePathToWalk {x y : G.vertexSet} (p : G.toSerreGraph.Path x y) :
    (G.serrePathToWalk p).edges =
      (p.weight (fun {a b} (f : @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver a b) =>
        FreeMonoid.of f.1.1.1)).toList := by
  induction p with
  | nil => simp [serrePathToWalk]
  | cons p f ih => simp [serrePathToWalk, ih]

/-- Every native walk between actual vertices is the projection of a Serre path. In the loop
case this chooses one of the two available directions without identifying them. -/
theorem serrePathToWalk_surjective {x y : V} (hx : x ∈ G.vertexSet)
    (hy : y ∈ G.vertexSet) :
    Function.Surjective (G.serrePathToWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)) := by
  suffices ∀ {a b : V} (p : G.Walk a b) (ha : a ∈ G.vertexSet) (hb : b ∈ G.vertexSet),
      ∃ q : G.toSerreGraph.Path ⟨a, ha⟩ ⟨b, hb⟩, G.serrePathToWalk q = p from
    fun p => this p hx hy
  intro a b p ha hb
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons x y z e h p ih =>
    obtain ⟨q, hq⟩ := ih h.right_mem hb
    obtain ⟨b, hb, ht⟩ :=
      (G.toSerreGraph_exists_dart_iff ⟨e, h.edge_mem⟩ ⟨x, ha⟩ ⟨y, h.right_mem⟩).mpr h
    let f : @Quiver.Hom G.toSerreGraph.V G.toSerreGraph.toQuiver
        ⟨x, ha⟩ ⟨y, h.right_mem⟩ := ⟨(⟨e, h.edge_mem⟩, b), hb, ht⟩
    refine ⟨f.toPath.comp q, ?_⟩
    simp [Quiver.Hom.toPath, hq, IsLink.toWalk_eq_cons, f]

/-- Serre path reachability agrees with native reachability on the actual vertices. -/
theorem nonempty_serrePath_iff_reachable (x y : G.vertexSet) :
    Nonempty (G.toSerreGraph.Path x y) ↔ G.Reachable x.1 y.1 := by
  constructor
  · rintro ⟨p⟩
    exact (G.serrePathToWalk p).reachable x.property
  · intro h
    obtain ⟨_, ⟨p⟩⟩ := reachable_def.mp h
    obtain ⟨q, _⟩ := G.serrePathToWalk_surjective x.property y.property p
    exact ⟨q⟩

/-- Native connectedness is nonemptiness together with pairwise Serre path reachability. -/
theorem connected_iff_nonempty_serrePath :
    G.Connected ↔ Nonempty G.toSerreGraph.V ∧
      ∀ x y : G.toSerreGraph.V, Nonempty (G.toSerreGraph.Path x y) := by
  rw [connected_iff_forall_reachable]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨Set.nonempty_coe_sort.mpr hne, fun x y =>
      (G.nonempty_serrePath_iff_reachable x y).mpr (h x.property y.property)⟩
  · rintro ⟨hne, h⟩
    exact ⟨Set.nonempty_coe_sort.mp hne, fun {_ _} hx hy =>
      (G.nonempty_serrePath_iff_reachable ⟨_, hx⟩ ⟨_, hy⟩).mp (h _ _)⟩

end Graph
