/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Isomorphism

/-!
# Complete labelled graphs

A labelled graph is complete when every vertex has an outgoing dart with each signed letter
as its label. A folded complete graph is what Kapovich and Myasnikov call a regular graph:
every vertex has exactly one outgoing dart with each label. In a complete graph every word
labels a path from every vertex, so every element of the free group is read along a path
from the base vertex. A labelled morphism from a complete graph to a folded graph all of
whose vertices are reachable from its base vertex is surjective on vertices. Completeness
passes to the target of a labelled morphism which is surjective on vertices, and is invariant
under isomorphism.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 8, Definition 8.1.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} (S : StallingsGraph α) {T : StallingsGraph α}

/-- A labelled graph is complete if every vertex has an outgoing dart with each signed letter
as its label. -/
def IsComplete : Prop :=
  ∀ (v : S.graph.V) (l : α × Bool), ∃ e : S.graph.E, S.graph.src e = v ∧ S.label e = l

/-- Completeness is existence of an outgoing dart with every label at every vertex. -/
theorem isComplete_def : S.IsComplete ↔
    ∀ (v : S.graph.V) (l : α × Bool), ∃ e : S.graph.E, S.graph.src e = v ∧ S.label e = l :=
  Iff.rfl

/-- The rose is complete: its only vertex carries a petal for each signed letter. -/
theorem rose_isComplete (α : Type*) : (rose α).IsComplete :=
  fun _ l => ⟨l, rfl, rfl⟩

variable {S}

/-- In a complete graph every vertex has an outgoing dart with each signed letter as its
label. -/
theorem IsComplete.exists_dart (hS : S.IsComplete) (v : S.graph.V) (l : α × Bool) :
    ∃ e : S.graph.E, S.graph.src e = v ∧ S.label e = l :=
  hS v l

/-- In a complete graph every word labels a path starting at any given vertex. -/
theorem IsComplete.exists_path_word (hS : S.IsComplete) (a : S.graph.V)
    (w : List (α × Bool)) : ∃ (b : S.graph.V) (p : S.graph.Path a b), S.word p = w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨a, .nil, S.word_nil a⟩
  | append_singleton w l ih =>
    obtain ⟨b, p, rfl⟩ := ih
    obtain ⟨e, rfl, rfl⟩ := hS.exists_dart b l
    exact ⟨S.graph.tgt e, p.cons (S.graph.dart e), by simp⟩

/-- In a complete graph every element of the free group is read along a path starting at any
given vertex. -/
theorem IsComplete.exists_path_read (hS : S.IsComplete) (a : S.graph.V) (g : FreeGroup α) :
    ∃ (b : S.graph.V) (p : S.graph.Path a b), S.read p = g := by
  classical
  obtain ⟨b, p, hp⟩ := hS.exists_path_word a g.toWord
  exact ⟨b, p, by rw [S.read_eq_mk_word, hp, FreeGroup.mk_toWord]⟩

/-- A labelled morphism from a complete graph to a folded graph all of whose vertices are
reachable from its base vertex is surjective on vertices. -/
theorem IsComplete.surjective_mapV (hS : S.IsComplete) (f : S.Hom T) (hT : T.IsFolded)
    (hreach : ∀ v : T.graph.V, Nonempty (T.graph.Path T.base v)) :
    Function.Surjective f.graphHom.mapV := by
  intro v
  obtain ⟨q⟩ := hreach v
  rw [← f.map_base] at q
  obtain ⟨b, p, hp⟩ := hS.exists_path_word S.base (T.word q)
  exact ⟨b, hT.eq_tgt_of_word_eq T (f.graphHom.toPrefunctor.mapPath p) q
    ((f.word_mapPath p).trans hp)⟩

/-- The target of a labelled morphism which is surjective on vertices is complete if the
source is. -/
theorem IsComplete.of_surjective (hS : S.IsComplete) (f : S.Hom T)
    (hf : Function.Surjective f.graphHom.mapV) : T.IsComplete := by
  intro v l
  obtain ⟨v, rfl⟩ := hf v
  obtain ⟨e, rfl, rfl⟩ := hS.exists_dart v l
  exact ⟨f.graphHom.mapE e, f.graphHom.map_src e, f.map_label e⟩

/-- Isomorphic labelled graphs are complete together. -/
theorem Iso.isComplete_iff (f : Iso S T) : S.IsComplete ↔ T.IsComplete :=
  ⟨fun h => h.of_surjective f.toHom fun v => ⟨f.vertexEquiv.symm v, by simp⟩,
    fun h => h.of_surjective f.symm.toHom fun v => ⟨f.vertexEquiv v, by simp⟩⟩

end TauCeti.StallingsGraph
