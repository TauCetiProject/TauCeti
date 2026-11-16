/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import TauCeti.Combinatorics.Graph.Serre.Core

/-!
# Labelled graphs presented by their positive edges

A based labelled graph is usually drawn as a directed graph whose edges carry letters of the
alphabet: each drawn edge stands for a dart reading its letter and for the reverse dart reading
the inverse letter. `StallingsGraph.ofDigraph` builds the based labelled Serre graph of such a
picture from the family of drawn edges, with loops and parallel edges allowed.

Foldedness of the result is the condition on the picture that no vertex is the origin of two
edges with the same letter, nor the terminus of two edges with the same letter. The graph is a
core at its base vertex as soon as every vertex is reachable and every drawn edge lies on a
reduced loop at the base.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 2, Definitions 2.1 and 2.3.
-/

public section

namespace TauCeti.StallingsGraph

variable {α V ι : Type*} (base : V) (src tgt : ι → V) (label : ι → α)

/-- The based labelled graph with vertices `V` and one edge for each `i : ι`, running from
`src i` to `tgt i` and reading the letter `label i`. Its darts are the pairs `(i, true)`, the
edge `i` traversed forwards, and `(i, false)`, the same edge traversed backwards and reading
the inverse letter. -/
abbrev ofDigraph : StallingsGraph α where
  graph := {
    V := V
    E := ι × Bool
    src := fun e => bif e.2 then src e.1 else tgt e.1
    rev := fun e => (e.1, !e.2)
    rev_rev := by intro ⟨e, b⟩; cases b <;> rfl
    rev_ne := by intro ⟨e, b⟩; cases b <;> simp }
  base := base
  label := fun e => (label e.1, e.2)
  label_rev := fun _ => rfl

@[simp] theorem ofDigraph_base : (ofDigraph base src tgt label).base = base := rfl

@[simp] theorem ofDigraph_label (e : ι × Bool) :
    (ofDigraph base src tgt label).label e = (label e.1, e.2) := rfl

@[simp] theorem ofDigraph_rev (e : ι × Bool) :
    (ofDigraph base src tgt label).graph.rev e = (e.1, !e.2) := rfl

@[simp] theorem ofDigraph_src_forward (i : ι) :
    (ofDigraph base src tgt label).graph.src (i, true) = src i := rfl

@[simp] theorem ofDigraph_src_backward (i : ι) :
    (ofDigraph base src tgt label).graph.src (i, false) = tgt i := rfl

@[simp] theorem ofDigraph_tgt_forward (i : ι) :
    (ofDigraph base src tgt label).graph.tgt (i, true) = tgt i := rfl

@[simp] theorem ofDigraph_tgt_backward (i : ι) :
    (ofDigraph base src tgt label).graph.tgt (i, false) = src i := rfl

/-- The graph of a labelled directed graph is folded exactly when no two distinct edges with
the same letter share their origin, and no two share their terminus. -/
theorem ofDigraph_isFolded_iff :
    (ofDigraph base src tgt label).IsFolded ↔
      (∀ i j, src i = src j → label i = label j → i = j) ∧
        ∀ i j, tgt i = tgt j → label i = label j → i = j := by
  rw [isFolded_def]
  constructor
  · intro h
    exact ⟨fun i j hs hl => congrArg Prod.fst (h (i, true) (j, true) hs (by simp [hl])),
      fun i j ht hl => congrArg Prod.fst (h (i, false) (j, false) ht (by simp [hl]))⟩
  · rintro ⟨hs, ht⟩ ⟨i, b⟩ ⟨j, c⟩ h hl
    obtain ⟨hl, rfl⟩ := Prod.mk.inj hl
    cases b
    · exact congrArg (fun k => (k, false)) (ht i j h hl)
    · exact congrArg (fun k => (k, true)) (hs i j h hl)

/-- The graph of a labelled directed graph is a core at its base vertex when every vertex is
reachable from the base and every edge, traversed forwards, lies on a reduced loop at the
base. -/
theorem ofDigraph_isCore
    (hreach : ∀ v : V, Nonempty ((ofDigraph base src tgt label).graph.Path base v))
    (h : ∀ i : ι, (i, true) ∈ (ofDigraph base src tgt label).graph.coreDarts base) :
    (ofDigraph base src tgt label).graph.IsCore base := by
  refine ((ofDigraph base src tgt label).graph.isCore_iff base).mpr ⟨hreach, fun e =>
    ((ofDigraph base src tgt label).graph.mem_coreDarts_iff base e).mp ?_⟩
  obtain ⟨i, _ | _⟩ := e
  · exact ((ofDigraph base src tgt label).graph.rev_mem_coreDarts_iff base (i, true)).mpr (h i)
  · exact h i

end TauCeti.StallingsGraph
