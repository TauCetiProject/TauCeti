/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Symmetric differences of simple graphs and cut switching

Two simple graphs `G₁` and `G₂` on the same vertex type have symmetric difference `G₁ ∆ G₂` in the
Boolean algebra `SimpleGraph V`: two vertices are adjacent in `G₁ ∆ G₂` precisely when they are
adjacent in one of `G₁`, `G₂` and not the other (`Xor`). Passing to edge sets or edge finsets
carries graph symmetric difference to set or finset symmetric difference.

Around any vertex triple `(u, v, w)`, the three cut conditions of `(⊤ : SimpleGraph V).between S Sᶜ`
cancel in pairs, so switching a graph `G` by `(⊤ : SimpleGraph V).between S Sᶜ` preserves the
parity `Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u))` of adjacent pairs among `(u, v)`, `(v, w)`,
and `(w, u)` (which counts spanned edges when `u`, `v`, `w` are pairwise distinct).

## Main results

* `SimpleGraph.SymmDiff.adjDecidable`: decidable adjacency instance for `G₁ ∆ G₂`.
* `SimpleGraph.symmDiff_adj`, `SimpleGraph.edgeSet_symmDiff`, `SimpleGraph.edgeFinset_symmDiff`:
  adjacency, edge set, and edge finset of `G₁ ∆ G₂`.
* `SimpleGraph.symmDiff_top_between_symmDiff`: switching twice by cuts `S` and `T` is switching
  once by `S ∆ T`.
* `SimpleGraph.xor_symmDiff_adj` and `SimpleGraph.xor_symmDiff_top_between_compl_adj`: adjacency
  parity around `(u, v, w)` adds modulo `2` under `∆` and is invariant under cut switching.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-- Adjacency in a symmetric difference of graphs with decidable adjacency is decidable. -/
instance SymmDiff.adjDecidable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G ∆ H).Adj :=
  inferInstanceAs <| DecidableRel fun u v ↦ Xor (G.Adj u v) (H.Adj u v)

/-- Two vertices are adjacent in `G₁ ∆ G₂` precisely when they are adjacent in exactly one of `G₁`
and `G₂`. -/
@[simp, grind =]
theorem symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v : V) :
    (G₁ ∆ G₂).Adj u v ↔ Xor (G₁.Adj u v) (G₂.Adj u v) :=
  (Iff.rfl)

/-- The edge set of `G₁ ∆ G₂` is the symmetric difference of the edge sets of `G₁` and `G₂`. -/
@[simp]
theorem edgeSet_symmDiff (G₁ G₂ : SimpleGraph V) :
    (G₁ ∆ G₂).edgeSet = G₁.edgeSet ∆ G₂.edgeSet := by
  rw [symmDiff_def, edgeSet_sup, edgeSet_sdiff, edgeSet_sdiff, symmDiff_def]

/-- The edge finset of `G₁ ∆ G₂` is the symmetric difference of the edge finsets of `G₁` and
`G₂`. -/
@[simp]
theorem edgeFinset_symmDiff (G₁ G₂ : SimpleGraph V) [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] [Fintype (G₁ ∆ G₂).edgeSet] :
    (G₁ ∆ G₂).edgeFinset = G₁.edgeFinset ∆ G₂.edgeFinset :=
  coe_injective <| by rw [coe_symmDiff, coe_edgeFinset, coe_edgeFinset, coe_edgeFinset,
    edgeSet_symmDiff]

/-- Switching `G` successively by the complete-graph cuts of `S` and `T` is switching once by the
complete-graph cut of `S ∆ T`. -/
theorem symmDiff_top_between_symmDiff (G : SimpleGraph V) (S T : Set V) :
    G ∆ (⊤ : SimpleGraph V).between S Sᶜ ∆ (⊤ : SimpleGraph V).between T Tᶜ =
      G ∆ (⊤ : SimpleGraph V).between (S ∆ T) (S ∆ T)ᶜ := by
  rw [symmDiff_assoc, ← top_between_symmDiff]

/-- Around any three vertices `u`, `v`, `w`, the parity of adjacent pairs among `(u, v)`, `(v, w)`,
and `(w, u)` in `G₁ ∆ G₂` is the `Xor` of those parities in `G₁` and `G₂`. -/
theorem xor_symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v w : V) :
    Xor ((G₁ ∆ G₂).Adj u v) (Xor ((G₁ ∆ G₂).Adj v w) ((G₁ ∆ G₂).Adj w u)) ↔
      Xor (Xor (G₁.Adj u v) (Xor (G₁.Adj v w) (G₁.Adj w u)))
        (Xor (G₂.Adj u v) (Xor (G₂.Adj v w) (G₂.Adj w u))) := by
  simp only [symmDiff_adj]
  grind

/-- Switching a graph by a complete-graph cut preserves the parity of adjacent pairs among
`(u, v)`, `(v, w)`, and `(w, u)` (which counts spanned edges when `u`, `v`, `w` are pairwise
distinct). -/
theorem xor_symmDiff_top_between_compl_adj (G : SimpleGraph V) (S : Set V) (u v w : V) :
    Xor ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj u v)
      (Xor ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj v w)
        ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj w u)) ↔
      Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) := by
  simp only [symmDiff_adj, top_between_compl_adj]
  grind

end SimpleGraph
