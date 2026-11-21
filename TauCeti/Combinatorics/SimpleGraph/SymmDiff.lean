/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Symmetric differences of simple graphs

Two simple graphs `G₁` and `G₂` on the same vertex type have symmetric difference `G₁ ∆ G₂` in the
Boolean algebra `SimpleGraph V`: two vertices are adjacent in `G₁ ∆ G₂` precisely when they are
adjacent in one of `G₁`, `G₂` and not the other (`Xor`). Passing to edge sets or edge finsets
carries graph symmetric difference to set or finset symmetric difference.

Around any vertex triple `(u, v, w)`, the parity `Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u))`
of adjacent pairs among `(u, v)`, `(v, w)`, and `(w, u)` adds modulo `2` under `∆`
(`SimpleGraph.xor_symmDiff_adj`).

## Main results

* `SimpleGraph.SymmDiff.adjDecidable`, `SimpleGraph.SymmDiff.edgeSetFintype`: decidable
  adjacency and finite edge-set instances for `G₁ ∆ G₂`.
* `SimpleGraph.symmDiff_adj`, `SimpleGraph.edgeSet_symmDiff`, `SimpleGraph.edgeFinset_symmDiff`:
  adjacency, edge set, and edge finset of `G₁ ∆ G₂`.
* `SimpleGraph.xor_symmDiff_adj`: adjacency parity around `(u, v, w)` adds modulo `2` under `∆`.
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

/-- The edge set of `G₁ ∆ G₂` is finite whenever both `G₁.edgeSet` and `G₂.edgeSet` are finite. -/
instance SymmDiff.edgeSetFintype (G₁ G₂ : SimpleGraph V) [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] : Fintype (G₁ ∆ G₂).edgeSet :=
  Fintype.ofFinset (G₁.edgeFinset ∆ G₂.edgeFinset) fun e ↦ by
    rw [mem_symmDiff, mem_edgeFinset, mem_edgeFinset, edgeSet_symmDiff, Set.mem_symmDiff]

/-- The edge finset of `G₁ ∆ G₂` is the symmetric difference of the edge finsets of `G₁` and
`G₂`. -/
@[simp]
theorem edgeFinset_symmDiff (G₁ G₂ : SimpleGraph V) [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] [Fintype (G₁ ∆ G₂).edgeSet] :
    (G₁ ∆ G₂).edgeFinset = G₁.edgeFinset ∆ G₂.edgeFinset :=
  coe_injective <| by rw [coe_symmDiff, coe_edgeFinset, coe_edgeFinset, coe_edgeFinset,
    edgeSet_symmDiff]

/-- Around any three vertices `u`, `v`, `w`, the parity of adjacent pairs among `(u, v)`, `(v, w)`,
and `(w, u)` in `G₁ ∆ G₂` is the `Xor` of those parities in `G₁` and `G₂`. -/
theorem xor_symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v w : V) :
    Xor ((G₁ ∆ G₂).Adj u v) (Xor ((G₁ ∆ G₂).Adj v w) ((G₁ ∆ G₂).Adj w u)) ↔
      Xor (Xor (G₁.Adj u v) (Xor (G₁.Adj v w) (G₁.Adj w u)))
        (Xor (G₂.Adj u v) (Xor (G₂.Adj v w) (G₂.Adj w u))) := by
  simp only [symmDiff_adj]
  grind

end SimpleGraph
