/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
import TauCeti.Combinatorics.SimpleGraph.Basic

/-!
# Symmetric differences of simple graphs

Two simple graphs `G₁` and `G₂` on the same vertex type have symmetric difference `G₁ ∆ G₂` in the
Boolean algebra `SimpleGraph V`, with adjacency given by `Xor` (`SimpleGraph.symmDiff_adj`) and
edge finsets by `G₁.edgeFinset ∆ G₂.edgeFinset` (`SimpleGraph.edgeFinset_symmDiff`). This file
provides decidable adjacency and finite edge-set instances for `G₁ ∆ G₂`, together with the vertex
triple edge-parity identity `SimpleGraph.xor_symmDiff_adj`.

## Main results

* `SimpleGraph.SymmDiff.adjDecidable`, `SimpleGraph.SymmDiff.edgeSetFintype`: decidable
  adjacency and finite edge-set instances for `G₁ ∆ G₂`.
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

/-- The edge set of `G₁ ∆ G₂` is finite whenever both `G₁.edgeSet` and `G₂.edgeSet` are finite. -/
@[instance_reducible, expose]
def SymmDiff.edgeSetFintype (G₁ G₂ : SimpleGraph V) [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] : Fintype (G₁ ∆ G₂).edgeSet :=
  Fintype.ofFinset (G₁.edgeFinset ∆ G₂.edgeFinset) fun e ↦ by
    rw [mem_symmDiff, mem_edgeFinset, mem_edgeFinset, edgeSet_symmDiff, Set.mem_symmDiff]

/-- Around any three vertices `u`, `v`, `w`, the parity of adjacent pairs among `(u, v)`, `(v, w)`,
and `(w, u)` in `G₁ ∆ G₂` is the `Xor` of those parities in `G₁` and `G₂`. -/
theorem xor_symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v w : V) :
    Xor ((G₁ ∆ G₂).Adj u v) (Xor ((G₁ ∆ G₂).Adj v w) ((G₁ ∆ G₂).Adj w u)) ↔
      Xor (Xor (G₁.Adj u v) (Xor (G₁.Adj v w) (G₁.Adj w u)))
        (Xor (G₂.Adj u v) (Xor (G₂.Adj v w) (G₂.Adj w u))) := by
  simp only [symmDiff_adj]
  grind

end SimpleGraph
