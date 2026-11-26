/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Subgraphs of simple graphs

This file collects general lemmas for `SimpleGraph.Subgraph` extending Mathlib's subgraph API.

## Main results

* `SimpleGraph.Subgraph.encard_edgeSet_map`: mapping a subgraph along an injective graph
  homomorphism preserves its edge-set extended cardinality `Set.encard` in `ℕ∞`.
-/

public section

namespace SimpleGraph.Subgraph

variable {V W : Type*}

/-- Mapping a subgraph along an injective graph homomorphism preserves its edge-set extended
cardinality `Set.encard` in `ℕ∞`. -/
theorem encard_edgeSet_map {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    (hf : Function.Injective f) (M : G.Subgraph) :
    (M.map f).edgeSet.encard = M.edgeSet.encard := by
  rw [Subgraph.edgeSet_map, (Sym2.map.injective hf).encard_image]

end SimpleGraph.Subgraph
