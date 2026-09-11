/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Disjoint sums of graphs

Two gaps in Mathlib's `SimpleGraph.sum` API.

`SimpleGraph.sum` has no `DecidableRel` instance in Mathlib. Consequently, even when adjacency in
both summands is decidable, `(G ⊕g H).edgeFinset` is not expressible without supplying an
instance. `TauCeti.instDecidableRelSumAdj` supplies it by the four-way case split in the definition
of `SimpleGraph.sum`.

`SimpleGraph.sum` has no `bot` law in Mathlib either: `TauCeti.SimpleGraph.sum_bot_bot` says a
disjoint sum of edgeless graphs is edgeless, the form in which a graph parameter that is
multiplicative over disjoint sums is evaluated on an edgeless graph.

## Main results

* `TauCeti.instDecidableRelSumAdj` — adjacency in a disjoint sum is decidable;
* `TauCeti.SimpleGraph.sum_bot_bot` — a disjoint sum of edgeless graphs is edgeless.
-/

public section

namespace TauCeti

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Adjacency in a disjoint sum of graphs is decidable: `SimpleGraph.sum` splits on which sides its
two arguments lie, and vertices on opposite sides are never adjacent. -/
instance instDecidableRelSumAdj (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | .inl u, .inl v => ‹DecidableRel G.Adj› u v
  | .inr u, .inr v => ‹DecidableRel H.Adj› u v
  | .inl _, .inr _ => isFalse (by simp)
  | .inr _, .inl _ => isFalse (by simp)

namespace SimpleGraph

/-- A disjoint sum of edgeless graphs is edgeless: no edge is contributed by either summand, and
none across the two sides. -/
theorem sum_bot_bot : ((⊥ : SimpleGraph V) ⊕g (⊥ : SimpleGraph W)) = ⊥ := by
  ext u v
  cases u <;> cases v <;> simp

end SimpleGraph

end TauCeti
