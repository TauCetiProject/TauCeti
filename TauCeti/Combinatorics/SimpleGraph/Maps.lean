/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Pulling a simple graph back along an embedding

Pulling a simple graph back along an embedding `f : V ↪ W` forgets everything outside the window
`f '' V`, and pushing the result forward again recovers exactly what the window sees: the
intersection of the graph with the complete graph supported on that window. Since pushing forward
along an embedding is injective, prescribing a pullback is therefore the same as prescribing that
intersection — a condition on an induced subgraph turned into a condition on edges.

The window of a graph on `ℕ` spanned by the first `n` labels is the pullback along `Fin.val`; it
is how a graph on an infinite label set is read as a finite sample.

## Main definitions

* `SimpleGraph.restrictFin` — the initial `n`-label window of a graph on `ℕ`.

## Main results

* `SimpleGraph.map_comap_eq_inf_map_top` — pushing a pullback forward cuts the graph down to the
  window;
* `SimpleGraph.comap_eq_iff_inf_map_top` — prescribing a pullback is prescribing that
  intersection;
* `SimpleGraph.restrictFin_adj` — two labels are joined in a window exactly when they are joined
  in the graph.
-/

public section

namespace SimpleGraph

variable {V W : Type*}

/-- Pushing a pullback forward again cuts the graph down to the window seen by the embedding. -/
@[simp]
theorem map_comap_eq_inf_map_top (f : V ↪ W) (G : SimpleGraph W) :
    (G.comap ⇑f).map ⇑f = G ⊓ (⊤ : SimpleGraph V).map ⇑f := by
  ext u v
  simp only [map_adj, comap_adj, inf_adj, top_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨hab, a, b, fun h => hab.ne (congrArg f h), rfl, rfl⟩
  · rintro ⟨hG, a, b, -, rfl, rfl⟩
    exact ⟨a, b, hG, rfl, rfl⟩

/-- A pullback along an embedding is prescribed exactly by prescribing the intersection of the
graph with the window seen by the embedding. -/
theorem comap_eq_iff_inf_map_top (f : V ↪ W) (G : SimpleGraph W) (H : SimpleGraph V) :
    G.comap ⇑f = H ↔ G ⊓ (⊤ : SimpleGraph V).map ⇑f = H.map ⇑f := by
  rw [← (map_injective f).eq_iff, map_comap_eq_inf_map_top]

/-- The window of a graph on `ℕ` spanned by the first `n` labels. -/
def restrictFin (G : SimpleGraph ℕ) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.comap (fun i => (i : ℕ)) G

@[simp]
theorem restrictFin_adj {n : ℕ} (G : SimpleGraph ℕ) (a b : Fin n) :
    (G.restrictFin n).Adj a b ↔ G.Adj a b := Iff.rfl

end SimpleGraph
