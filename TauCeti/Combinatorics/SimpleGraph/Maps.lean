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

/-- Pulling a window back along a map of finite labels is pulling the graph back along the
composite labels. -/
theorem comap_restrictFin {m n : ℕ} (G : SimpleGraph ℕ) (f : Fin m → Fin n) :
    SimpleGraph.comap f (G.restrictFin n) = SimpleGraph.comap (fun i => (f i : ℕ)) G := by
  ext a b; simp [restrictFin_adj]

/-- The first of two consecutive windows of a window is the window. -/
@[simp]
theorem comap_restrictFin_castAdd (G : SimpleGraph ℕ) (k l : ℕ) :
    SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)) = G.restrictFin k := by
  rw [comap_restrictFin]; ext a b; simp [restrictFin_adj]

/-- The second of two consecutive windows of a window is the window at the offset. -/
@[simp]
theorem comap_restrictFin_natAdd (G : SimpleGraph ℕ) (k l : ℕ) :
    SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))
      = SimpleGraph.comap (fun i : Fin l => k + (i : ℕ)) G := by
  rw [comap_restrictFin]; simp

/-- Pulling back along the coercion of finite labels is taking the window. -/
@[simp]
theorem comap_val (G : SimpleGraph ℕ) (n : ℕ) :
    SimpleGraph.comap (fun i : Fin n => (i : ℕ)) G = G.restrictFin n := by
  ext a b; simp [restrictFin_adj]

open Classical in
/-- The adjacency array of a graph: `true` exactly on edges. -/
noncomputable def adjArray {V : Type*} (G : SimpleGraph V) : V × V → Bool :=
  fun p => decide (G.Adj p.1 p.2)

open Classical in
/-- The adjacency array is `true` exactly on edges. -/
@[simp]
theorem adjArray_apply {V : Type*} (G : SimpleGraph V) (i j : V) :
    G.adjArray (i, j) = decide (G.Adj i j) :=
  (rfl)

/-- A graph is determined by its adjacency array. -/
theorem adjArray_injective {V : Type*} :
    Function.Injective (adjArray : SimpleGraph V → V × V → Bool) := fun G G' h => by
  ext i j
  have := congrFun h (i, j)
  simpa only [adjArray_apply, decide_eq_decide] using this

end SimpleGraph
