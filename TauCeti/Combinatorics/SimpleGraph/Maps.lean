/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Pulling simple graphs back and pushing them forward

Pulling a simple graph back along a map `f : V → W` forgets everything outside the window
`Set.range f`, and pushing the result forward again recovers exactly what the window sees: the
intersection of the graph with the complete graph supported on that window. Since pushing forward
along an embedding is injective, for an embedding prescribing a pullback is therefore the same as
prescribing that intersection — a condition on an induced subgraph turned into a condition on
edges.

The window of a graph on `ℕ` spanned by the first `n` labels is the pullback along `Fin.val`; it
is how a graph on an infinite label set is read as a finite sample. A graph is also recorded by
its Boolean adjacency array.

## Main definitions

* `SimpleGraph.restrictFin` — the initial `n`-label window of a graph on `ℕ`;
* `SimpleGraph.adjArray` — the Boolean adjacency array of a graph.

## Main results

* `SimpleGraph.map_comap_eq_inf_map_top` — pushing a pullback forward cuts the graph down to the
  window;
* `SimpleGraph.comap_eq_iff_inf_map_top` — prescribing a pullback is prescribing that
  intersection;
* `SimpleGraph.map_sup` — pushing forward along any map commutes with joins;
* `SimpleGraph.restrictFin_adj` — two labels are joined in a window exactly when they are joined
  in the graph;
* `SimpleGraph.comap_restrictFin_castLE` — a window of a longer window is the shorter window;
* `SimpleGraph.adjArray_injective` — a graph is determined by its adjacency array.
-/

public section

namespace SimpleGraph

variable {V W : Type*}

/-- Pushing a pullback forward again cuts the graph down to the window seen by the map. -/
@[simp]
theorem map_comap_eq_inf_map_top (f : V → W) (G : SimpleGraph W) :
    (G.comap f).map f = G ⊓ (⊤ : SimpleGraph V).map f := by
  ext
  grind [comap_adj, inf_adj, top_adj]

/-- A pullback along an embedding is prescribed exactly by prescribing the intersection of the
graph with the window seen by the embedding. -/
theorem comap_eq_iff_inf_map_top (f : V ↪ W) (G : SimpleGraph W) (H : SimpleGraph V) :
    G.comap ⇑f = H ↔ G ⊓ (⊤ : SimpleGraph V).map ⇑f = H.map ⇑f := by
  rw [← (map_injective f).eq_iff, map_comap_eq_inf_map_top]

/-- Pushing a graph forward along any map commutes with joins: an edge of the image of `G ⊔ H`
is the image of an edge of `G` or of an edge of `H`. -/
@[simp]
theorem map_sup (f : V → W) (G H : SimpleGraph V) : (G ⊔ H).map f = G.map f ⊔ H.map f := by
  ext
  grind

/-- The window of a graph on `ℕ` spanned by the first `n` labels. -/
def restrictFin (G : SimpleGraph ℕ) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.comap (fun i => (i : ℕ)) G

/-- Two labels are joined in a window exactly when they are joined in the graph. -/
@[simp]
theorem restrictFin_adj {n : ℕ} (G : SimpleGraph ℕ) (a b : Fin n) :
    (G.restrictFin n).Adj a b ↔ G.Adj a b := Iff.rfl

/-- Pulling a window back along a map into its labels is pulling the graph back along the
composite labels. -/
theorem comap_restrictFin {α : Type*} {n : ℕ} (G : SimpleGraph ℕ) (f : α → Fin n) :
    SimpleGraph.comap f (G.restrictFin n) = SimpleGraph.comap (fun i => (f i : ℕ)) G := by
  ext; simp

/-- The first of two consecutive windows of a window is the window. -/
@[simp]
theorem comap_restrictFin_castAdd (G : SimpleGraph ℕ) (k l : ℕ) :
    SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)) = G.restrictFin k := by
  ext; simp

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
  ext; simp

/-- A window of a longer window is the shorter window: pulling the length-`n` window back along
the inclusion of `Fin m` in `Fin n` is the length-`m` window. -/
@[simp]
theorem comap_restrictFin_castLE {m n : ℕ} (G : SimpleGraph ℕ) (h : m ≤ n) :
    SimpleGraph.comap (Fin.castLE h) (G.restrictFin n) = G.restrictFin m := by
  ext; simp

open Classical in
/-- The adjacency array of a graph: `true` exactly on edges. -/
noncomputable def adjArray (G : SimpleGraph V) : V × V → Bool :=
  fun p => decide (G.Adj p.1 p.2)

open Classical in
/-- The adjacency array is `true` exactly on edges. -/
@[simp]
theorem adjArray_apply (G : SimpleGraph V) (i j : V) :
    G.adjArray (i, j) = decide (G.Adj i j) :=
  (rfl)

/-- A graph is determined by its adjacency array. -/
theorem adjArray_injective :
    Function.Injective (adjArray : SimpleGraph V → V × V → Bool) := fun G G' h => by
  ext i j
  simpa only [adjArray_apply, decide_eq_decide] using congrFun h (i, j)

end SimpleGraph
