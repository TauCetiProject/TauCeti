/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity

/-!
# Multigraph vertex-connectivity examples

These examples distinguish the empty graph, a singleton with arbitrarily many loops, and two
vertices joined by a nonempty edge set. The ambient types are infinite; the last example also
allows infinitely many parallel edges. Only the actual vertex set determines the size bound for
vertex connectivity.
-/

open Graph Set

example : (⊥ : Graph ℕ ℕ).vertexConnectivity = 0 := by
  have : IsEmpty V((⊥ : Graph ℕ ℕ)) := by rw [vertexSet_bot]; infer_instance
  simp

example : ¬(⊥ : Graph ℕ ℕ).IsVertexConnected 0 := by
  simp

example (F : Set ℕ) : (bouquet (7 : ℕ) F).vertexConnectivity = 0 := by
  have : Subsingleton V(bouquet (7 : ℕ) F) := by
    rw [vertexSet_bouquet]
    infer_instance
  simp

example (F : Set ℕ) : ¬(bouquet (7 : ℕ) F).IsVertexConnected 1 := by
  simp

-- This includes a single edge (`F = {37}`) and infinitely many parallel edges (`F = univ`).
example (F : Set ℕ) (hF : F.Nonempty) :
    (banana (0 : ℕ) 1 F).vertexConnectivity = 1 := by
  let G := banana (0 : ℕ) 1 F
  have : Nonempty V(G) := ⟨⟨0, by simp [G]⟩⟩
  have hnt : V(G).Nontrivial := ⟨0, by simp [G], 1, by simp [G], by decide⟩
  have h1 : G.IsVertexConnected 1 := isVertexConnected_one.mpr
    ⟨componentCount_eq_one_iff.mp (componentCount_banana hF), hnt⟩
  have hcard : ENat.card V(G) = 2 := by simp [G]
  have hu : G.vertexConnectivity + 1 ≤ (1 : ℕ∞) + 1 := by
    simpa only [hcard, one_add_one_eq_two] using G.vertexConnectivity_add_one_le_card
  exact le_antisymm ((ENat.add_le_add_iff_right ENat.one_ne_top).mp hu)
    ((isVertexConnected_iff_le_vertexConnectivity 1).mp h1)
