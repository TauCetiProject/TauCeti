/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Colourings and the independence number

The colour classes of a colouring are independent sets, so each has at most `G.indepNum`
vertices. A colouring of a finite graph by `k` colours therefore has at most `k * G.indepNum`
vertices, which gives the lower bound `n ≤ χ(G) · α(G)` on the chromatic number of a graph on
`n` vertices, that is `χ(G) ≥ ⌈n / α(G)⌉`.

See Diestel, *Graph Theory*, Chapter 5, Exercise 52.
-/

public section

open Finset

namespace SimpleGraph

variable {V α : Type*} {G : SimpleGraph V} {k : ℕ}

/-- A colouring of a finite graph by a finite type `α` of colours has at most
`Fintype.card α * G.indepNum` vertices, since each colour class is an independent set. -/
theorem Coloring.card_le_card_mul_indepNum [Fintype V] [Fintype α] (C : G.Coloring α) :
    Fintype.card V ≤ Fintype.card α * G.indepNum := by
  classical
  simpa [mul_comm] using card_le_mul_card_image_of_maps_to (f := C) (s := univ) (t := univ)
    (fun _ _ ↦ mem_univ _) G.indepNum fun c _ ↦ IsIndepSet.card_le_indepNum
      (by simpa [Coloring.colorClass] using C.isIndepSet_colorClass c)

/-- A finite graph that is colourable with `k` colours has at most `k * G.indepNum` vertices. -/
theorem Colorable.card_le_mul_indepNum [Fintype V] (h : G.Colorable k) :
    Fintype.card V ≤ k * G.indepNum := by
  simpa using h.some.card_le_card_mul_indepNum

/-- The number of vertices of a finite graph is at most its chromatic number times its
independence number. -/
theorem card_le_chromaticNumber_mul_indepNum [Fintype V] :
    (Fintype.card V : ℕ∞) ≤ G.chromaticNumber * G.indepNum := by
  have h := G.colorable_chromaticNumber_of_fintype
  rw [← ENat.natCast_toNat (G.chromaticNumber_ne_top_iff_exists.mpr ⟨_, h⟩)]
  exact_mod_cast h.card_le_mul_indepNum

end SimpleGraph
