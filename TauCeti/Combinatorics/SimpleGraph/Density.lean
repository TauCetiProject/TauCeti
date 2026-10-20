/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Edge counts from edge densities

The number of edges of a graph between two finsets is their edge density times the product of
their sizes. When one of the finsets is empty, both sides vanish.

## Main results

* `SimpleGraph.card_interedges_eq_edgeDensity_mul`: `#(G.interedges s t) = d(s, t) |s| |t|`.
-/

public section

open Finset

namespace SimpleGraph

variable {α 𝕜 : Type*} [DivisionRing 𝕜] [CharZero 𝕜]

/-- **Edge count from edge density.** The number of edges of `G` between `s` and `t` is
`G.edgeDensity s t * (#s * #t)`, in any division ring of characteristic zero. -/
theorem card_interedges_eq_edgeDensity_mul (G : SimpleGraph α) [DecidableRel G.Adj]
    (s t : Finset α) : (#(G.interedges s t) : 𝕜) = G.edgeDensity s t * (#s * #t) := by
  rcases eq_or_ne (#s * #t) 0 with h | h
  · have : #(G.interedges s t) = 0 := Nat.eq_zero_of_le_zero (h ▸ G.card_interedges_le_mul s t)
    simp [this, ← Nat.cast_mul, h]
  · rw [edgeDensity_def]
    push_cast
    exact (div_mul_cancel₀ _ (by exact_mod_cast h)).symm

end SimpleGraph
