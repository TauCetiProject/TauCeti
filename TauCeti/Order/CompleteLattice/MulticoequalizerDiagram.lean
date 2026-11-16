/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram

/-!
# Bicartesian squares in distributive lattices

In a distributive lattice, intersecting the four corners of a bicartesian square
(`Lattice.BicartSq`) with a fixed element gives a bicartesian square again.

## Main results

* `Lattice.BicartSq.inf_left`: for a bicartesian square `x₁, x₂, x₃, x₄` and an element `s`,
  the elements `s ⊓ x₁, s ⊓ x₂, s ⊓ x₃, s ⊓ x₄` form a bicartesian square.
-/

public section

namespace Lattice.BicartSq

variable {T : Type*} [DistribLattice T] {x₁ x₂ x₃ x₄ : T}

/-- Intersecting a bicartesian square in a distributive lattice with a further element `s` gives a
bicartesian square. -/
lemma inf_left (sq : BicartSq x₁ x₂ x₃ x₄) (s : T) :
    BicartSq (s ⊓ x₁) (s ⊓ x₂) (s ⊓ x₃) (s ⊓ x₄) where
  sup_eq := by rw [← sq.sup_eq, inf_sup_left]
  inf_eq := by rw [← sq.inf_eq, ← inf_inf_distrib_left]

end Lattice.BicartSq
