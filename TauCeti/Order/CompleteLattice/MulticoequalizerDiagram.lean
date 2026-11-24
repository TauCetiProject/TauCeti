/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram

/-!
# Bicartesian squares in distributive lattices

In a distributive lattice, meeting each corner of a bicartesian square (`Lattice.BicartSq`) with a
fixed element gives a bicartesian square again (`Lattice.BicartSq.inf_left`).
-/

public section

namespace Lattice.BicartSq

variable {T : Type*} [DistribLattice T] {x₁ x₂ x₃ x₄ : T}

/-- In a distributive lattice, meeting each corner of a bicartesian square with `y` gives a
bicartesian square. -/
theorem inf_left (sq : BicartSq x₁ x₂ x₃ x₄) (y : T) :
    BicartSq (y ⊓ x₁) (y ⊓ x₂) (y ⊓ x₃) (y ⊓ x₄) where
  sup_eq := by rw [← inf_sup_left, sq.sup_eq]
  inf_eq := by rw [← inf_inf_distrib_left, sq.inf_eq]

end Lattice.BicartSq
