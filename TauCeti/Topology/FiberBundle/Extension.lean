/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Coordinates of fibre-bundle extensions

The preferred trivialization sends a fibre-bundle extension back to its prescribed coordinate.
This is the coordinate identity underlying the local smoothness of `FiberBundle.extend`; it is
useful whenever a fibre-bundle section is compared with the constant coordinate section in the
trivialization centred at the prescribed value.
-/

public section

open Bundle Set

namespace FiberBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [∀ x, Zero (E x)] [FiberBundle F E]

/-- The preferred trivialization sends a fibre-bundle extension back to its prescribed coordinate.

This is the coordinate identity underlying the local smoothness of `FiberBundle.extend`; it is
useful whenever a fibre-bundle section is compared with the constant coordinate section in the
trivialization centred at the prescribed value. -/
@[simp]
theorem trivializationAt_extend_apply {x y : B}
    (hy : y ∈ (trivializationAt F E x).baseSet) (v₀ : E x) :
    ((trivializationAt F E x) ⟨y, FiberBundle.extend F v₀ y⟩).2 =
      ((trivializationAt F E x) ⟨x, v₀⟩).2 := by
  simp only [FiberBundle.extend]
  rwa [Trivialization.apply_mk_symm]

end FiberBundle
