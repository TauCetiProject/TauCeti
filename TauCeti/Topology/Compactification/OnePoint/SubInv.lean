/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Translation and inversion of one-point targets

`OnePoint.subInv` reads a target in the finite coordinate obtained by subtracting a base point
and inverting. This lets approximation to infinity be treated as approximation to zero.
-/

public section

open scoped OnePoint

namespace OnePoint

variable {F : Type*} [Zero F] [Sub F] [Inv F]

/-- Subtract `c` and invert at a finite target, and send infinity to zero. The map has values
in `F`, so at the finite target `c` it uses the same total formula as at any finite point. -/
def subInv (t : OnePoint F) (c : F) : F :=
  t.elim 0 fun a ↦ (a - c)⁻¹

/-- Infinity is transported to zero. -/
@[simp, grind =]
theorem subInv_infty (c : F) : (∞ : OnePoint F).subInv c = 0 := (rfl)

/-- A finite target is transported by subtracting the base point and inverting. -/
@[simp, grind =]
theorem subInv_coe (a c : F) : (a : OnePoint F).subInv c = (a - c)⁻¹ := (rfl)

end OnePoint
