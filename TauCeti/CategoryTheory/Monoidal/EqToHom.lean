/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Tensor products of transports along object equalities

The tensor product of two morphisms `eqToHom h` and `eqToHom h'` is the transport along the induced
equality of tensor products. This complements Mathlib's `MonoidalCategory.whiskerLeft_eqToHom` and
`MonoidalCategory.eqToHom_whiskerRight`, which treat whiskering.

## Main results

* `TauCeti.eqToHom_tensorHom_eqToHom`: `eqToHom h ⊗ₘ eqToHom h' = eqToHom _`.
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor product of two transports along object equalities is the transport along the
induced equality of tensor products. -/
@[simp]
theorem eqToHom_tensorHom_eqToHom {X X' Y Y' : C} (h : X = X') (h' : Y = Y') :
    (eqToHom h ⊗ₘ eqToHom h') = eqToHom (congrArg₂ (· ⊗ ·) h h') := by
  subst h h'
  simp

end TauCeti
