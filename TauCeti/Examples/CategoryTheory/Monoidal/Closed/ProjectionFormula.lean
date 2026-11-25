/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.CategoryTheory.Monoidal.Closed.ProjectionFormula

/-!
# Checks for projection formulas and internal Hom

For identity functors and identity adjunctions, the identity projection formula corresponds to
the identity of the internal Hom, in both forms of the duality.
-/

open CategoryTheory MonoidalCategory MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] (B : C)

-- The first form: the identity projection formula gives the identity of `ihom B`.
example : ihomLeftAdjointObjEquiv (Adjunction.id (C := C)) (Adjunction.id (C := C)) (D := C) B
    (Iso.refl _) = Iso.refl _ := by
  ext A'
  rw [ihomLeftAdjointObjEquiv_apply_hom]
  simp

-- The second form: the identity projection formula gives the identity of `ihom B`.
example : ihomRightAdjointEquiv (Adjunction.id (C := C)) B B (Iso.refl _) = Iso.refl _ := by
  ext A'
  rw [ihomRightAdjointEquiv_apply_hom]
  simp
