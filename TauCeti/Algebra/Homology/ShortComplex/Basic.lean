/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# The columns of a `3 × 3` diagram

A commutative `3 × 3` diagram is recorded as a short complex of short complexes
`D : ShortComplex (ShortComplex C)`: its objects `D.X₁`, `D.X₂`, `D.X₃` are the rows, and its
columns are `D.map ShortComplex.π₁`, `D.map ShortComplex.π₂` and `D.map ShortComplex.π₃`.

This file identifies the columns explicitly. The column `D.map ShortComplex.πᵢ` is the short
complex `ShortComplex.mk D.f.τᵢ D.g.τᵢ _` (`CategoryTheory.ShortComplex.map_π₁_eq`,
`CategoryTheory.ShortComplex.map_π₂_eq`, `CategoryTheory.ShortComplex.map_π₃_eq`). In the
opposite diagram `ShortComplex.mk (ShortComplex.opMap D.g) (ShortComplex.opMap D.f) _`, whose rows
are `D.X₃.op`, `D.X₂.op`, `D.X₁.op`, the `i`-th column is `(D.map ShortComplex.π₄₋ᵢ).op`
(`CategoryTheory.ShortComplex.opMap_map_π₁`, `CategoryTheory.ShortComplex.opMap_map_π₂`,
`CategoryTheory.ShortComplex.opMap_map_π₃`).
-/

public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (D : ShortComplex (ShortComplex C))

/-- The left column of a `3 × 3` diagram `D` is the short complex `D.f.τ₁`, `D.g.τ₁`. -/
theorem map_π₁_eq : D.map π₁ = mk D.f.τ₁ D.g.τ₁ (by simp [← comp_τ₁]) :=
  (rfl)

/-- The middle column of a `3 × 3` diagram `D` is the short complex `D.f.τ₂`, `D.g.τ₂`. -/
theorem map_π₂_eq : D.map π₂ = mk D.f.τ₂ D.g.τ₂ (by simp [← comp_τ₂]) :=
  (rfl)

/-- The right column of a `3 × 3` diagram `D` is the short complex `D.f.τ₃`, `D.g.τ₃`. -/
theorem map_π₃_eq : D.map π₃ = mk D.f.τ₃ D.g.τ₃ (by simp [← comp_τ₃]) :=
  (rfl)

/-- The left column of the opposite of a `3 × 3` diagram `D` is the opposite of its right
column. -/
theorem opMap_map_π₁ (w : opMap D.g ≫ opMap D.f = 0) : (mk _ _ w).map π₁ = (D.map π₃).op :=
  (rfl)

/-- The middle column of the opposite of a `3 × 3` diagram `D` is the opposite of its middle
column. -/
theorem opMap_map_π₂ (w : opMap D.g ≫ opMap D.f = 0) : (mk _ _ w).map π₂ = (D.map π₂).op :=
  (rfl)

/-- The right column of the opposite of a `3 × 3` diagram `D` is the opposite of its left
column. -/
theorem opMap_map_π₃ (w : opMap D.g ≫ opMap D.f = 0) : (mk _ _ w).map π₃ = (D.map π₁).op :=
  (rfl)

end CategoryTheory.ShortComplex
