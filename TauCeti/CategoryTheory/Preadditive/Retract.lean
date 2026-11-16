/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Retract

/-!
# The complement of a retract in a preadditive category

If `X` is a retract of `Y` in a preadditive category, with `r.i : X ⟶ Y` and `r.r : Y ⟶ X`, then
`𝟙 Y - r.r ≫ r.i` is an idempotent of `Y` killing `X`. It induces a section of
`cokernel.π r.i`, so the complement `cokernel r.i` of `X` in `Y` is again a retract of `Y`
(`CategoryTheory.Retract.cokernel`).

## Main definitions

* `CategoryTheory.Retract.cokernel`: the cokernel of `r.i` is a retract of `Y`.
-/

public section

universe v u

namespace CategoryTheory.Retract

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **The complement of a retract is a retract.** If `X` is a retract of `Y`, then so is
`cokernel r.i`: it embeds into `Y` through the idempotent `𝟙 Y - r.r ≫ r.i`, which kills `X`, and
`cokernel.π r.i` retracts this embedding. -/
@[expose, simps]
noncomputable def cokernel {X Y : C} (r : Retract X Y) [HasCokernel r.i] :
    Retract (Limits.cokernel r.i) Y where
  i := Limits.cokernel.desc r.i (𝟙 Y - r.r ≫ r.i) (by simp)
  r := Limits.cokernel.π r.i
  retract := by
    ext
    simp

end CategoryTheory.Retract
