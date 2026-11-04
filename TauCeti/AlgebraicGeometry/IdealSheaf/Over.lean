/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Over

/-!
# Closed subschemes of a scheme over a base

If `X` is a scheme over `S` and `I` is an ideal sheaf on `X`, the closed subscheme `V(I)` is a
scheme over `S` through its inclusion `V(I) ⟶ X ⟶ S`, and the inclusion is then an
`S`-morphism.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.instOverSubscheme`: the structure of scheme over `S`
  on `V(I)`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.over_eq_subschemeι_comp`: the structure morphism of
  `V(I)` is the inclusion followed by the structure morphism of `X`.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}} [X.Over S] (I : X.IdealSheafData)

/-- A closed subscheme of a scheme over `S` is a scheme over `S` through its inclusion. -/
instance instOverSubscheme : I.subscheme.Over S :=
  ⟨I.subschemeι ≫ X ↘ S⟩

/-- The structure morphism of a closed subscheme over `S` is its inclusion followed by the
structure morphism of the ambient scheme. -/
-- Not `@[simp]`: `CategoryTheory.comp_over` with `isOver_subschemeι` rewrites the right side
-- back to the left side.
theorem over_eq_subschemeι_comp : I.subscheme ↘ S = I.subschemeι ≫ X ↘ S :=
  (rfl)

/-- The inclusion of a closed subscheme is a morphism over `S`. -/
instance isOver_subschemeι : I.subschemeι.IsOver S :=
  ⟨rfl⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
