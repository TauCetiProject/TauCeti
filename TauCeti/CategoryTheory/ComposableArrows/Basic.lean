/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Equality of composable arrows of length one

Two composable arrows `mk₁ f` and `mk₁ f'` of length one are equal exactly when `f` and `f'`
are equal as arrows (`CategoryTheory.ComposableArrows.mk₁_eq_mk₁_iff`). Combined with
`CategoryTheory.Arrow.mk_eq_mk_iff`, this identifies the sources and targets of `f` and `f'`
and relates the two morphisms by `eqToHom`s; for instance, it compares edges of a nerve.
-/

public section

namespace CategoryTheory.ComposableArrows

variable {C : Type*} [Category* C]

/-- The composable arrows `mk₁ f` and `mk₁ f'` are equal exactly when `f` and `f'` are equal
as arrows. -/
lemma mk₁_eq_mk₁_iff {X₀ X₁ Y₀ Y₁ : C} {f : X₀ ⟶ X₁} {f' : Y₀ ⟶ Y₁} :
    mk₁ f = mk₁ f' ↔ Arrow.mk f = Arrow.mk f' :=
  arrowEquiv.apply_eq_iff_eq.symm

end CategoryTheory.ComposableArrows
