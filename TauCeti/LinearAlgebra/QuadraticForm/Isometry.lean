/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Isometries of quadratic maps

This file records general properties of quadratic-map isometries.

## Main results

* `QuadraticMap.Isometry.polar_apply`: an isometry preserves polarization.
* `QuadraticMap.IsometryEquiv.trans_apply`: a composite isometric equivalence applies the two
  equivalences in turn.
-/

public section

namespace TauCeti

open QuadraticMap

universe u v w

/-- An isometry preserves the polarization of a quadratic map. -/
@[simp]
theorem _root_.QuadraticMap.Isometry.polar_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {N : Type w} [CommSemiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup N] [Module R N] {Q₁ : QuadraticMap R M₁ N}
    {Q₂ : QuadraticMap R M₂ N} (f : Q₁ →qᵢ Q₂) (x y : M₁) :
    polar Q₂ (f x) (f y) = polar Q₁ x y := by
  simp only [QuadraticMap.polar, ← map_add f, QuadraticMap.Isometry.map_app]

/-- A composite isometric equivalence applies the two equivalences in turn. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.trans_apply {R : Type u} {M₁ : Type v} {M₂ M₃ : Type*}
    {N : Type w} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
    [Module R M₂] [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid N] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}
    (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) (x : M₁) : (f.trans g) x = g (f x) :=
  (rfl)

end TauCeti
