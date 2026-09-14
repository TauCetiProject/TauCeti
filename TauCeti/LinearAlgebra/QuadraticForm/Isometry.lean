/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Isometries of quadratic maps

This file records general properties of quadratic-map isometries.

## Main results

* `QuadraticMap.Isometry.polar_apply`: an isometry preserves polarization.
* `QuadraticMap.IsometryEquiv.nondegenerate_iff`: nondegeneracy is invariant under isometry.
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

/-- Nondegeneracy of a quadratic map is invariant under an isometric equivalence. -/
theorem _root_.QuadraticMap.IsometryEquiv.nondegenerate_iff
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w}
    [CommRing R] [Invertible (2 : R)] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup N] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.Nondegenerate ↔ Q₂.Nondegenerate := by
  constructor
  · intro hQ₁
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
    have hradical := e.map_radical
    rw [hQ₁.radical_eq_bot, Submodule.map_bot] at hradical
    exact hradical.symm
  · intro hQ₂
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
    have hradical := e.symm.map_radical
    rw [hQ₂.radical_eq_bot, Submodule.map_bot] at hradical
    exact hradical.symm

end TauCeti
