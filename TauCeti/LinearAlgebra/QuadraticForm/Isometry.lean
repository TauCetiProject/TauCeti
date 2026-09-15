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
* `QuadraticMap.IsometryEquiv.trans_apply`: composition of isometries acts by composition.
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

/-- The composition of two isometric equivalences acts by composing their underlying maps. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.trans_apply {R : Type u} {M₁ : Type v} {M₂ : Type*}
    {M₃ : Type*} {N : Type w} [CommSemiring R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] [AddCommGroup N]
    [Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    {Q₃ : QuadraticMap R M₃ N} (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) (x : M₁) :
    f.trans g x = g (f x) :=
  rfl

/-- Nondegeneracy of a quadratic map is invariant under an isometric equivalence. -/
theorem _root_.QuadraticMap.IsometryEquiv.nondegenerate_iff
    {R : Type u} {M₁ : Type v} {M₂ : Type*} {N : Type w}
    [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.Nondegenerate ↔ Q₂.Nondegenerate := by
  have hpolar : Q₁.polarBilin.ker.map e.toLinearMap = Q₂.polarBilin.ker := by
    ext y
    simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.ext_iff,
      LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply]
    constructor
    · intro hy z
      calc
        QuadraticMap.polar Q₂ y z =
            QuadraticMap.polar Q₂ (e (e.symm y)) (e (e.symm z)) := by simp
        _ = QuadraticMap.polar Q₁ (e.symm y) (e.symm z) := by
          simp only [QuadraticMap.polar, ← map_add e, QuadraticMap.IsometryEquiv.map_app]
        _ = 0 := hy (e.symm z)
    · intro hy x
      calc
        QuadraticMap.polar Q₁ (e.symm y) x =
            QuadraticMap.polar Q₂ (e (e.symm y)) (e x) := by
          simp only [QuadraticMap.polar, ← map_add e, QuadraticMap.IsometryEquiv.map_app]
        _ = 0 := by simpa using hy (e x)
  constructor
  · intro hQ₁
    have hradical := e.map_radical
    rw [hQ₁.radical_eq_bot, Submodule.map_bot] at hradical
    refine ⟨hradical.symm, ?_⟩
    rw [← hpolar]
    apply Cardinal.lift_le_one_iff.mp
    rw [e.toLinearEquiv.lift_rank_map_eq]
    exact Cardinal.lift_le_one_iff.mpr hQ₁.rank_rad_polar_le
  · intro hQ₂
    have hradical := e.symm.map_radical
    rw [hQ₂.radical_eq_bot, Submodule.map_bot] at hradical
    refine ⟨hradical.symm, ?_⟩
    apply Cardinal.lift_le_one_iff.mp
    rw [← e.toLinearEquiv.lift_rank_map_eq Q₁.polarBilin.ker, hpolar]
    exact Cardinal.lift_le_one_iff.mpr hQ₂.rank_rad_polar_le

end TauCeti
