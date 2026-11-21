/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.Localization
import TauCeti.RingTheory.RingHom.Pure

/-!
# Examples of pure maps

These examples test the notions of pure linear maps and pure ring homomorphisms:

* split injections such as `ℤ → ℤ × ℤ` and `R → R[X]` are pure, and so is every faithfully flat
  ring map, such as `ℤ → ℤ[X]`;
* multiplication by `2` on `ℤ` is injective but not pure: after tensoring with `ℤ ⧸ 2` it becomes
  the zero map on a nonzero module;
* `ℤ → ℚ` is injective and flat but not pure: `(ℤ ⧸ 2) ⊗ ℚ = 0`.
-/

open TensorProduct Polynomial

/-! ### Pure maps -/

/-- The inclusion of the first factor `ℤ → ℤ × ℤ` is pure, being split by the first projection. -/
example : (LinearMap.inl ℤ ℤ ℤ).IsPure :=
  LinearMap.isPure_of_comp_eq_id (g := LinearMap.fst ℤ ℤ ℤ) (LinearMap.fst_comp_inl ℤ ℤ ℤ)

/-- The inclusion of the constants `R → R[X]` is pure, being split by the constant coefficient. -/
example (R : Type*) [CommRing R] : (algebraMap R R[X]).IsPure :=
  RingHom.isPure_algebraMap_iff.mpr <|
    LinearMap.isPure_of_comp_eq_id (g := lcoeff R 0) (by ext; simp)

/-- A faithfully flat ring map is pure; here the constants `R → R[X]` again, through faithful
flatness of a free module of positive rank. -/
example (R : Type*) [CommRing R] [Nontrivial R] : (algebraMap R R[X]).IsPure :=
  RingHom.FaithfullyFlat.isPure (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

/-- Base change of the pure map `R → R[X]` along `R → S` gives the pure map
`S → S ⊗[R] R[X]`. -/
example (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap S (S ⊗[R] R[X])).IsPure :=
  (RingHom.isPure_algebraMap_iff.mpr <|
    LinearMap.isPure_of_comp_eq_id (g := lcoeff R 0) (by ext; simp)).algebraMap_tensorProduct S

/-! ### Injective maps that are not pure -/

/-- Multiplication by `2` on `ℤ` is injective. -/
example : Function.Injective ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) := fun a b h ↦ by
  simpa using h

/-- Multiplication by `2` on `ℤ` is not pure: tensoring with `ℤ ⧸ 2` gives the zero map on the
nonzero module `(ℤ ⧸ 2) ⊗ ℤ`. A definition of purity as injectivity would accept this map. -/
example : ¬ ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ).IsPure := by
  intro h
  -- In `(ℤ ⧸ 2) ⊗[ℤ] ℤ ≃ ℤ ⧸ 2`, the element `1 ⊗ 1` is nonzero.
  have hne : ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) ≠ 0 := fun h0 ↦ by
    simpa using congrArg (TensorProduct.rid ℤ (ZMod 2)) h0
  apply hne
  apply h.lTensor_injective (ZMod 2)
  rw [map_zero, LinearMap.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, tmul_smul,
    smul_tmul']
  simp [show (2 : ZMod 2) = 0 from rfl]

/-- `ℤ → ℚ` is injective and flat. -/
example : Function.Injective (algebraMap ℤ ℚ) ∧ (algebraMap ℤ ℚ).Flat :=
  ⟨(algebraMap ℤ ℚ).injective_int,
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ (nonZeroDivisors ℤ))⟩

/-- `ℤ → ℚ` is not pure: the nonzero element `1` of `ℤ ⧸ 2` maps to `1 ⊗ 1 = 0` in
`ℚ ⊗[ℤ] (ℤ ⧸ 2)`. -/
example : ¬ (algebraMap ℤ ℚ).IsPure := by
  intro h
  have h1 : TensorProduct.mk ℤ ℚ (ZMod 2) 1 1 = 0 := by
    rw [TensorProduct.mk_apply, show (1 : ℚ) = (2 : ℤ) • (1 / 2 : ℚ) by norm_num, smul_tmul]
    simp [show (2 : ZMod 2) = 0 from rfl]
  exact one_ne_zero (h.injective_tensorProduct_mk (ZMod 2) (h1.trans (map_zero _).symm))
