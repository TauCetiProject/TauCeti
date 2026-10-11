/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic

/-!
# Dilating the carrier of an integral lattice

Multiplication by a nonzero integer sends the carrier of an integral lattice to another full
integral carrier in the same rational quadratic space. The rational bilinear form stays fixed;
this differs from scaling the form while keeping the carrier fixed. The carrier equivalence
below is used to compare their localizations.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Multiply the carrier of `L` by a nonzero integer, without changing its rational form. -/
noncomputable def carrierDilation (L : IntegralLattice V) (n : ℤ) (hn : n ≠ 0) :
    IntegralLattice V := by
  let e := LinearEquiv.smulOfNeZero ℚ V (n : ℚ) (Int.cast_ne_zero.mpr hn)
  let S := L.carrier.map (e.restrictScalars ℤ).toLinearMap
  letI : S.IsLattice ℚ := Submodule.IsLattice.map L.carrier e
  refine ofSubmodule S L.form L.isSymm ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  rintro _ ⟨y, hy, rfl⟩
  have hxy := L.form_mem_one ⟨x, hx⟩ ⟨y, hy⟩
  have he (z : V) : e z = (n : ℚ) • z := LinearEquiv.smulOfNeZero_apply ..
  simp only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_coe, he,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at *
  have h := (1 : Submodule ℤ ℚ).smul_mem (n * n) hxy
  convert h using 1; ring

/-- The carrier of the dilation is the image of the old carrier under multiplication by `n`. -/
@[simp]
theorem carrierDilation_carrier (L : IntegralLattice V) (n : ℤ) (hn : n ≠ 0) :
    (L.carrierDilation n hn).carrier =
      L.carrier.map ((LinearEquiv.smulOfNeZero ℚ V (n : ℚ)
        (Int.cast_ne_zero.mpr hn)).restrictScalars ℤ).toLinearMap := by
  simp [carrierDilation]

/-- Carrier dilation leaves the rational pairing unchanged. -/
@[simp]
theorem carrierDilation_form (L : IntegralLattice V) (n : ℤ) (hn : n ≠ 0) :
    (L.carrierDilation n hn).form = L.form := by
  simp [carrierDilation]

/-- Multiplication by `n` identifies the original carrier with the dilated carrier. -/
noncomputable def carrierDilationEquiv (L : IntegralLattice V) (n : ℤ) (hn : n ≠ 0) :
    L ≃ₗ[ℤ] L.carrierDilation n hn :=
  ((LinearEquiv.smulOfNeZero ℚ V (n : ℚ) (Int.cast_ne_zero.mpr hn)).restrictScalars ℤ).ofSubmodules
    L.carrier (L.carrierDilation n hn).carrier (L.carrierDilation_carrier n hn).symm

/-- The carrier equivalence acts by multiplication by `n` in the rational ambient space. -/
@[simp]
theorem coe_carrierDilationEquiv_apply (L : IntegralLattice V) (n : ℤ) (hn : n ≠ 0)
    (x : L) :
    ((L.carrierDilationEquiv n hn x : L.carrierDilation n hn) : V) = (n : ℚ) • (x : V) := by
  simp [carrierDilationEquiv]

/-- Dilating both vectors multiplies their integral pairing by the square of the dilation. -/
theorem integralForm_carrierDilationEquiv (L : IntegralLattice V) (n : ℤ) (hn : n ≠ 0)
    (x y : L) :
    (L.carrierDilation n hn).integralForm (L.carrierDilationEquiv n hn x)
        (L.carrierDilationEquiv n hn y) = n ^ 2 * L.integralForm x y := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  rw [Int.cast_mul, Int.cast_pow, (L.carrierDilation n hn).integralForm_cast,
    L.integralForm_cast, L.carrierDilation_form]
  simp only [coe_carrierDilationEquiv_apply, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  ring

end TauCeti.IntegralLattice
