/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.BaseChange
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Scalar extension of an integral bilinear form

This file specializes `IsBaseChange.bilinForm` to integral lattices and their rational and
complex scalar extensions. The two extensions agree on purely rational vectors of the
complexification.

Two properties make the complex extension usable in Hodge theory. It is *real*: conjugating both
arguments conjugates the value, because lattice-induced conjugation fixes the integral vectors. And
it is nondegenerate as soon as the integral form is: nondegeneracy is preserved first by
localization from `ℤ` to `ℚ` and then by scalar extension from `ℚ` to `ℂ`.

## Main declarations

* `TauCeti.Hodge.bilinForm_latticeConj`: the complex extension commutes with lattice-induced
  conjugation.
* `TauCeti.Hodge.nondegenerate_bilinForm_complex`: the complex extension inherits
  nondegeneracy from the integral form.
* `TauCeti.Hodge.bilinForm_rationalToComplexLinearEquiv_one_tmul`: the complexified
  form computes the rationalified one on purely rational vectors.
-/

public section

namespace TauCeti.Hodge

open IsBaseChange

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- Complexifying the linear map from a bilinear form to the dual gives the linear map of the
complexified form. -/
theorem integralMapToComplex_bilinForm (hℂ : IsBaseChange ℂ ιℂ)
    (Q : LinearMap.BilinForm ℤ V) :
    integralMapToComplex hℂ (dualLatticeMap hℂ) Q = bilinForm hℂ Q := by
  apply hℂ.algHom_ext
  intro x
  apply hℂ.algHom_ext
  intro y
  simp

/-- Conjugating the second argument of a complexified integral form against an integral first
argument conjugates its value. -/
theorem bilinForm_apply_latticeConj (hℂ : IsBaseChange ℂ ιℂ)
    (Q : LinearMap.BilinForm ℤ V)
    (x : V) (y : Vℂ) :
    bilinForm hℂ Q (ιℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (bilinForm hℂ Q (ιℂ x) y) := by
  induction y using hℂ.inductionOn with
  | tmul w => simp
  | smul z y hy => simp [hy]
  | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]

/-- Conjugating both arguments of a complexified integral form conjugates its value: the form
takes real values on the lattice. -/
@[simp]
theorem bilinForm_latticeConj (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x y : Vℂ) :
    bilinForm hℂ Q (latticeConj hℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (bilinForm hℂ Q x y) := by
  induction x using hℂ.inductionOn generalizing y with
  | tmul v => simpa using bilinForm_apply_latticeConj hℂ Q v y
  | smul z x hx => simp [hx]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

/-- Complexification preserves nondegeneracy of an integral bilinear form. -/
theorem nondegenerate_bilinForm_complex (hℂ : IsBaseChange ℂ ιℂ)
    {Q : LinearMap.BilinForm ℤ V} (hQ : Q.Nondegenerate) :
    (bilinForm hℂ Q).Nondegenerate := by
  have hn : (Q.baseChange ℂ).Nondegenerate := by
    let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ V
    have heq : Q.baseChange ℂ =
        LinearMap.BilinForm.congr e ((Q.baseChange ℚ).baseChange ℂ) := by
      ext z v
      simp [e]
    rw [heq]
    exact LinearMap.BilinForm.Nondegenerate.congr e
      ((hQ.baseChange_of_isLocalization ℚ (nonZeroDivisors ℤ)).baseChange ℂ)
  rw [bilinForm_def]
  exact LinearMap.BilinForm.Nondegenerate.congr hℂ.equiv hn

/-! ### Comparing the rational and the complex extension -/

section Rational

variable {Vℚ : Type*} [AddCommGroup Vℚ] [Module ℚ Vℚ] {ιℚ : V →ₗ[ℤ] Vℚ}

/-- On an integral vector and a purely rational vector the complexified form takes the value of
the rationalified form. -/
private theorem bilinForm_rationalToComplexLinearEquiv_ι (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) (v : V) (y : Vℚ) :
    bilinForm hℂ Q (ιℂ v) (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y)) =
      ((bilinForm hℚ Q (ιℚ v) y : ℚ) : ℂ) := by
  induction y using hℚ.inductionOn with
  | tmul w => simp
  | smul q y hy =>
      simp [TensorProduct.tmul_smul, ← algebraMap_smul ℂ q, map_smul, hy]
  | add y₁ y₂ h₁ h₂ =>
      simp [TensorProduct.tmul_add, h₁, h₂]

/-- The two scalar extensions of an integral form agree: on purely rational vectors of the
complexification, the complexified form takes the values of the rationalified form. -/
theorem bilinForm_rationalToComplexLinearEquiv_one_tmul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) (x y : Vℚ) :
    bilinForm hℂ Q (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x))
        (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y)) =
      ((bilinForm hℚ Q x y : ℚ) : ℂ) := by
  induction x using hℚ.inductionOn generalizing y with
  | tmul v => simpa using bilinForm_rationalToComplexLinearEquiv_ι hℚ hℂ Q v y
  | smul q x hx =>
      simp [TensorProduct.tmul_smul, ← algebraMap_smul ℂ q, map_smul, hx]
  | add x₁ x₂ h₁ h₂ =>
      simp [TensorProduct.tmul_add, h₁, h₂]

end Rational


end TauCeti.Hodge
