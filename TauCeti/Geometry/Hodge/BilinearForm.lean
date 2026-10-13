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

An integral bilinear form on a lattice extends uniquely to a bilinear form on any abstract base
change of that lattice. This file constructs that extension,
`TauCeti.Hodge.integralFormBaseChange`, from Mathlib's base change of a bilinear form along the
canonical tensor model, and characterizes it by its values on integral vectors. The rational and
the complex extension are the two cases the Hodge theory uses, and they agree on the purely
rational vectors of the complexification.

Two properties make the complex extension usable in Hodge theory. It is *real*: conjugating both
arguments conjugates the value, because lattice-induced conjugation fixes the integral vectors. And
it is nondegenerate as soon as the integral form is: nondegeneracy is preserved first by
localization from `ℤ` to `ℚ` and then by scalar extension from `ℚ` to `ℂ`.

## Main declarations

* `TauCeti.Hodge.integralFormBaseChange`: the bilinear form extending an integral one along an
  abstract base change of its lattice.
* `TauCeti.Hodge.integralFormBaseChange_ι`: its values on integral vectors.
* `TauCeti.Hodge.integralFormBaseChange_unique`: it is the only such extension.
* `TauCeti.Hodge.integralFormBaseChange_apply_symm`: a symmetry `Q y x = k * Q x y` between an
  integral form and its flip passes to the extension.
* `TauCeti.Hodge.integralFormBaseChange_conj`: the complex extension commutes with lattice-induced
  conjugation.
* `TauCeti.Hodge.integralFormBaseChange_nondegenerate`: the complex extension inherits
  nondegeneracy from the integral form.
* `TauCeti.Hodge.integralFormBaseChange_prod`: scalar extension of a block-diagonal form is
  block diagonal.
* `TauCeti.Hodge.integralFormBaseChange_tmul`: complexification of the tensor product of two
  integral forms is the tensor product of their complexifications.
* `TauCeti.Hodge.integralFormBaseChange_rationalToComplexLinearEquiv_one_tmul`: the complexified
  form computes the rationalified one on purely rational vectors.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

section BaseChange

variable {A : Type*} {V_A : Type*} [CommRing A] [AddCommGroup V_A] [Module A V_A]
variable {ι : V →ₗ[ℤ] V_A}

/-- The scalar extension of an integral bilinear form along an abstract base change of its
lattice, transported from Mathlib's base change along the canonical tensor model. -/
noncomputable def integralFormBaseChange (h : IsBaseChange A ι)
    (Q : LinearMap.BilinForm ℤ V) : LinearMap.BilinForm A V_A :=
  (Q.baseChange A).compl₁₂ h.equiv.symm.toLinearMap h.equiv.symm.toLinearMap

/-- On integral vectors the extended form is the integral form. -/
@[simp]
theorem integralFormBaseChange_ι (h : IsBaseChange A ι) (Q : LinearMap.BilinForm ℤ V)
    (x y : V) : integralFormBaseChange h Q (ι x) (ι y) = (Q x y : A) := by
  simp [integralFormBaseChange, h.equiv_symm_apply]

/-- Complexifying the linear map from a bilinear form to the dual gives the linear map of the
complexified form. -/
theorem integralMapToComplex_bilinForm (hℂ : IsBaseChange ℂ ιℂ)
    (Q : LinearMap.BilinForm ℤ V) :
    integralMapToComplex hℂ (dualLatticeMap hℂ) Q = integralFormBaseChange hℂ Q := by
  apply hℂ.algHom_ext
  intro x
  apply hℂ.algHom_ext
  intro y
  simp

/-- The extended form is the unique bilinear form restricting to the integral one. -/
theorem integralFormBaseChange_unique (h : IsBaseChange A ι) (Q : LinearMap.BilinForm ℤ V)
    (B : LinearMap.BilinForm A V_A) (hB : ∀ x y : V, B (ι x) (ι y) = (Q x y : A)) :
    B = integralFormBaseChange h Q := by
  refine h.algHom_ext _ _ fun x ↦ h.algHom_ext _ _ fun y ↦ ?_
  simp [hB x y]

/-- Complexifying a form pulled back along integral linear maps gives the complexified form
pulled back along their complexifications. -/
theorem integralFormBaseChange_comp {V' V'ℂ : Type*} [AddCommGroup V'] [AddCommGroup V'ℂ]
    [Module ℂ V'ℂ] {ι'ℂ : V' →ₗ[ℤ] V'ℂ} (h'ℂ : IsBaseChange ℂ ι'ℂ) (hℂ : IsBaseChange ℂ ιℂ)
    (Q : LinearMap.BilinForm ℤ V) (l r : V' →ₗ[ℤ] V) :
    integralFormBaseChange h'ℂ (Q.comp l r) =
      (integralFormBaseChange hℂ Q).comp (integralMapToComplex h'ℂ ιℂ l)
        (integralMapToComplex h'ℂ ιℂ r) :=
  (integralFormBaseChange_unique h'ℂ _ _ fun x y ↦ by simp).symm

/-- Scalar extension turns the flip of an integral form into the flip of the extended form. -/
@[simp]
theorem integralFormBaseChange_flip (h : IsBaseChange A ι) (Q : LinearMap.BilinForm ℤ V) :
    (integralFormBaseChange h Q).flip = integralFormBaseChange h Q.flip :=
  integralFormBaseChange_unique h _ _ fun x y ↦ by simp

/-- Scalar extension commutes with integer multiples of an integral form. -/
@[simp]
theorem integralFormBaseChange_zsmul (h : IsBaseChange A ι) (k : ℤ)
    (Q : LinearMap.BilinForm ℤ V) :
    integralFormBaseChange h (k • Q) = k • integralFormBaseChange h Q :=
  (integralFormBaseChange_unique h _ _ fun x y ↦ by simp).symm

/-- **A weight symmetry passes to the scalar extension.**  If an integral form satisfies
`Q y x = k * Q x y` for an integer `k` -- the symmetry a polarizing form has, with
`k = (-1)^n` -- then so does its scalar extension. -/
theorem integralFormBaseChange_apply_symm (h : IsBaseChange A ι) (Q : LinearMap.BilinForm ℤ V)
    {k : ℤ} (hQ : ∀ x y, Q y x = k * Q x y) (x y : V_A) :
    integralFormBaseChange h Q y x = (k : A) * integralFormBaseChange h Q x y := by
  have hflip : Q.flip = k • Q := by
    ext u w
    simpa using hQ u w
  have hforms : (integralFormBaseChange h Q).flip = k • integralFormBaseChange h Q := by
    rw [integralFormBaseChange_flip, hflip, integralFormBaseChange_zsmul]
  simpa only [LinearMap.BilinForm.flip_apply, LinearMap.smul_apply, zsmul_eq_mul] using
    DFunLike.congr_fun (DFunLike.congr_fun hforms x) y

end BaseChange

/-- Conjugating the second argument of a complexified integral form against an integral first
argument conjugates its value. -/
theorem integralFormBaseChange_conj_right (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x : V) (y : Vℂ) :
    integralFormBaseChange hℂ Q (ιℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (integralFormBaseChange hℂ Q (ιℂ x) y) := by
  induction y using hℂ.inductionOn with
  | tmul w => simp
  | smul z y hy => simp [hy]
  | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]

/-- Conjugating both arguments of a complexified integral form conjugates its value: the form
takes real values on the lattice. -/
@[simp]
theorem integralFormBaseChange_conj (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x y : Vℂ) :
    integralFormBaseChange hℂ Q (latticeConj hℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (integralFormBaseChange hℂ Q x y) := by
  induction x using hℂ.inductionOn generalizing y with
  | tmul v => simpa using integralFormBaseChange_conj_right hℂ Q v y
  | smul z x hx => simp [hx]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

/-- Complexification preserves nondegeneracy of an integral bilinear form. -/
theorem integralFormBaseChange_nondegenerate (hℂ : IsBaseChange ℂ ιℂ)
    {Q : LinearMap.BilinForm ℤ V} (hQ : Q.Nondegenerate) :
    (integralFormBaseChange hℂ Q).Nondegenerate := by
  have hn : (Q.baseChange ℂ).Nondegenerate := by
    let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ V
    have heq : Q.baseChange ℂ =
        LinearMap.BilinForm.congr e ((Q.baseChange ℚ).baseChange ℂ) := by
      ext z v
      simp [e]
    rw [heq]
    exact LinearMap.BilinForm.Nondegenerate.congr e
      ((hQ.baseChange_of_isLocalization ℚ (nonZeroDivisors ℤ)).baseChange ℂ)
  have hform : integralFormBaseChange hℂ Q =
      LinearMap.BilinForm.congr hℂ.equiv (Q.baseChange ℂ) := by
    ext x y
    simp only [integralFormBaseChange, LinearMap.compl₁₂_apply,
      LinearMap.BilinForm.congr_apply, LinearEquiv.coe_coe]
  rw [hform]
  exact LinearMap.BilinForm.Nondegenerate.congr hℂ.equiv hn

/-! ### Comparing the rational and the complex extension -/

section Rational

variable {Vℚ : Type*} [AddCommGroup Vℚ] [Module ℚ Vℚ] {ιℚ : V →ₗ[ℤ] Vℚ}

/-- On an integral vector and a purely rational vector the complexified form takes the value of
the rationalified form. -/
private theorem integralFormBaseChange_rationalToComplexLinearEquiv_ι (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) (v : V) (y : Vℚ) :
    integralFormBaseChange hℂ Q (ιℂ v) (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y)) =
      ((integralFormBaseChange hℚ Q (ιℚ v) y : ℚ) : ℂ) := by
  induction y using hℚ.inductionOn with
  | tmul w => simp
  | smul q y hy =>
      simp [TensorProduct.tmul_smul, ← algebraMap_smul ℂ q, map_smul, hy]
  | add y₁ y₂ h₁ h₂ =>
      simp [TensorProduct.tmul_add, h₁, h₂]

/-- The two scalar extensions of an integral form agree: on purely rational vectors of the
complexification, the complexified form takes the values of the rationalified form. -/
theorem integralFormBaseChange_rationalToComplexLinearEquiv_one_tmul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) (x y : Vℚ) :
    integralFormBaseChange hℂ Q (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x))
        (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y)) =
      ((integralFormBaseChange hℚ Q x y : ℚ) : ℂ) := by
  induction x using hℚ.inductionOn generalizing y with
  | tmul v => simpa using integralFormBaseChange_rationalToComplexLinearEquiv_ι hℚ hℂ Q v y
  | smul q x hx =>
      simp [TensorProduct.tmul_smul, ← algebraMap_smul ℂ q, map_smul, hx]
  | add x₁ x₂ h₁ h₂ =>
      simp [TensorProduct.tmul_add, h₁, h₂]

end Rational

/-! ### Products -/

section Prod

variable {A : Type*} {V' : Type*} {V_A : Type*} {V'_A : Type*}
variable [CommRing A] [AddCommGroup V'] [AddCommGroup V_A] [Module A V_A]
variable [AddCommGroup V'_A] [Module A V'_A]
variable {ι : V →ₗ[ℤ] V_A} {ι' : V' →ₗ[ℤ] V'_A}

/-- The scalar extension of a block-diagonal integral form is the block-diagonal form of the
scalar extensions of its two blocks. -/
@[simp]
theorem integralFormBaseChange_prod (h : IsBaseChange A ι) (h' : IsBaseChange A ι')
    (Q : LinearMap.BilinForm ℤ V) (Q' : LinearMap.BilinForm ℤ V') :
    integralFormBaseChange (IsBaseChange.prodMap ι ι' h h') (Q.prod Q') =
      (integralFormBaseChange h Q).prod (integralFormBaseChange h' Q') :=
  (integralFormBaseChange_unique _ _ _ fun x y ↦ by
    simp [LinearMap.prodMap_apply]).symm

end Prod

/-! ### Tensor products -/

section TensorProduct

variable {V' : Type*} {V'ℂ : Type*} [AddCommGroup V'] [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℂ : V' →ₗ[ℤ] V'ℂ}

/-- The complexification of the tensor product of two integral forms, along the tensor product of
two complexifications, is the tensor product of the two complexified forms. -/
@[simp]
theorem integralFormBaseChange_tmul (hℂ : IsBaseChange ℂ ιℂ) (h'ℂ : IsBaseChange ℂ ι'ℂ)
    (Q : LinearMap.BilinForm ℤ V) (Q' : LinearMap.BilinForm ℤ V') :
    integralFormBaseChange (isBaseChange_tensorLatticeMap hℂ h'ℂ) (Q.tmul Q') =
      (integralFormBaseChange hℂ Q).tmul (integralFormBaseChange h'ℂ Q') := by
  refine (integralFormBaseChange_unique _ _ _ fun x y ↦ ?_).symm
  induction x with
  | tmul v w =>
    induction y with
    | tmul v' w' =>
      rw [tensorLatticeMap_tmul, tensorLatticeMap_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        integralFormBaseChange_ι, integralFormBaseChange_ι, smul_eq_mul, ← Int.cast_mul]
      -- The integral form is applied through the canonical `ℤ`-module structure of `V ⊗[ℤ] V'`,
      -- which is only defeq, not reducibly, to the one `tensorDistrib_tmul` is stated for.
      exact congrArg _ (LinearMap.BilinForm.tensorDistrib_tmul ℤ ℤ Q Q' v w v' w').symm
    | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy', Int.cast_add]
  | add x x' hx hx' =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hx', ← Int.cast_add]
    exact congrArg _ (LinearMap.map_add₂ (Q.tmul Q') x x' y).symm

end TensorProduct

end TauCeti.Hodge
