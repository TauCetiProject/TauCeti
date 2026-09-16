/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# The standard sesquilinear form with a specified automorphism

The form `sesquilinearForm σ` is linear in its first argument and `σ`-semilinear in its
second: `h(x,y) = ∑ i, x i * σ (y i)`. It identifies the second coordinate space
semilinearly with the dual of the first. When `σ` is involutive, the form has Hermitian
symmetry. This orientation is useful for Hermitian duals of codes over finite fields.

This identification with the dual gives a nondegenerate pairing for studying orthogonality
in finite coordinate spaces.

The API is in `TauCeti`: use `TauCeti.sesquilinearForm σ`, or `sesquilinearForm σ`
after `open TauCeti`.
-/

public section

namespace TauCeti

open Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The standard sesquilinear form, linear in the first argument and twisted by `σ`
in the second. It is Hermitian when `σ` is involutive. -/
noncomputable def sesquilinearForm (σ : R ≃+* R) :
    (ι → R) →ₗ[R] (ι → R) →ₛₗ[(σ : R →+* R)] R := by
  classical
  exact Matrix.toLinearMapₛₗ₂' R (RingHom.id R) (σ : R →+* R) 1

/-- The standard sesquilinear form evaluates as the coordinate sum `∑ i, x i * σ (y i)`. -/
@[simp]
theorem sesquilinearForm_apply (σ : R ≃+* R) (x y : ι → R) :
    sesquilinearForm σ x y = ∑ i, x i * σ (y i) := by
  classical
  unfold sesquilinearForm
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp [Matrix.one_apply, smul_eq_mul]

/-- Swapping the arguments and inverting the automorphism applies the inverse automorphism
to the value of the standard sesquilinear form. -/
theorem sesquilinearForm_symm_swap (σ : R ≃+* R) (x y : ι → R) :
    sesquilinearForm σ.symm y x = σ.symm (sesquilinearForm σ x y) := by
  simp [sesquilinearForm_apply, mul_comm]

/-- For an involutive automorphism, swapping the arguments conjugates the value. -/
theorem sesquilinearForm_swap (σ : R ≃+* R) (hσ : Function.Involutive σ) (x y : ι → R) :
    sesquilinearForm σ y x = σ (sesquilinearForm σ x y) := by
  simp only [sesquilinearForm_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hσ (y i), mul_comm]

/-- The standard sesquilinear form is nondegenerate over any commutative semiring. -/
theorem nondegenerate_sesquilinearForm (σ : R ≃+* R) :
    (sesquilinearForm σ (ι := ι)).Nondegenerate := by
  classical
  constructor
  · intro x hx
    ext i
    simpa [sesquilinearForm_apply, Pi.single_apply] using hx (Pi.single i 1)
  · intro y hy
    ext i
    have h : σ (y i) = 0 := by
      simpa [sesquilinearForm_apply, Pi.single_apply] using hy (Pi.single i 1)
    exact σ.injective (h.trans σ.map_zero.symm)

/-- The second argument of the standard sesquilinear form identifies the coordinate space
with its dual. -/
theorem sesquilinearForm_flip_bijective (σ : R ≃+* R) :
    Function.Bijective (sesquilinearForm σ (ι := ι)).flip := by
  classical
  constructor
  · intro x y h
    ext i
    apply σ.injective
    have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [sesquilinearForm_apply, Pi.single_apply] using this
  · intro f
    obtain ⟨y, rfl⟩ := (dotProductEquiv R ι).surjective f
    refine ⟨fun i ↦ σ.symm (y i), ?_⟩
    ext x
    simp [sesquilinearForm_apply, dotProduct, mul_comm]

end TauCeti
