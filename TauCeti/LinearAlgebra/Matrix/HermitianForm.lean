/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# The standard Hermitian form with a specified automorphism

The form `hermitianForm σ` is linear in its first argument and `σ`-semilinear in its
second: `h(x,y) = ∑ i, x i * σ (y i)`. It identifies the second coordinate space
semilinearly with the dual of the first. When `σ` is involutive, the form has Hermitian
symmetry. This orientation is useful for Hermitian duals of codes over finite fields.

This identification with the dual gives a nondegenerate pairing for studying orthogonality
in finite coordinate spaces.
-/

public section

namespace TauCeti

open Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The standard sesquilinear form, linear in the first argument and twisted by `σ`
in the second. It is Hermitian when `σ` is involutive. -/
noncomputable def hermitianForm (σ : R ≃+* R) :
    (ι → R) →ₗ[R] (ι → R) →ₛₗ[(σ : R →+* R)] R := by
  classical
  exact Matrix.toLinearMapₛₗ₂' R (RingHom.id R) (σ : R →+* R) 1

/-- The standard Hermitian form evaluates as the coordinate sum `∑ i, x i * σ (y i)`. -/
@[simp]
theorem hermitianForm_apply (σ : R ≃+* R) (x y : ι → R) :
    hermitianForm σ x y = ∑ i, x i * σ (y i) := by
  classical
  unfold hermitianForm
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp [Matrix.one_apply, smul_eq_mul]

/-- Swapping the arguments conjugates the value of the standard Hermitian form. -/
theorem hermitianForm_swap (σ : R ≃+* R) (hσ : Function.Involutive σ) (x y : ι → R) :
    hermitianForm σ y x = σ (hermitianForm σ x y) := by
  simp only [hermitianForm_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hσ (y i), mul_comm]

/-- The standard Hermitian form is nondegenerate over any commutative semiring. -/
theorem hermitianForm_nondegenerate (σ : R ≃+* R) :
    (hermitianForm σ (ι := ι)).Nondegenerate := by
  classical
  constructor
  · intro x hx
    ext i
    simpa [hermitianForm_apply, Pi.single_apply] using hx (Pi.single i 1)
  · intro y hy
    ext i
    have h : σ (y i) = 0 := by simpa [hermitianForm_apply, Pi.single_apply] using hy (Pi.single i 1)
    exact σ.injective (h.trans σ.map_zero.symm)

/-- The second argument of the standard Hermitian form identifies the coordinate space
with its dual. -/
theorem hermitianForm_flip_bijective (σ : R ≃+* R) :
    Function.Bijective (hermitianForm σ (ι := ι)).flip := by
  classical
  constructor
  · intro x y h
    ext i
    apply σ.injective
    have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [hermitianForm_apply, Pi.single_apply] using this
  · intro f
    obtain ⟨y, rfl⟩ := (dotProductEquiv R ι).surjective f
    refine ⟨fun i ↦ σ.symm (y i), ?_⟩
    ext x
    simp [hermitianForm_apply, dotProduct, mul_comm]

end TauCeti
