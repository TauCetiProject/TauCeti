/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.RepresentationTheory.LieHom

/-!
# The conjugation action of the real orthogonal group on complex matrices

A real orthogonal matrix `g ∈ O(n)` is a complex matrix whose transpose is its inverse, so `O(n)`
acts on `𝔤𝔩ₙ(ℂ)` by conjugation, `Ad g M = g M g⁻¹ = g M gᵀ`, by Lie algebra automorphisms.

## Main definitions

* `TauCeti.orthogonalComplexMatrix g`: the complex matrix of `g ∈ O(n)`.
* `TauCeti.orthogonalAd n`: the conjugation action of `O(n)` on `𝔤𝔩ₙ(ℂ)`.
-/

public section

noncomputable section

open Complex Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complex matrix of an element of `O(n)`. -/
def orthogonalComplexMatrix (g : orthogonalGroup n ℝ) : Matrix n n ℂ :=
  ofRealHom.mapMatrix (g : Matrix n n ℝ)

/-- The entries of the complex matrix of `g ∈ O(n)`. -/
@[simp]
theorem orthogonalComplexMatrix_apply (g : orthogonalGroup n ℝ) (i j : n) :
    orthogonalComplexMatrix g i j = ((g : Matrix n n ℝ) i j : ℂ) :=
  (rfl)

/-- The complex matrix of a product is the product of the complex matrices. -/
theorem orthogonalComplexMatrix_mul (g h : orthogonalGroup n ℝ) :
    orthogonalComplexMatrix (g * h) = orthogonalComplexMatrix g * orthogonalComplexMatrix h := by
  simp only [orthogonalComplexMatrix, Submonoid.coe_mul, map_mul]

/-- The complex matrix of the identity is the identity. -/
@[simp]
theorem orthogonalComplexMatrix_one : orthogonalComplexMatrix (1 : orthogonalGroup n ℝ) = 1 := by
  simp only [orthogonalComplexMatrix, OneMemClass.coe_one, map_one]

/-- The transpose of the complex matrix of `g ∈ O(n)` is its inverse. -/
theorem transpose_orthogonalComplexMatrix_mul_self (g : orthogonalGroup n ℝ) :
    (orthogonalComplexMatrix g)ᵀ * orthogonalComplexMatrix g = 1 := by
  have h := (mem_orthogonalGroup_iff' n ℝ).1 g.property
  have ht : (orthogonalComplexMatrix g)ᵀ = ofRealHom.mapMatrix (g : Matrix n n ℝ)ᵀ := by
    rw [orthogonalComplexMatrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, transpose_map]
  rw [ht, orthogonalComplexMatrix, ← map_mul, h, map_one]

variable (n) in
/-- The conjugation action `Ad g M = g M g⁻¹ = g M gᵀ` of `O(n)` on `𝔤𝔩ₙ(ℂ)`. -/
def orthogonalAd : Representation ℂ (orthogonalGroup n ℝ) (Matrix n n ℂ) where
  toFun g := LinearMap.mulLeft ℂ (orthogonalComplexMatrix g) ∘ₗ
    LinearMap.mulRight ℂ (orthogonalComplexMatrix g)ᵀ
  map_one' := by ext; simp
  map_mul' g h := by
    ext M
    simp [orthogonalComplexMatrix_mul, transpose_mul, Matrix.mul_assoc]

/-- `Ad g M = g M gᵀ`. -/
@[simp]
theorem orthogonalAd_apply (g : orthogonalGroup n ℝ) (M : Matrix n n ℂ) :
    orthogonalAd n g M = orthogonalComplexMatrix g * M * (orthogonalComplexMatrix g)ᵀ := by
  simp [orthogonalAd, Matrix.mul_assoc]

/-- `O(n)` acts on `𝔤𝔩ₙ(ℂ)` by Lie algebra automorphisms. -/
instance instIsLieActionOrthogonalAd : (orthogonalAd n).IsLieAction where
  map_lie g M N := by
    simp only [orthogonalAd_apply, Ring.lie_def]
    have h := transpose_orthogonalComplexMatrix_mul_self g
    simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
    rw [← Matrix.mul_assoc (orthogonalComplexMatrix g)ᵀ, h, Matrix.one_mul,
      ← Matrix.mul_assoc (orthogonalComplexMatrix g)ᵀ, h, Matrix.one_mul]

end TauCeti
