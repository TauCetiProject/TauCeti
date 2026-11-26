/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Unitary
public import TauCeti.RepresentationTheory.LieHom

/-!
# The conjugation action of the real orthogonal group on complex matrices

A real orthogonal matrix `g ∈ O(n)` is a unitary complex matrix whose transpose is its inverse, so
`O(n)` acts on `𝔤𝔩ₙ(ℂ)` by conjugation, `Ad g M = g M g⁻¹ = g M gᵀ`, through Mathlib's
`Unitary.conjStarAlgAut`, by Lie algebra automorphisms.

## Main definitions

* `TauCeti.orthogonalAd n`: the conjugation action of `O(n)` on `𝔤𝔩ₙ(ℂ)`.
-/

public section

noncomputable section

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

variable (n) in
/-- The conjugation action `Ad g M = g M g⁻¹ = g M gᵀ` of `O(n)` on `𝔤𝔩ₙ(ℂ)`. -/
def orthogonalAd : Representation ℂ (orthogonalGroup n ℝ) (Matrix n n ℂ) where
  toFun g :=
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (orthogonalComplexMatrix g)).toAlgEquiv.toLinearMap
  map_one' := by ext1; simp
  map_mul' _ _ := by ext1; simp

/-- `Ad g M = g M gᵀ`. -/
@[simp]
theorem orthogonalAd_apply (g : orthogonalGroup n ℝ) (M : Matrix n n ℂ) :
    orthogonalAd n g M = (orthogonalComplexMatrix g : Matrix n n ℂ) * M *
      (orthogonalComplexMatrix g : Matrix n n ℂ)ᵀ := by
  have h : star (orthogonalComplexMatrix g : Matrix n n ℂ) =
      (orthogonalComplexMatrix g : Matrix n n ℂ)ᵀ := by
    ext i j
    simp
  simp [orthogonalAd, h]

/-- `O(n)` acts on `𝔤𝔩ₙ(ℂ)` by Lie algebra automorphisms. -/
instance instIsLieActionOrthogonalAd : (orthogonalAd n).IsLieAction :=
  .of_lieEquiv (fun g ↦
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (orthogonalComplexMatrix g)).toAlgEquiv.toLieEquiv)
    fun _ _ ↦ by simp [orthogonalAd]

end TauCeti
