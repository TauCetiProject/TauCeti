/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.Algebra.Homology.DG.Algebra.Defs

/-!
# The graded Leibniz rule for matrices over a differential graded algebra

A differential `d` acts on matrices over an algebra `A` entrywise, through `Matrix.map`. For a
matrix `F` whose entry `F x y` is homogeneous of degree `g y - f x`, the graded Leibniz rule of a
differential graded algebra gives `d (F G) = (d F) G + τ(F) (d G)`, where the **sign twist**
`τ(F) x y = (-1) ^ (g y - f x) • F x y` is the grading involution `a ↦ (-1) ^ |a| a` applied
entrywise. The sign twist is multiplicative and fixes the identity matrix.

This is the graded counterpart of `TauCeti.IsUngradedDGAlgebra.map_mul_matrix`. Matrices with
entries of degree `g y - f x` are the matrices of twisting and continuation cocycles of
`TauCeti.Algebra.Homology.DG.Twisted.Continuation`.

## Main definitions

* `Matrix.signTwist F f g`: the sign twist `(-1) ^ (g y - f x) • F x y`.

## Main results

* `Matrix.signTwist_mul`, `Matrix.signTwist_one`: the sign twist is multiplicative and fixes the
  identity matrix.
* `TauCeti.IsDGAlgebra.map_mul_matrix_of_mem`: `d (F G) = (d F) G + τ(F) (d G)`.
* `TauCeti.IsDGAlgebra.map_one_matrix_eq_zero`: the differential of the identity matrix vanishes.
-/

public section

namespace Matrix

variable {A : Type*} [Ring A] {P Q S : Type*}

/-- The sign twist `(-1) ^ (g y - f x) • F x y` of a matrix whose entry `F x y` has degree
`g y - f x`: entrywise, it is the grading involution `a ↦ (-1) ^ |a| a`. -/
def signTwist (F : Matrix P Q A) (f : P → ℤ) (g : Q → ℤ) : Matrix P Q A :=
  of fun x y ↦ (g y - f x).negOnePow • F x y

@[simp]
theorem signTwist_apply (F : Matrix P Q A) (f : P → ℤ) (g : Q → ℤ) (x : P) (y : Q) :
    F.signTwist f g x y = (g y - f x).negOnePow • F x y :=
  (rfl)

/-- The sign twist is multiplicative. -/
theorem signTwist_mul [Fintype Q] (F : Matrix P Q A) (G : Matrix Q S A) (f : P → ℤ) (g : Q → ℤ)
    (k : S → ℤ) : (F * G).signTwist f k = F.signTwist f g * G.signTwist g k := by
  ext x z
  simp only [signTwist_apply, Matrix.mul_apply, Finset.smul_sum, smul_mul_smul_comm,
    ← Int.negOnePow_add]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [show g y - f x + (k z - g y) = k z - f x by ring]

/-- The sign twist fixes the identity matrix. -/
@[simp]
theorem signTwist_one [DecidableEq P] (f : P → ℤ) : (1 : Matrix P P A).signTwist f f = 1 := by
  ext x y
  rw [signTwist_apply, Matrix.one_apply]
  split_ifs with hxy
  · rw [hxy, sub_self, Int.negOnePow_zero, one_smul]
  · exact smul_zero _

end Matrix

namespace TauCeti

namespace IsDGAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
  [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {P Q S : Type*}

/-- **The graded Leibniz rule for matrices**: for a matrix `F` whose entry `F x y` has degree
`g y - f x`, `d (F G) = (d F) G + τ(F) (d G)`, where `τ` is the sign twist. -/
theorem map_mul_matrix_of_mem (h : IsDGAlgebra 𝒜 d) [Fintype Q] {f : P → ℤ} {g : Q → ℤ}
    {F : Matrix P Q A} (hF : ∀ x y, F x y ∈ 𝒜 (g y - f x)) (G : Matrix Q S A) :
    (F * G).map d = F.map d * G + F.signTwist f g * G.map d := by
  ext x z
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_sum, h.leibniz (hF x _),
    Finset.sum_add_distrib, Matrix.signTwist_apply, smul_mul_assoc]

/-- The differential of the identity matrix vanishes. -/
theorem map_one_matrix_eq_zero (h : IsDGAlgebra 𝒜 d) [DecidableEq P] :
    (1 : Matrix P P A).map d = 0 := by
  ext x y
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.zero_apply]
  split_ifs
  · exact h.map_one_eq_zero
  · exact map_zero d

end IsDGAlgebra

end TauCeti
