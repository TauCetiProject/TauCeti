/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Basic
public import TauCeti.LinearAlgebra.CoordinateLattice

/-!
# Integral matrices acting on a rational coordinate space

An explicit Chevalley carrier starts from a representation of a Serre presentation by matrices
with integer entries, extends it to the rational Serre algebra, and shows that the integral
coordinate lattice of the rational module is preserved. This file collects the facts that step
needs, stated for an arbitrary index type so that every such carrier shares them.

Entrywise coercion of integer matrices is a homomorphism of Lie rings for the commutator
brackets, so it carries a Serre system over `ℤ` to one over the target ring. A coerced integer
matrix then sends integral coordinate vectors to integral coordinate vectors, which is what
keeps the lattice stable under the resulting action.

## Main declarations

* `TauCeti.matrixIntCastLieHom`: entrywise coercion of integer matrices, as a homomorphism of
  Lie rings.

## Main results

* `TauCeti.matrixIntCastLieHom_apply` and `TauCeti.matrixIntCastLieHom_mul`: the coercion acts
  entrywise and is multiplicative.
* `Matrix.intCastLieHom_mulVec_mem_coordinateLattice`: a coerced integer matrix preserves the
  integral coordinate lattice.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Entrywise coercion of integer matrices -/

/-- Entrywise coercion of integer matrices into a ring, as a homomorphism of Lie rings for the
commutator brackets. -/
noncomputable def matrixIntCastLieHom (R : Type*) [Ring R] :
    Matrix n n ℤ →ₗ⁅ℤ⁆ Matrix n n R :=
  ((Int.castRingHom R).mapMatrix.toIntAlgHom).toLieHom

/-- Entrywise coercion of integer matrices acts on entries by the integer cast. -/
@[simp]
theorem matrixIntCastLieHom_apply (R : Type*) [Ring R] (M : Matrix n n ℤ) (a b : n) :
    matrixIntCastLieHom R M a b = (M a b : R) := by
  simp only [matrixIntCastLieHom, AlgHom.toLieHom_apply, RingHom.toIntAlgHom_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]

/-- Entrywise coercion of integer matrices is multiplicative, being a ring homomorphism read as
a homomorphism of Lie rings. -/
@[simp]
theorem matrixIntCastLieHom_mul (R : Type*) [Ring R] (M N : Matrix n n ℤ) :
    matrixIntCastLieHom R (M * N) = matrixIntCastLieHom R M * matrixIntCastLieHom R N := by
  ext a b
  simp only [matrixIntCastLieHom_apply, Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

end TauCeti

namespace Matrix

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A coerced integer matrix preserves the integral coordinate lattice**, each coordinate of
the image being an integer combination of the coordinates of the argument. -/
theorem intCastLieHom_mulVec_mem_coordinateLattice (M : Matrix n n ℤ) {v : n → ℚ}
    (hv : v ∈ coordinateLattice n) :
    matrixIntCastLieHom ℚ M *ᵥ v ∈ coordinateLattice n := by
  rw [mem_coordinateLattice_iff] at hv ⊢
  choose z hz using hv
  intro a
  refine ⟨∑ b, M a b * z b, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, hz, Matrix.mulVec, dotProduct,
    matrixIntCastLieHom_apply]

end Matrix
