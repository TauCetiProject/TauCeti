/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations applied entrywise to matrices

A derivation `D` of a commutative algebra `A` acts on matrices over `A` entrywise. This action
satisfies the Leibniz rule `D (M * N) = D M * N + M * D N` for matrix products, and it kills
matrices of scalars. For instance, differentiating `M * M⁻¹ = 1` computes the derivative of the
inverse of an invertible matrix as `D (M⁻¹) = -M⁻¹ * D M * M⁻¹`.

## Main results

* `Derivation.matrix_map_mul`: the Leibniz rule for matrix products.
* `Derivation.matrix_map_map_algebraMap`: a derivation kills every matrix of scalars.
-/

public section

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **The Leibniz rule for matrices**: a derivation applied entrywise to a product of matrices is
`D (M * N) = D M * N + M * D N`. -/
theorem matrix_map_mul {l m n : Type*} [Fintype m] (D : Derivation R A A) (M : Matrix l m A)
    (N : Matrix m n A) : (M * N).map D = M.map D * N + M * N.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, leibniz, smul_eq_mul,
    Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- A derivation kills every matrix of scalars. -/
theorem matrix_map_map_algebraMap {m n : Type*} (D : Derivation R A A) (C : Matrix m n R) :
    (C.map (algebraMap R A)).map D = 0 := by
  ext i j
  simp

end Derivation
