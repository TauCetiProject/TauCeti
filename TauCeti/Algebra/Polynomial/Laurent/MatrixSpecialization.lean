/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Polynomial.Laurent.Specialization

/-!
# Matrices under Laurent specialization

A basis of a module over a Laurent polynomial ring specializes coefficientwise to a basis over
the coefficient ring. In those bases, specializing a Laurent-linear map simply evaluates every
entry of its matrix. This is the matrix form of base change along evaluation at a unit.

## Main result

* `TauCeti.LaurentSpecialization.toMatrix_map`: specialization evaluates a matrix entrywise.
-/

public section

noncomputable section

namespace TauCeti.LaurentSpecialization

open LaurentPolynomial

variable {R : Type*} [CommRing R] (ε : Rˣ)
variable {N : Type*} [AddCommGroup N] [Module R[T;T⁻¹] N] [Module R N]
  [IsScalarTower R R[T;T⁻¹] N]
variable {M : Type*} [AddCommGroup M] [Module R[T;T⁻¹] M] [Module R M]
  [IsScalarTower R R[T;T⁻¹] M]

/-- **Specializing a Laurent-linear map evaluates its matrix.** The source and target bases are
specialized coefficientwise, so every matrix entry is evaluated at the specialization point. -/
@[simp]
theorem toMatrix_map {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Finite κ]
    (bN : Module.Basis ι R[T;T⁻¹] N) (bM : Module.Basis κ R[T;T⁻¹] M)
    (f : N →ₗ[R[T;T⁻¹]] M) :
    LinearMap.toMatrix (basis ε bN) (basis ε bM) (map ε f) =
      (LinearMap.toMatrix bN bM f).map (laurentEval ε) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, basis_apply,
    map_mk, basis_repr_mk_apply]

end TauCeti.LaurentSpecialization
