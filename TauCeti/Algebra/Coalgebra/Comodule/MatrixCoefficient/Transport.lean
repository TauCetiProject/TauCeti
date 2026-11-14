/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Transport invariance of matrix coefficients

This file records how the matrix coefficients and coefficient matrices of a right comodule behave
under transport of a comodule structure across a linear equivalence. The general functoriality
lemmas for comodule morphisms live with the coefficient span and adjoin API in
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin`; this file keeps the
transport-specific consequences behind the `Comodule.Transport` import.

These lemmas are bookkeeping for the faithful-representation criterion and for passing between an
abstract finite free comodule and its coordinate presentation on `ι → R`.

## Main declarations

* `TauCeti.Comodule.matrixCoefficientSet_transport`: the set of coefficients is invariant
  under transported coactions.
* `TauCeti.Comodule.matrixCoefficientSubmodule_transport` and
  `TauCeti.Comodule.matrixCoefficientSubalgebra_transport`: coefficient objects are
  invariant under transported coactions.
* `TauCeti.Comodule.coefficientMatrix_map_transport` and
  `TauCeti.Comodule.coefficientMatrix_basisFun_transport_equivFun`: coefficient matrices are
  invariant under transporting along a linear equivalence and mapping the basis.

## References

This is standard matrix-coefficient functoriality for comodules; see Sweedler, *Hopf Algebras*,
Chapter 2.
-/

public section

open Module

namespace TauCeti

namespace Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]

section Transport

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N₀ : Type x} [AddCommMonoid N₀] [Module R N₀]

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient set. -/
@[simp]
theorem matrixCoefficientSet_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSet (R := R) (C := C) (M := N₀) =
      matrixCoefficientSet (R := R) (C := C) (M := M) := by
  let : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  exact (matrixCoefficientSet_eq_of_inverse_hom
    (R := R) (C := C) (M := M) (N := N₀)
    (transportToHom (R := R) (C := C) (M := M) (N := N₀) e)
    (transportInvHom (R := R) (C := C) (M := M) (N := N₀) e)
    (by intro n; simp) (by intro m; simp)).symm

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient submodule. -/
@[simp]
theorem matrixCoefficientSubmodule_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSubmodule (R := R) (C := C) (M := N₀) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  let : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  rw [matrixCoefficientSubmodule, matrixCoefficientSubmodule, matrixCoefficientSet_transport]

/-- Transporting a comodule structure along a linear equivalence `e` preserves the coefficient
matrix with respect to the mapped basis `b.map e`. -/
@[simp]
theorem coefficientMatrix_map_transport {ι : Type*} (e : M ≃ₗ[R] N₀) (b : Basis ι R M) :
    letI : Comodule R C N₀ := Transport e
    coefficientMatrix (C := C) (b.map e) = coefficientMatrix (C := C) b := by
  let _ : Comodule R C N₀ := Transport e
  ext i j
  have hbj : b.map e j = transportToHom (C := C) e (b j) := by simp
  have hci : (b.map e).coord i ∘ₗ (transportToHom (C := C) e).toLinearMap = b.coord i := by
    apply b.ext
    intro k
    simp [Basis.coord_apply]
  rw [coefficientMatrix_apply, hbj, matrixCoefficient_map, hci, ← coefficientMatrix_apply]

/-- Transporting a comodule along `b.equivFun` turns `b` into the standard basis `Pi.basisFun`
with the exact same coefficient matrix. -/
theorem coefficientMatrix_basisFun_transport_equivFun {ι : Type*} [Finite ι] (b : Basis ι R M) :
    letI : Comodule R C (ι → R) := Transport b.equivFun
    coefficientMatrix (C := C) (Pi.basisFun R ι) = coefficientMatrix (C := C) b := by
  classical
  cases nonempty_fintype ι
  let _ : Comodule R C (ι → R) := Transport b.equivFun
  have hmap : b.map b.equivFun = Pi.basisFun R ι := by
    ext j k
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [← hmap, coefficientMatrix_map_transport]

end Transport

section AlgebraTransport

variable [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N₀ : Type x} [AddCommMonoid N₀] [Module R N₀]

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient algebra. -/
@[simp]
theorem matrixCoefficientSubalgebra_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSubalgebra (R := R) (C := C) (M := N₀) =
      matrixCoefficientSubalgebra (R := R) (C := C) (M := M) := by
  let : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  rw [matrixCoefficientSubalgebra, matrixCoefficientSubalgebra, matrixCoefficientSet_transport]

end AlgebraTransport

end Comodule

end TauCeti
