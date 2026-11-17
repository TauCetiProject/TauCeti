/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Transport invariance of matrix coefficients

This file records how the matrix coefficients of a right comodule behave under transport of
a comodule structure across a linear equivalence. The general functoriality lemmas for
comodule morphisms live with the coefficient span and adjoin API in
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin`; this file keeps the
transport-specific consequences behind the `Comodule.Transport` import.

These lemmas are bookkeeping for the faithful-representation criterion: faithfulness is detected by
whether the matrix coefficients, together with their antipode images, generate the coordinate Hopf
algebra. Transporting a finite free comodule along a basis equivalence `b.equivFun` recovers the
reconstructed matrix comodule of its coefficient matrix.

## Main declarations

* `TauCeti.Comodule.matrixCoefficientSet_transport`: the set of coefficients is invariant
  under transported coactions.
* `TauCeti.Comodule.matrixCoefficientSubmodule_transport` and
  `TauCeti.Comodule.matrixCoefficientSubalgebra_transport`: coefficient objects are
  invariant under transported coactions.
* `Module.Basis.transport_equivFun_eq_matrixComodule`: transporting a comodule along `b.equivFun`
  produces the matrix comodule of its coefficient matrix.

## References

This is standard matrix-coefficient functoriality for comodules; see Sweedler, *Hopf Algebras*,
Chapter 2.
-/

public section

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

namespace Module.Basis

open TauCeti TauCeti.Comodule

/-- Transporting a comodule along `b.equivFun` produces the matrix comodule of its coefficient
matrix. -/
theorem transport_equivFun_eq_matrixComodule {R S M ι : Type*} [CommSemiring R]
    [Semiring S] [Bialgebra R S] [AddCommMonoid M] [Module R M] [Comodule R S M]
    [Fintype ι] (b : Basis ι R M) :
    Transport (R := R) (C := S) b.equivFun =
      matrixComodule R (coefficientMatrix (C := S) b)
        (b.coefficientMatrix_map_comul (C := S))
        (b.coefficientMatrix_counit_basisFun (C := S)) := by
  rw [transport_eq_iff]
  apply b.ext
  intro j
  have hb_apply (k : ι) : b.equivFun (b k) = Pi.basisFun R ι k := by
    classical
    ext i
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  simp only [LinearMap.coe_comp, Function.comp_apply, coact_basis_eq_sum_coefficientMatrix b,
    map_sum, TensorProduct.map_tmul, LinearEquiv.coe_coe, LinearMap.id_apply,
    matrixComodule_coact, hb_apply, matrixCoact_apply_basisFun]

end Module.Basis
