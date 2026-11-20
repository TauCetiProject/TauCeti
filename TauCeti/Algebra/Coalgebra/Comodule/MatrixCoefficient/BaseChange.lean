/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Matrix coefficients under base change

Extending a comodule and its coefficient coalgebra along the same scalar morphism extends
its matrix coefficients. For a finite free comodule, this extends every entry of its coefficient
matrix and maps its characteristic polynomial along the right tensor-factor inclusion. These are
the coordinate calculations used to transport faithful representations, characteristic polynomials,
and projective orbit morphisms across scalar extensions.

## Main declarations

* `TauCeti.Comodule.matrixCoefficient_baseChange_tmul`: coefficients of scalar-extended
  functionals and vectors, without finiteness or freeness assumptions.

* `TauCeti.Comodule.coefficientMatrix_baseChange`: the coefficient matrix in the base-changed
  basis is obtained by sending `cᵢⱼ` to `1 ⊗ cᵢⱼ`.

* `TauCeti.Comodule.coefficientMatrix_baseChange_charpoly` and
  `TauCeti.Comodule.coefficientMatrix_baseChange_charpoly_eq_iff`: effect of scalar extension on
  the characteristic polynomial of the coefficient matrix, and reflection along flat base change.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

noncomputable section

section Semiring

variable {R : Type u} {A : Type v} {C : Type w} {M : Type x} {ι : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Scalar extension of a functional and a vector extends their matrix coefficient.
This holds for arbitrary comodules, without freeness or finiteness assumptions. -/
@[simp]
theorem matrixCoefficient_baseChange_tmul (a b : A) (φ : Module.Dual R M) (m : M) :
    letI := Comodule.baseChange (R := R) (H := C) (M := M) A
    matrixCoefficient (C := A ⊗[R] C)
        (Module.Dual.baseChangeEvaluation (a ⊗ₜ[R] φ)) (b ⊗ₜ[R] m) =
      (a * b) ⊗ₜ[R] matrixCoefficient (C := C) φ m := by
  let := Comodule.baseChange (R := R) (H := C) (M := M) A
  rw [matrixCoefficient_def, matrixCoefficient_def, baseChange_coact, baseChangeCoact_tmul]
  induction coact (R := R) (C := C) (M := M) m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul n c =>
      simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.map_tmul, Module.Dual.baseChangeEvaluation_tmul, LinearMap.id_apply,
        TensorProduct.lid_tmul, TensorProduct.tmul_smul]
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
        mul_one, Algebra.smul_def]
      congr 1
      ac_rfl

/-- Base change sends every entry of a comodule's coefficient matrix to the corresponding pure
tensor in the base-changed coefficient coalgebra. -/
@[simp]
theorem coefficientMatrix_baseChange (b : Basis ι R M) :
    letI := Comodule.baseChange (R := R) (H := C) (M := M) A
    coefficientMatrix (C := A ⊗[R] C) (b.baseChange A) =
      (coefficientMatrix (C := C) b).map
        ((TensorProduct.mk R A C) 1) := by
  let _ := Comodule.baseChange (R := R) (H := C) (M := M) A
  ext i j
  rw [coefficientMatrix_apply, Matrix.map_apply, coefficientMatrix_apply,
    matrixCoefficient_def, matrixCoefficient_def, Basis.baseChange_apply,
    baseChange_coact, baseChangeCoact_tmul]
  induction coact (R := R) (C := C) (M := M) (b j) using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, TensorProduct.tmul_add, hz, hw]
  | tmul m c => simp

end Semiring

section CommRing

variable {R : Type u} {A : Type v} {C : Type w} {M : Type x} {ι : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [CommRing C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [Fintype ι] [DecidableEq ι]

/-- Extending scalars of a finite free comodule maps the characteristic polynomial of its
coefficient matrix along `C → A ⊗[R] C`. -/
theorem coefficientMatrix_baseChange_charpoly (b : Basis ι R M) :
    letI := Comodule.baseChange (R := R) (H := C) (M := M) A
    (coefficientMatrix (C := A ⊗[R] C) (b.baseChange A)).charpoly =
      (coefficientMatrix (C := C) b).charpoly.map
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) := by
  let _ := Comodule.baseChange (R := R) (H := C) (M := M) A
  let f : C →+* A ⊗[R] C :=
    (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C)
  have hmatrix : coefficientMatrix (C := A ⊗[R] C) (b.baseChange A) =
      (coefficientMatrix (C := C) b).map f := by
    rw [coefficientMatrix_baseChange]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, TensorProduct.mk_apply]
    exact (Algebra.TensorProduct.includeRight_apply _).symm
  rw [hmatrix, Matrix.charpoly_map]

/-- When `C` is `R`-flat and `R → A` is injective, the base-changed coefficient matrix has
characteristic polynomial `(p.map (algebraMap R A)).map (algebraMap A (A ⊗[R] C))` if and only if
the original coefficient matrix has characteristic polynomial `p.map (algebraMap R C)`. -/
theorem coefficientMatrix_baseChange_charpoly_eq_iff [FaithfulSMul R A] [Module.Flat R C]
    (b : Basis ι R M) (p : Polynomial R) :
    letI := Comodule.baseChange (R := R) (H := C) (M := M) A
    (coefficientMatrix (C := A ⊗[R] C) (b.baseChange A)).charpoly =
        (p.map (algebraMap R A)).map (algebraMap A (A ⊗[R] C)) ↔
      (coefficientMatrix (C := C) b).charpoly = p.map (algebraMap R C) := by
  let _ := Comodule.baseChange (R := R) (H := C) (M := M) A
  let f : C →+* A ⊗[R] C :=
    (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C)
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective R A)
  rw [← (Polynomial.map_injective f hf).eq_iff, coefficientMatrix_baseChange_charpoly,
    Polynomial.map_map, Polynomial.map_map]
  have hcomp : f.comp (algebraMap R C) = (algebraMap A (A ⊗[R] C)).comp (algebraMap R A) := by
    ext r
    exact (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).commutes r
  rw [hcomp]

end CommRing

end

end TauCeti.Comodule
