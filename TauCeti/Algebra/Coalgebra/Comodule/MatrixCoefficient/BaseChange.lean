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
matrix. These are the coordinate calculations used to transport faithful representations and
projective orbit morphisms across scalar extensions.

## Main declarations

* `TauCeti.Comodule.matrixCoefficient_baseChange_tmul`: coefficients of scalar-extended
  functionals and vectors, without finiteness or freeness assumptions.

* `TauCeti.Comodule.coefficientMatrix_baseChange`: the coefficient matrix in the base-changed
  basis is obtained by sending `cᵢⱼ` to `1 ⊗ cᵢⱼ`.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.

This supplies the matrix-coefficient compatibility needed for base-change invariance of
geometric unipotence in Layer 5 of the ReductiveGroups roadmap.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

noncomputable section

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

end

end TauCeti.Comodule
