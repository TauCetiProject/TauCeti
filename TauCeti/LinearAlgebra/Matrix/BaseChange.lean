/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# Scalar extension of matrix cokernels

Mapping the entries of a finite matrix along an algebra map presents the scalar extension
of its cokernel. No flatness is required: this is right exactness of tensor product, expressed
in the standard bases. The equivalence keeps track of the quotient generators, so it can be
used to descend module presentations to smaller coefficient rings.

The construction uses Mathlib's finite-product tensor equivalence and the cokernel
base-change equivalence in `TauCeti.LinearAlgebra.TensorProduct.Quotient`.
-/

public section

open TensorProduct

namespace Matrix

section Semiring

variable {R S m n : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The standard-basis identifications intertwine scalar extension of a matrix map with
mapping its entries along the algebra map. -/
theorem piScalarRight_comp_baseChange_mulVecLin (A : Matrix m n R) :
    (piScalarRight R S S m).toLinearMap.comp (A.mulVecLin.baseChange S) =
      (A.map (algebraMap R S)).mulVecLin.comp (piScalarRight R S S n).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro b x
  ext i
  simp [piScalarRight_apply, piScalarRightHom_tmul, mulVec, dotProduct,
    Algebra.smul_def, Finset.sum_mul, mul_assoc]

end Semiring

variable {R S m n : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Scalar extension of a finite matrix cokernel is the cokernel of the matrix obtained by
mapping its entries. This holds for arbitrary commutative coefficient algebras. -/
noncomputable def cokernelBaseChangeEquiv (A : Matrix m n R) :
    S ⊗[R] ((m → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[S]
      (m → S) ⧸ LinearMap.range (A.map (algebraMap R S)).mulVecLin :=
  A.mulVecLin.cokernelBaseChangeEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (piScalarRight R S S m) (by
      rw [← LinearMap.range_comp, piScalarRight_comp_baseChange_mulVecLin,
        LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])

/-- On quotient representatives the cokernel comparison maps each coordinate along the
algebra map and multiplies by the tensor's scalar. -/
@[simp]
theorem cokernelBaseChangeEquiv_tmul (A : Matrix m n R) (s : S) (x : m → R) :
    A.cokernelBaseChangeEquiv (S := S) (s ⊗ₜ[R] Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (fun i ↦ algebraMap R S (x i) * s) := by
  simp [cokernelBaseChangeEquiv, Submodule.Quotient.equiv_apply,
    piScalarRight_apply, piScalarRightHom_tmul, Algebra.smul_def]

/-- The inverse comparison carries a scalar multiple of a standard quotient generator to
the corresponding pure tensor. -/
@[simp]
theorem cokernelBaseChangeEquiv_symm_mk_single (A : Matrix m n R) (i : m) (s : S) :
    (A.cokernelBaseChangeEquiv (S := S)).symm (Submodule.Quotient.mk (Pi.single i s)) =
      s ⊗ₜ[R] Submodule.Quotient.mk (Pi.single i 1) := by
  classical
  apply (A.cokernelBaseChangeEquiv (S := S)).injective
  rw [LinearEquiv.apply_symm_apply, cokernelBaseChangeEquiv_tmul]
  congr 1
  ext j
  simp [Pi.single_apply]

end Matrix
