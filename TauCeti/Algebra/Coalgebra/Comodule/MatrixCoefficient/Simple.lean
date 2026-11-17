/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.Finiteness.Cardinality
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trace
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
public import TauCeti.Algebra.Coalgebra.Subcomodule.Convolution
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.LinearAlgebra.Trace.Nondegenerate

/-!
# The coefficient space of a simple comodule

Over an algebraically closed field, the matrix coefficient map of a finite-dimensional
simple comodule `M` identifies `M* ⊗ M` with its coefficient subcoalgebra. In particular,
that subcoalgebra has dimension `(dim M)²`, and for any basis `b` of `M`, the entries of its
coefficient matrix form a basis of the coefficient submodule
(`Module.Basis.matrixCoefficientSubmoduleBasis`).

The convolution dual exhausts all endomorphisms of `M` by Burnside's theorem, and the
trace pairing detects the kernel of the coefficient map. No linear reductivity assumption
on the coalgebra is needed. For an affine group this identifies the individual blocks
in the algebraic Peter--Weyl decomposition, including in positive characteristic.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), §12, matrix coefficients.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable {k C M : Type*} [Field k] [IsAlgClosed k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]
  [Module.Finite k M] [IsSimpleOrder (Subcomodule k C M)]

/-- The matrix coefficient tensor map of a finite-dimensional simple comodule over an
algebraically closed field is injective. -/
theorem matrixCoefficientTensor_injective :
    Function.Injective (matrixCoefficientTensor (R := k) (C := C) (M := M)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply (dualTensorHom_bijective (R := k) (M := M) (N := M)).1
  rw [map_zero]
  apply LinearMap.forall_trace_mul_eq_zero_iff.mp
  intro T
  obtain ⟨f, rfl⟩ := convolutionAction_surjective (C := C) T
  rw [LinearMap.trace_mul_comm, ← WithConv.apply_matrixCoefficientTensor_eq_trace, hz, map_zero]

/-- The coefficient tensor identifies a simple comodule's tensor product `M* ⊗ M` with the
underlying module of its coefficient subcoalgebra. -/
noncomputable def matrixCoefficientTensorEquiv :
    Module.Dual k M ⊗[k] M ≃ₗ[k]
      (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule :=
  LinearEquiv.ofInjective (matrixCoefficientTensor (R := k) (C := C))
      matrixCoefficientTensor_injective ≪≫ₗ
    LinearEquiv.ofEq _ _ (by
      rw [range_matrixCoefficientTensor, matrixCoefficientSubcoalgebra_toSubmodule])

/-- The coefficient-space identification is the coefficient tensor map on underlying vectors. -/
@[simp]
theorem coe_matrixCoefficientTensorEquiv_apply (z : Module.Dual k M ⊗[k] M) :
    (matrixCoefficientTensorEquiv (C := C) z : C) =
      matrixCoefficientTensor (C := C) z := by
  simp [matrixCoefficientTensorEquiv]

/-- The inverse coefficient-space identification recovers the tensor of a coefficient. -/
@[simp]
theorem matrixCoefficientTensor_matrixCoefficientTensorEquiv_symm
    (c : (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule) :
    matrixCoefficientTensor (C := C) ((matrixCoefficientTensorEquiv (C := C)).symm c) =
      (c : C) := by
  rw [← coe_matrixCoefficientTensorEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The coefficient subcoalgebra of a finite-dimensional simple comodule has square dimension
over an algebraically closed field. -/
theorem finrank_matrixCoefficientSubcoalgebra :
    Module.finrank k (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule =
      Module.finrank k M ^ 2 := by
  rw [← (matrixCoefficientTensorEquiv (k := k) (C := C) (M := M)).finrank_eq,
    Module.finrank_tensorProduct, Subspace.dual_finrank_eq, pow_two]

end TauCeti.Comodule

namespace Module.Basis

open TauCeti TauCeti.Comodule

variable {k C M ι : Type*} [Field k] [IsAlgClosed k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]
  [IsSimpleOrder (Subcomodule k C M)]

/-- Over an algebraically closed field, the entries of the coefficient matrix of a simple
comodule form a basis of its coefficient submodule. -/
noncomputable def matrixCoefficientSubmoduleBasis (b : Basis ι k M) :
    Basis (ι × ι) k (matrixCoefficientSubmodule (R := k) (C := C) (M := M)) :=
  open scoped Classical in
  let _ : Module.Finite k M := finite_of_isSimpleOrder (R := k) (C := C) (M := M)
  let _ : Finite ι := Module.Finite.finite_basis b
  let _ : Fintype ι := Fintype.ofFinite ι
  ((b.dualBasis.tensorProduct b).map (matrixCoefficientTensorEquiv (k := k) (C := C) (M := M))).map
    (LinearEquiv.ofEq _ _ (matrixCoefficientSubcoalgebra_toSubmodule (R := k) (C := C) (M := M)))

/-- The `(i, j)` basis vector of `matrixCoefficientSubmoduleBasis` is the `(i, j)` entry of the
coefficient matrix. -/
@[simp]
theorem coe_matrixCoefficientSubmoduleBasis (b : Basis ι k M) (p : ι × ι) :
    (b.matrixCoefficientSubmoduleBasis (C := C) p : C) =
      coefficientMatrix (C := C) b p.1 p.2 := by
  classical
  rcases p with ⟨i, j⟩
  have : Module.Finite k M := finite_of_isSimpleOrder (R := k) (C := C) (M := M)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have hcoord : b.dualBasis i = b.coord i := by
    ext m
    exact b.dualBasis_apply i m
  simp [matrixCoefficientSubmoduleBasis, coefficientMatrix_apply, Basis.tensorProduct_apply,
    hcoord]

end Module.Basis
