/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trace
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
public import TauCeti.Algebra.Coalgebra.Subcomodule.Convolution
import TauCeti.LinearAlgebra.Trace.Nondegenerate

/-!
# The coefficient space of a simple comodule

Over an algebraically closed field, the matrix coefficient map of a finite-dimensional
simple comodule `M` identifies `M* ⊗ M` with its coefficient subcoalgebra. In particular,
that subcoalgebra has dimension `(dim M)²`.

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
  apply TauCeti.LinearMap.eq_zero_of_trace_mul_eq_zero
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
theorem coe_matrixCoefficientTensorEquiv (z : Module.Dual k M ⊗[k] M) :
    (matrixCoefficientTensorEquiv (C := C) z : C) =
      matrixCoefficientTensor (C := C) z := by
  simp [matrixCoefficientTensorEquiv]

/-- The inverse coefficient-space identification recovers the tensor of a coefficient. -/
@[simp]
theorem matrixCoefficientTensor_matrixCoefficientTensorEquiv_symm
    (c : (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule) :
    matrixCoefficientTensor (C := C) ((matrixCoefficientTensorEquiv (C := C)).symm c) =
      (c : C) := by
  rw [← coe_matrixCoefficientTensorEquiv, LinearEquiv.apply_symm_apply]

/-- The coefficient subcoalgebra of a finite-dimensional simple comodule has square dimension
over an algebraically closed field. -/
theorem finrank_matrixCoefficientSubcoalgebra :
    Module.finrank k (matrixCoefficientSubcoalgebra (R := k) (C := C) (M := M)).toSubmodule =
      Module.finrank k M ^ 2 := by
  rw [← (matrixCoefficientTensorEquiv (k := k) (C := C) (M := M)).finrank_eq,
    Module.finrank_tensorProduct, Subspace.dual_finrank_eq, pow_two]

end TauCeti.Comodule
