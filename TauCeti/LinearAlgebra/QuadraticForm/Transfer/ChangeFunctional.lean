/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Changing the functional in Scharlau transfer

Multiplying the input of a transfer functional by `a` has the same effect as tensoring
the quadratic form with the line `⟨a⟩` before transfer. The tensor factor is placed on
the left, as in the usual change-of-functional formula. For a finite field extension,
any two nonzero functionals are related in this way by a unique unit.

The formula follows Scharlau, *Quadratic and Hermitian Forms*, Chapter 2, §5, and
Lam, *Introduction to Quadratic Forms over Fields*, Chapter VII, §1.
-/

public section

namespace TauCeti

open scoped TensorProduct

section CommSemiring

variable {K L V : Type*} [CommSemiring K] [CommRing L] [Algebra K L]
  [Invertible (2 : L)] [AddCommGroup V] [Module L V]
  [Module K V] [IsScalarTower K L V]

/-- Changing the functional by `x ↦ s (a * x)` tensors the form with `⟨a⟩`.
No nonzeroness or finite-dimensionality is needed for this isometry. -/
@[expose, simps toLinearEquiv]
def scharlauTransferChangeFunctional (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) :
    (Q.scharlauTransfer (s.comp (LinearMap.mul K L a))).IsometryEquiv
      ((QuadraticForm.tmul
        (a • (QuadraticMap.sq (R := L) (A := L) : QuadraticForm L L)) Q).scharlauTransfer s) where
  toLinearEquiv := (TensorProduct.lid L V).symm.restrictScalars K
  map_app' x := by
    rw [QuadraticMap.scharlauTransfer_comp_mul]
    simp only [QuadraticMap.scharlauTransfer_apply]
    exact congrArg s ((tensorLIdSmul Q a).symm.map_app x)

@[simp]
theorem scharlauTransferChangeFunctional_apply (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) (x : V) :
    scharlauTransferChangeFunctional Q s a x =
      (TensorProduct.lid L V).symm x := by
  rfl

@[simp]
theorem scharlauTransferChangeFunctional_symm_apply (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) (x : L ⊗[L] V) :
    (scharlauTransferChangeFunctional Q s a).symm x = TensorProduct.lid L V x := by
  rfl

end CommSemiring

section Field

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [Invertible (2 : L)] [FiniteDimensional K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-- Transfers along two nonzero functionals on a finite extension differ by tensoring
with a one-dimensional form. -/
theorem exists_unit_scharlauTransfer_changeFunctional (Q : QuadraticForm L V)
    (s t : L →ₗ[K] K) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Lˣ, (Q.scharlauTransfer t).Equivalent
      ((QuadraticForm.tmul
        ((a : L) • (QuadraticMap.sq (R := L) (A := L) : QuadraticForm L L)) Q).scharlauTransfer
        s) := by
  obtain ⟨a, h⟩ := Q.exists_unit_scharlauTransfer_eq s t hs ht
  refine ⟨a, ?_⟩
  rw [h]
  exact ⟨(tensorLIdSmul Q (a : L)).symm.scharlauTransfer s⟩

end Field

end TauCeti
