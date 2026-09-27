/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries

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

namespace QuadraticForm

section CommRing

variable {K L V : Type*} [CommRing K] [CommRing L] [Algebra K L]
  [Invertible (2 : L)] [AddCommGroup V] [Module L V]
  [Module K V] [IsScalarTower K L V]

/-- The tensor product of `⟨a⟩` with `Q` is isometric to `a • Q` by the left unit map. -/
def tensorLIdSmul (Q : QuadraticForm L V) (a : L) :
    (QuadraticForm.tmul
      (a • (QuadraticMap.sq (R := L) (A := L) : QuadraticForm L L)) Q).IsometryEquiv
      (a • Q) := by
  have h : QuadraticForm.tmul (a • (QuadraticMap.sq (R := L) (A := L) : QuadraticForm L L)) Q =
      QuadraticForm.tmul (QuadraticMap.sq (R := L) (A := L) : QuadraticForm L L)
        (a • Q) := by
    apply _root_.baseChange_ext
    intro v
    simp [QuadraticForm.tmul, mul_comm]
  rw [h]
  exact QuadraticForm.tensorLId (a • Q)

/-- Changing the functional by `x ↦ s (a * x)` tensors the form with `⟨a⟩`.
No nonzeroness or finite-dimensionality is needed for this isometry. -/
def scharlauTransferChangeFunctional (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) :
    (Q.scharlauTransfer (s.comp (LinearMap.mul K L a))).IsometryEquiv
      ((QuadraticForm.tmul
        (a • (QuadraticMap.sq (R := L) (A := L) : QuadraticForm L L)) Q).scharlauTransfer s) := by
  rw [QuadraticMap.scharlauTransfer_comp_mul]
  exact ((tensorLIdSmul Q a).scharlauTransfer s).symm

end CommRing

section Field

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [Invertible (2 : L)] [FiniteDimensional K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-- Transfers along two nonzero functionals on a finite extension differ by tensoring
with a one-dimensional form. The unit relating the functionals is unique, although the
resulting isometry need not determine it. -/
theorem exists_unit_scharlauTransfer_changeFunctional (Q : QuadraticForm L V)
    (s t : L →ₗ[K] K) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Lˣ, (Q.scharlauTransfer t).Equivalent
      ((QuadraticForm.tmul
        ((a : L) • (QuadraticMap.sq (R := L) (A := L) : QuadraticForm L L)) Q).scharlauTransfer
        s) := by
  obtain ⟨a, ha, _⟩ := s.existsUnique_unit_apply_eq_apply_mul t hs ht
  refine ⟨a, ?_⟩
  have h : t = s.comp (LinearMap.mul K L (a : L)) := by
    ext x
    simpa using ha x
  rw [h]
  exact ⟨scharlauTransferChangeFunctional Q s (a : L)⟩

end Field

end QuadraticForm

end TauCeti
