/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Two-sided invertible equivalence of matrices

Matrices related by `L * A * R` with `L` and `R` invertible. Rows and columns are transformed
independently, so the two index types are separate, and nothing here needs more than a
semiring.

## Main results

* `Matrix.GeneralLinearGroup.inv_mul_mul_inv_eq_iff_mul_mul_eq`: inverting a two-sided
  invertible transformation.
* `Equiv.reindexGL`: reindexing the rows and columns of a general linear group along an
  equivalence of index types, with identity, inverse, and composition laws.
-/

namespace Matrix.GeneralLinearGroup

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

public section

/-- **Inverting a two-sided invertible transformation.** `L⁻¹ * B * R⁻¹ = A` exactly when
`L * A * R = B`. The rows and columns are transformed independently, so they need not share an
index type. -/
theorem inv_mul_mul_inv_eq_iff_mul_mul_eq {S : Type*} [Semiring S]
    {A B : Matrix ι κ S} (L : GeneralLinearGroup ι S) (R : GeneralLinearGroup κ S) :
    (↑L⁻¹ : Matrix ι ι S) * B * (↑R⁻¹ : Matrix κ κ S) = A ↔
      (L : Matrix ι ι S) * A * (R : Matrix κ κ S) = B := by
  -- the rectangular products are not monoid products, so the unit cancellations are reached by
  -- reassociating: first to cancel the left factors, then to cancel the right ones
  constructor <;> rintro rfl <;> simp [← Matrix.mul_assoc] <;> simp [Matrix.mul_assoc]

end

end Matrix.GeneralLinearGroup

namespace Equiv

public section

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
  (e : n ≃ p) (R : Type*) [Semiring R]

/-- Reindexing along an equivalence of index types, as a group isomorphism of general linear
groups. -/
def reindexGL : GL n R ≃* GL p R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

@[simp]
theorem coe_reindexGL (M : GL n R) :
    (reindexGL e R M : Matrix p p R) = (M : Matrix n n R).submatrix e.symm e.symm :=
  (rfl)

/-- Reindexing along the identity equivalence is the identity. -/
@[simp]
theorem reindexGL_refl : (Equiv.refl n).reindexGL R = MulEquiv.refl (GL n R) :=
  (rfl)

/-- The inverse of reindexing is reindexing along the inverse equivalence. -/
@[simp]
theorem reindexGL_symm : (e.reindexGL R).symm = e.symm.reindexGL R :=
  (rfl)

/-- Successive reindexings compose according to the equivalences of index types. -/
@[simp]
theorem reindexGL_trans_reindexGL {q : Type*} [Fintype q] [DecidableEq q] (e' : p ≃ q) :
    (e.reindexGL R).trans (e'.reindexGL R) = (e.trans e').reindexGL R :=
  (rfl)

/-- Reindexing back after reindexing recovers the original invertible matrix. -/
@[simp]
theorem reindexGL_symm_apply_reindexGL (M : GL n R) :
    e.symm.reindexGL R (e.reindexGL R M) = M := by
  rw [← reindexGL_symm, MulEquiv.symm_apply_apply]

/-- Reindexing after reindexing back recovers the original invertible matrix. -/
@[simp]
theorem reindexGL_apply_symm_reindexGL (M : GL p R) :
    e.reindexGL R (e.symm.reindexGL R M) = M := by
  rw [← reindexGL_symm, MulEquiv.apply_symm_apply]

end

end Equiv
