/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL`, its coercion to matrices, and the determinant occur in the statement below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Conjugation invariants in the general linear group

This file records elementary invariants of conjugation in a general linear group that are useful
across the concrete subgroup and conjugacy-class computations.

## Main results

* `Matrix.GeneralLinearGroup.det_sub_algebraMap_conj`: shifting a matrix by a scalar and taking its
  determinant is invariant under conjugation.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Shifting a matrix by a scalar and taking its determinant is invariant under conjugation in
the general linear group. -/
theorem det_sub_algebraMap_conj (g x : GL n R) (a : R) :
    (((x⁻¹ * g * x : GL n R) : Matrix n n R) - algebraMap R (Matrix n n R) a).det =
      ((g : Matrix n n R) - algebraMap R (Matrix n n R) a).det := by
  have hxx : ((x⁻¹ : GL n R) : Matrix n n R) * (x : Matrix n n R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcancel : ((x⁻¹ : GL n R) : Matrix n n R) *
      algebraMap R (Matrix n n R) a * (x : Matrix n n R) =
      algebraMap R (Matrix n n R) a := by
    rw [mul_assoc, Algebra.commutes a (x : Matrix n n R), ← mul_assoc, hxx, one_mul]
  have hsplit : ((x⁻¹ * g * x : GL n R) : Matrix n n R) -
      algebraMap R (Matrix n n R) a =
      ((x⁻¹ : GL n R) : Matrix n n R) *
        ((g : Matrix n n R) - algebraMap R (Matrix n n R) a) * (x : Matrix n n R) := by
    rw [mul_sub, sub_mul, hcancel, Units.val_mul, Units.val_mul]
  rw [hsplit, Matrix.coe_units_inv, Matrix.det_conj' x.isUnit]

end Matrix.GeneralLinearGroup
