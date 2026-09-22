/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Operations on ideal quotients

This file complements `Mathlib/RingTheory/Ideal/Quotient/Operations.lean` with elementary facts
about the quotient map and the scalar action on an ideal quotient.

## Main results

* `Ideal.Quotient.smul_one_eq_mk`: scalar multiplication of the unit in an ideal quotient agrees
  with the quotient map.
-/

public section

namespace Ideal.Quotient

variable {R : Type*} [Ring R]

/-- Scalar multiplication of the unit in an ideal quotient is the quotient map. -/
@[simp]
theorem smul_one_eq_mk (I : Ideal R) [I.IsTwoSided] (r : R) :
    r • (1 : R ⧸ I) = Ideal.Quotient.mk I r := by
  calc
    r • (1 : R ⧸ I) = r • Ideal.Quotient.mk I 1 := by rw [map_one]
    _ = Ideal.Quotient.mk I r := by
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul]
      simp only [smul_eq_mul, mul_one]
      exact Ideal.Quotient.mk_eq_mk r

end Ideal.Quotient

end
