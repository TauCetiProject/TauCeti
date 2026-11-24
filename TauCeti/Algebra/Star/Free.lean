/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Free

import TauCeti.Algebra.FreeAlgebra

/-!
# Word reversal on the free algebra

Mathlib's `star` on `FreeAlgebra R X` reverses words. This file records that it commutes with
scalar multiplication, so it is `R`-linear even though `R` carries no star structure, and that it
does not change the constant term `FreeAlgebra.algebraMapInv`.
-/

public section

namespace FreeAlgebra

variable {R X : Type*} [CommSemiring R]

/-- Word reversal commutes with scalar multiplication. -/
@[simp]
protected theorem star_smul (r : R) (a : FreeAlgebra R X) : star (r • a) = r • star a := by
  rw [Algebra.smul_def, star_mul, star_algebraMap, ← Algebra.commutes, Algebra.smul_def]

/-- Word reversal does not change the constant term. -/
@[simp]
theorem algebraMapInv_star (a : FreeAlgebra R X) : algebraMapInv (star a) = algebraMapInv a := by
  induction a using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 x => simp
  | mul a b ha hb => simp [ha, hb, mul_comm]
  | add a b ha hb => simp [ha, hb]

end FreeAlgebra
