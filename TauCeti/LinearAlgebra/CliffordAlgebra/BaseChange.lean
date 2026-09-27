/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange

/-!
# Clifford involution and extension of scalars

This file records that the canonical map from a Clifford algebra into the Clifford algebra after
extension of scalars commutes with the grade involution. This is the compatibility needed to
transport twisted-conjugation actions along scalar extensions.
-/

public section

namespace CliffordAlgebra

universe u v w

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- The canonical map to the Clifford algebra after extension of scalars commutes with the grade
involution. -/
@[simp]
theorem ofBaseChangeAux_involute (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ofBaseChangeAux A Q (involute x) =
      involute (Q := Q.baseChange A) (ofBaseChangeAux A Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

end CliffordAlgebra
