/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Star.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Basic

/-!
# Conjugate transpose on the special linear Lie algebra

Over a commutative star ring, the trace of `Aᴴ` is the conjugate of the trace of `A`, so the
trace-zero matrices `sl n R` are closed under conjugate transpose, and hence under `X ↦ -Xᴴ`.
-/

public section

open Matrix

namespace LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]

/-- The conjugate transpose of a trace-zero matrix has trace zero. -/
theorem conjTranspose_mem_sl {A : Matrix n n R} (hA : A ∈ sl n R) : Aᴴ ∈ sl n R := by
  simp_all [mem_sl_iff]

end LieAlgebra.SpecialLinear
