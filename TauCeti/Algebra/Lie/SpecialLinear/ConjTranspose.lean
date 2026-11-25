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
# Transpose and conjugate transpose on the special linear Lie algebra

Over a commutative ring, the trace of `Aᵀ` is the trace of `A`, so the trace-zero matrices
`sl n R` are closed under transpose, and hence under the involution `A ↦ -Aᵀ` (the Cartan
involution when `R = ℝ`). Over a commutative star ring, the trace of `Aᴴ` is the conjugate of the
trace of `A`, so `sl n R` is also closed under conjugate transpose, and hence under `X ↦ -Xᴴ`.
-/

public section

open Matrix

namespace LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Mathlib's special linear Lie algebra `sl n R` is stable under transposition. -/
theorem transpose_mem_sl {A : Matrix n n R} (hA : A ∈ sl n R) : Aᵀ ∈ sl n R := by
  rw [mem_sl_iff] at hA ⊢
  rwa [trace_transpose]

/-- Mathlib's special linear Lie algebra `sl n R` is stable under the involution `A ↦ -Aᵀ` (the
Cartan involution when `R = ℝ`). -/
theorem neg_transpose_mem_sl {A : Matrix n n R} (hA : A ∈ sl n R) : -Aᵀ ∈ sl n R :=
  neg_mem (transpose_mem_sl hA)

variable [StarRing R]

/-- The conjugate transpose of a trace-zero matrix has trace zero. -/
theorem conjTranspose_mem_sl {A : Matrix n n R} (hA : A ∈ sl n R) : Aᴴ ∈ sl n R := by
  simp_all [mem_sl_iff]

end LieAlgebra.SpecialLinear
