/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-!
# Polarizing the trace quadratic form of a matrix

For a fixed square matrix `S`, the map `Θ ↦ trace (Θ * S * Θ * S)` is a quadratic form on square
matrices. This file records its expansion at a sum, which is the polarization identity for that
form: the two mixed products are cyclic rotations of one another, so they have the same trace and
the cross term appears with coefficient two.

The form is the one whose polarization gives the covariance of two trace statistics of a Wishart
matrix.

## Main results

* `Matrix.trace_add_mul_mul_add_mul` — the expansion of `trace ((Θ₁ + Θ₂) * S * (Θ₁ + Θ₂) * S)`.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [CommSemiring R]

/-- The quadratic form `Θ ↦ trace (Θ * S * Θ * S)` expanded at a sum. The cross term carries a
factor of two because exchanging the two matrices rotates the product cyclically, which leaves
the trace unchanged. -/
theorem trace_add_mul_mul_add_mul (S Θ₁ Θ₂ : Matrix n n R) :
    ((Θ₁ + Θ₂) * S * (Θ₁ + Θ₂) * S).trace =
      (Θ₁ * S * Θ₁ * S).trace + 2 * (Θ₁ * S * Θ₂ * S).trace + (Θ₂ * S * Θ₂ * S).trace := by
  have hcomm : (Θ₂ * S * Θ₁ * S).trace = (Θ₁ * S * Θ₂ * S).trace := by
    rw [Matrix.mul_assoc (Θ₂ * S) Θ₁ S, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, hcomm]
  ring

end Matrix
