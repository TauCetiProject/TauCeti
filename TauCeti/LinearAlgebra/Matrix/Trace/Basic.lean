/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-!
# Traces of products alternating with a fixed matrix

Fix a square matrix `S`. This file expands the quadratic map `M ↦ trace (M * S * M * S)` at a
sum, so that polarization recovers the symmetric bilinear map `(M, N) ↦ trace (M * S * N * S)`
from it.

## Main results

* `Matrix.trace_add_mul_add_mul`: the expansion of `trace ((M + N) * S * (M + N) * S)` into the
  two pure terms and twice the mixed term.
* `Matrix.trace_pow_mul_eq_trace_pow_mul`: positive powers of rectangular products `A * B` and
  `B * A` have equal traces.
-/

public section

namespace Matrix

section RectangularProducts

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [CommSemiring R]

/-- For rectangular matrices over a commutative semiring, positive powers of `A * B` and `B * A`
have equal traces. -/
theorem trace_pow_mul_eq_trace_pow_mul (A : Matrix ι κ R) (B : Matrix κ ι R) {k : ℕ}
    (hk : k ≠ 0) : ((A * B) ^ k).trace = ((B * A) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hpow := Matrix.mul_pow_mul A B
  calc
    ((A * B) ^ (j + 1)).trace = ((A * B) ^ j * A * B).trace := by
      rw [pow_succ]
      simp only [Matrix.mul_assoc]
    _ = (B * ((A * B) ^ j * A)).trace := Matrix.trace_mul_comm _ _
    _ = (B * (A * (B * A) ^ j)).trace := by rw [hpow]
    _ = ((B * A) ^ (j + 1)).trace := by
      rw [← Matrix.mul_assoc, pow_succ']

end RectangularProducts

variable {n R : Type*} [Fintype n] [CommSemiring R]

/-- The quadratic map `M ↦ trace (M * S * M * S)` expands at a sum into the two pure terms plus
twice the mixed term. -/
theorem trace_add_mul_add_mul (M N S : Matrix n n R) :
    ((M + N) * S * (M + N) * S).trace =
      (M * S * M * S).trace + 2 * (M * S * N * S).trace + (N * S * N * S).trace := by
  have hcross : (N * S * M * S).trace = (M * S * N * S).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (N * S) (M * S)
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
  rw [hcross]
  ring

end Matrix
