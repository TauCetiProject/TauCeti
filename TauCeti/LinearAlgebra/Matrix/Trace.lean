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

Fix a square matrix `S`. This file records two identities for the trace of a product that
alternates between `S` and two further matrices. The first expands the quadratic map
`M ↦ trace (M * S * M * S)` at a sum, so that polarization recovers the symmetric bilinear map
`(M, N) ↦ trace (M * S * N * S)` from it. The second evaluates such an alternating product at
matrix units, where it collapses to a product of two entries.

## Main results

* `TauCeti.trace_add_mul_add_mul`: the expansion of `trace ((M + N) * S * (M + N) * S)` into the
  two pure terms and twice the mixed term;
* `TauCeti.trace_single_mul_mul_single_mul`: the value of
  `trace (single i j c * A * single k l d * B)` as a product of entries of `A` and `B`.
-/

public section

open Matrix

namespace TauCeti

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

variable [DecidableEq n]

/-- A product alternating between two matrix units and two matrices has trace the product of the
matching entries of the two matrices, scaled by the coefficients of the units. -/
theorem trace_single_mul_mul_single_mul (i j k l : n) (c d : R) (A B : Matrix n n R) :
    (single i j c * A * single k l d * B).trace = c * d * (A j k * B l i) := by
  have hmul (x : n) : (A * single k l d) j x = if l = x then A j k * d else 0 := by
    rw [Matrix.mul_apply]
    by_cases hx : l = x
    · subst x
      simp [Matrix.single_apply]
    · simp [hx]
  calc
    (single i j c * A * single k l d * B).trace =
        (single i j c * (A * single k l d * B)).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = c • ((A * single k l d * B) j i) := by
      rw [Matrix.trace_single_mul]
    _ = c * d * (A j k * B l i) := by
      rw [Matrix.mul_apply]
      simp_rw [hmul]
      simp only [smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring

end TauCeti
