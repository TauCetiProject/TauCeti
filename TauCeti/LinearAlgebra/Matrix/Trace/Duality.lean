/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace duality for square matrices

Over a commutative semiring `R`, every linear functional `f` on `n × n` matrices is of the form
`x ↦ Tr (ρ x)` for a unique matrix `ρ`, `Matrix.existsUnique_trace_mul_eq`: the entries of `ρ`
are the values of `f` on the matrix units.

A square matrix `M` is scalar exactly when the functional `x ↦ Tr (M x)` is tracial, that is
`Tr (M a b) = Tr (M b a)` for all `a, b`, `Matrix.mem_range_scalar_iff_trace_mul_mul_comm`:
by nondegeneracy of the trace form such an `M` commutes with every matrix.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [CommSemiring R]

/-- **Trace duality.** Every linear functional on square matrices is `x ↦ Tr (ρ x)` for a unique
matrix `ρ`. -/
theorem existsUnique_trace_mul_eq (f : Matrix n n R →ₗ[R] R) :
    ∃! ρ : Matrix n n R, ∀ x, f x = (ρ * x).trace := by
  classical
  refine ⟨of fun i j => f (single j i 1), fun x => ?_, fun ρ hρ => ?_⟩
  · have hf (i j : n) (a : R) : f (single i j a) = a * f (single i j 1) := by
      rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [matrix_eq_sum_single x]
    simp only [map_sum, trace, diag, mul_apply, of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf, mul_comm]
  · ext i j
    simp [hρ, trace_mul_single]

variable [DecidableEq n]

/-- A square matrix `M` is scalar exactly when `Tr (M a b) = Tr (M b a)` for all `a, b`. -/
theorem mem_range_scalar_iff_trace_mul_mul_comm {M : Matrix n n R} :
    M ∈ Set.range (scalar n) ↔ ∀ a b : Matrix n n R, (M * a * b).trace = (M * b * a).trace := by
  refine ⟨?_, fun h => mem_range_scalar_of_commute_single fun i j _ => ?_⟩
  · rintro ⟨c, rfl⟩ a b
    simp only [scalar_apply, ← smul_one_eq_diagonal, smul_mul, Matrix.one_mul, trace_smul,
      trace_mul_comm a b]
  refine ext_iff_trace_mul_right.mpr fun b => ?_
  rw [h, Matrix.mul_assoc, trace_mul_comm]

end Matrix
