/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Eigenspaces of diagonal operators over reduced rings

This file supplies the reduced-ring diagonal-operator lemma used by concrete Lie root-space
computations. It is the generic part of the argument first developed for the diagonal Cartan of
`gl n` in `TauCeti.Algebra.Lie.GeneralLinear.RootSpace`; concrete Lie-algebra files provide the
adjoint-action calculation and their own weight/support API.

The main theorem extends Mathlib's `Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace`, whose
domain hypothesis is weakened here to the reduced-ring hypothesis needed by the coordinatewise
nilpotence argument.
-/

public section

namespace TauCeti

open Matrix

variable {R : Type*} [CommRing R]

/-- In a reduced ring, a power of a scalar annihilating an element already makes the scalar
annihilate that element. -/
private theorem mul_eq_zero_of_pow_mul_eq_zero [IsReduced R] {a x : R} {k : ℕ}
    (h : a ^ k * x = 0) : a * x = 0 :=
  IsNilpotent.eq_zero ⟨k + 1, by
    calc (a * x) ^ (k + 1) = a ^ k * x * (a * x ^ k) := by ring
      _ = 0 := by rw [h, zero_mul]⟩

/-- A generalized eigenspace of a diagonal operator over a reduced ring is its eigenspace.

Coordinatewise, a generalized eigenvector satisfies `(d j - μ) ^ k * x j = 0`; reducedness is
exactly what removes the nilpotent factor. -/
theorem maxGenEigenspace_toLin_diagonal_eq_eigenspace_of_isReduced [IsReduced R]
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M] (d : ι → R)
    (b : Module.Basis ι R M) (μ : R) :
    Module.End.maxGenEigenspace (Matrix.toLin b b (Matrix.diagonal d)) μ
      = Module.End.eigenspace (Matrix.toLin b b (Matrix.diagonal d)) μ := by
  refine le_antisymm (fun x hx => ?_) Module.End.eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  replace hk (j : ι) : b.repr x j * d j = μ * b.repr x j := by
    have aux : Matrix.toLin b b (Matrix.diagonal d) - μ • 1 =
        Matrix.toLin b b (Matrix.diagonal (d - μ • 1)) := by
      rw [Pi.sub_def, ← Matrix.diagonal_sub]
      simp [Module.End.one_eq_id]
    rw [aux, ← Matrix.toLin_pow, Matrix.diagonal_pow, Matrix.toLin_apply_eq_zero_iff] at hk
    have := mul_eq_zero_of_pow_mul_eq_zero (a := d j - μ) (x := b.repr x j)
      (by simpa [Matrix.mulVec_diagonal] using hk j)
    calc
      b.repr x j * d j = d j * b.repr x j := mul_comm _ _
      _ = μ * b.repr x j := by
        apply sub_eq_zero.mp
        rw [← sub_mul]
        exact this
  have aux (j : ι) : (b.repr x j * d j) • b j = μ • (b.repr x j • b j) := by
    rw [smul_smul, hk j]
  simp [toLin_apply, mulVec_eq_sum, diagonal_apply, aux, ← Finset.smul_sum]

end TauCeti
