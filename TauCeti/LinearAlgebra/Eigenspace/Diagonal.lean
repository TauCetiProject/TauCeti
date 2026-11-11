/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic.LinearCombination

/-!
# Eigenspaces of diagonal operators over reduced rings

For a diagonal linear operator over a reduced ring, coordinatewise generalized eigenvector
conditions already imply the corresponding eigenvector conditions. The theorem below identifies
the maximal generalized eigenspace with the eigenspace, so a diagonalized action can be studied
through its ordinary eigenvectors.

The main theorem generalizes Mathlib's `Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace`
from domains to reduced rings. Some hypothesis of this kind is needed: over `ZMod 4`, the zero
operator has every vector in its maximal generalized `2`-eigenspace, but not in its `2`-eigenspace.
-/

public section

namespace TauCeti

open Matrix Module End

variable {R : Type*} [CommRing R]

/-- A generalized eigenspace of a diagonal operator over a reduced ring is its eigenspace.

This generalizes `Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace` from domains to reduced
rings. -/
@[simp]
theorem maxGenEigenspace_toLin_diagonal_eq_eigenspace_of_isReduced [IsReduced R]
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M] (d : ι → R)
    {μ : R} (b : Basis ι R M) :
    maxGenEigenspace ((diagonal d).toLin b b) μ = eigenspace ((diagonal d).toLin b b) μ := by
  refine le_antisymm (fun x hx => ?_) eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace _ _ _).mp hx
  replace hk (j : ι) : b.repr x j * d j = μ * b.repr x j := by
    have aux : (diagonal d).toLin b b - μ • 1 = (diagonal (d - μ • 1)).toLin b b := by
      rw [Pi.sub_def, ← diagonal_sub]
      simp [one_eq_id]
    rw [aux, ← toLin_pow, diagonal_pow, toLin_apply_eq_zero_iff] at hk
    -- Coordinatewise, `(d j - μ) ^ k` kills `x j`; reducedness removes the nilpotent factor.
    have hcoord : (d j - μ) ^ k * b.repr x j = 0 := by
      simpa [mulVec_diagonal] using hk j
    have hmul : (d j - μ) * b.repr x j = 0 := by
      generalize d j - μ = a at hcoord ⊢
      exact IsNilpotent.eq_zero ⟨k + 1, by linear_combination a * b.repr x j ^ k * hcoord⟩
    linear_combination hmul
  simp [toLin_apply, mulVec_eq_sum, diagonal_apply, hk, mul_smul, ← Finset.smul_sum]

end TauCeti
