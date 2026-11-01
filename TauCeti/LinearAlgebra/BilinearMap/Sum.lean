/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Bilinear maps on finite linear combinations

A bilinear map evaluated on two finite linear combinations `∑ k ∈ s, c k • φ k` and
`∑ l ∈ t, d l • ψ l` expands as the double sum `∑ k ∈ s, ∑ l ∈ t, c k • d l • B (φ k) (ψ l)`.
This is the expansion along arbitrary families of vectors, rather than along a basis as in
Mathlib's `LinearMap.sum_repr_mul_repr_mul`.
-/

public section

namespace LinearMap

variable {R M N P ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [AddCommMonoid P] [Module R M] [Module R N] [Module R P]

/-- A bilinear map evaluated on two finite linear combinations is the double sum of its values
on the summands. -/
theorem apply_sum_smul_sum_smul (B : M →ₗ[R] N →ₗ[R] P) (s : Finset ι) (t : Finset κ)
    (c : ι → R) (φ : ι → M) (d : κ → R) (ψ : κ → N) :
    B (∑ k ∈ s, c k • φ k) (∑ l ∈ t, d l • ψ l) =
      ∑ k ∈ s, ∑ l ∈ t, c k • d l • B (φ k) (ψ l) := by
  simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

end LinearMap
