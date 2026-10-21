/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Eigenvectors of a matrix and of its transpose

The nonzero eigenvectors of a square matrix, for all eigenvalues together, form the set
`Matrix.eigenvectors A`. Over a field, a matrix and its transpose have eigenspaces of the same
size for every scalar `c`, because both are kernels of matrices `A - c` and `(A - c)ᵀ` of the same
rank. Over a finite field, each nonzero eigenvector has exactly one eigenvalue, so summing over
eigenvalues shows that a matrix and its transpose have equally many nonzero eigenvectors.

## Main definitions

* `Matrix.eigenvectors A`: the nonzero vectors `v` with `A *ᵥ v = c • v` for some scalar `c`.

## Main results

* `Matrix.natCard_eigenspace_transpose`: `A` and `Aᵀ` have eigenspaces of equal size.
* `Matrix.natCard_eigenvectors_transpose`: over a finite field, `A` and `Aᵀ` have equally many
  nonzero eigenvectors.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n]

/-- The nonzero eigenvectors of a square matrix, for all eigenvalues together. -/
def eigenvectors [Semiring R] (A : Matrix n n R) : Set (n → R) :=
  {v | v ≠ 0 ∧ ∃ c : R, A *ᵥ v = c • v}

@[simp]
theorem mem_eigenvectors [Semiring R] {A : Matrix n n R} {v : n → R} :
    v ∈ A.eigenvectors ↔ v ≠ 0 ∧ ∃ c : R, A *ᵥ v = c • v :=
  Iff.rfl

variable {K : Type*} [Field K]

/-- A matrix and its transpose have eigenspaces of equal size for every scalar: both are
`|K| ^ (|n| - r)`, where `r` is the common rank of `A - c` and its transpose. -/
theorem natCard_eigenspace_transpose (A : Matrix n n K) (c : K) :
    Nat.card {v : n → K // Aᵀ *ᵥ v = c • v} = Nat.card {v : n → K // A *ᵥ v = c • v} := by
  classical
  have key (B : Matrix n n K) :
      Nat.card {v : n → K // B *ᵥ v = c • v} =
        Nat.card K ^ (Fintype.card n - (B - c • 1).rank) := by
    have hker : Nat.card {v : n → K // B *ᵥ v = c • v} =
        Nat.card (LinearMap.ker (B - c • 1).mulVecLin) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v ↦ by
        simp [sub_eq_zero])
    have hrk := (B - c • 1).mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_fintype_fun_eq_card] at hrk
    rw [hker, Module.natCard_eq_pow_finrank (K := K), Matrix.rank, ← hrk, Nat.add_sub_cancel_left]
  have htr : Aᵀ - c • (1 : Matrix n n K) = (A - c • 1)ᵀ := by
    rw [transpose_sub, transpose_smul, transpose_one]
  rw [key, key, htr, rank_transpose]

/-- A matrix and its transpose have equally many nonzero eigenvectors over a finite field. -/
theorem natCard_eigenvectors_transpose [Finite K] (A : Matrix n n K) :
    Nat.card Aᵀ.eigenvectors = Nat.card A.eigenvectors := by
  have := Fintype.ofFinite K
  -- Sort the nonzero eigenvectors by their eigenvalue, which a nonzero vector determines.
  have hsigma (B : Matrix n n K) : Nat.card B.eigenvectors =
      ∑ c : K, Nat.card {v : n → K // v ≠ 0 ∧ B *ᵥ v = c • v} := by
    rw [← Nat.card_sigma]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : Σ c : K, {v : n → K // v ≠ 0 ∧ B *ᵥ v = c • v} ↦
        (⟨p.2.1, p.2.2.1, p.1, p.2.2.2⟩ : B.eigenvectors)) ⟨?_, ?_⟩)).symm
    · rintro ⟨c, v, hv, hc⟩ ⟨c', v', hv', hc'⟩ h
      obtain rfl : v = v' := congrArg Subtype.val h
      exact Sigma.subtype_ext (smul_left_injective K hv (hc.symm.trans hc')) rfl
    · rintro ⟨v, hv, c, hc⟩
      exact ⟨⟨c, v, hv, hc⟩, rfl⟩
  -- Removing the zero vector from each eigenspace lowers its size by one.
  have hzero (B : Matrix n n K) (c : K) :
      Nat.card {v : n → K // v ≠ 0 ∧ B *ᵥ v = c • v} =
        Nat.card {v : n → K // B *ᵥ v = c • v} - 1 := by
    let S : Set (n → K) := {v | B *ᵥ v = c • v}
    calc Nat.card {v : n → K // v ≠ 0 ∧ B *ᵥ v = c • v}
        = Nat.card ↥(S \ {0}) :=
          Nat.card_congr (Equiv.subtypeEquivRight fun v ↦ by simp [S, and_comm])
      _ = Nat.card S - 1 := by
          rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_sdiff_singleton_of_mem (by simp [S])
      _ = Nat.card {v : n → K // B *ᵥ v = c • v} - 1 := by rw [Set.coe_ofPred]
  rw [hsigma, hsigma]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [hzero, hzero, natCard_eigenspace_transpose]

end Matrix
