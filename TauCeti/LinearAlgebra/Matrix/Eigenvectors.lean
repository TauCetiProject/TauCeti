/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Eigenvectors of a matrix and of its transpose

The nonzero eigenvectors of a square matrix `A`, for all eigenvalues together, form the set
`Matrix.eigenvectors A`: the vectors that are eigenvectors of `A.mulVecLin`, in the sense of
`Module.End.HasEigenvector`, for some scalar. Over a field, a matrix and its transpose have
eigenspaces of the same size for every scalar `c`, because both are kernels of matrices `A - c`
and `(A - c)ᵀ` of the same rank. Over a finite field, each nonzero eigenvector has exactly one
eigenvalue, so summing over eigenvalues shows that a matrix and its transpose have equally many
nonzero eigenvectors. Over an infinite field the nonzero eigenvectors of any matrix are infinite
in number or absent, so `Nat.card` counts zero of them for both, and the equality holds over every
field. An invertible matrix and its inverse have the same nonzero eigenvectors.

## Main definitions

* `Matrix.eigenvectors A`: the nonzero vectors `v` with `A *ᵥ v = c • v` for some scalar `c`.

## Main results

* `Matrix.natCard_eigenspace_transpose`: `A` and `Aᵀ` have eigenspaces of equal size.
* `Matrix.natCard_eigenvectors_of_infinite`: over an infinite field, `Nat.card` of the nonzero
  eigenvectors is zero.
* `Matrix.natCard_eigenvectors_transpose`: `A` and `Aᵀ` have equally many nonzero eigenvectors.
* `Matrix.GeneralLinearGroup.mem_eigenvectors_iff`: membership in the eigenvectors of an
  invertible matrix, in terms of its action on vectors.
* `Matrix.GeneralLinearGroup.eigenvectors_inv`: an invertible matrix and its inverse have the
  same nonzero eigenvectors.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n]

/-- The nonzero eigenvectors of a square matrix, for all eigenvalues together: the vectors that
are eigenvectors of `A.mulVecLin` for some scalar. -/
def eigenvectors [CommRing R] (A : Matrix n n R) : Set (n → R) :=
  {v | ∃ c : R, Module.End.HasEigenvector A.mulVecLin c v}

@[simp]
theorem mem_eigenvectors [CommRing R] {A : Matrix n n R} {v : n → R} :
    v ∈ A.eigenvectors ↔ v ≠ 0 ∧ ∃ c : R, A *ᵥ v = c • v := by
  simp [eigenvectors, Module.End.hasEigenvector_iff, and_comm]

variable {K : Type*} [Field K]

/-- A matrix and its transpose have eigenspaces of equal size for every scalar: both are
`|K| ^ (|n| - r)`, where `r` is the common rank of `A - c` and its transpose. -/
theorem natCard_eigenspace_transpose (A : Matrix n n K) (c : K) :
    Nat.card (Module.End.eigenspace Aᵀ.mulVecLin c) =
      Nat.card (Module.End.eigenspace A.mulVecLin c) := by
  classical
  have key (B : Matrix n n K) :
      Nat.card (Module.End.eigenspace B.mulVecLin c) =
        Nat.card K ^ (Fintype.card n - (B - c • 1).rank) := by
    have hker : Module.End.eigenspace B.mulVecLin c = LinearMap.ker (B - c • 1).mulVecLin := by
      ext v
      simp [sub_eq_zero]
    have hrk := (B - c • 1).mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_fintype_fun_eq_card] at hrk
    rw [hker, Module.natCard_eq_pow_finrank (K := K), Matrix.rank, ← hrk, Nat.add_sub_cancel_left]
  have htr : Aᵀ - c • (1 : Matrix n n K) = (A - c • 1)ᵀ := by
    rw [transpose_sub, transpose_smul, transpose_one]
  rw [key, key, htr, rank_transpose]

/-- Over an infinite field the nonzero eigenvectors of a matrix are infinite in number or absent,
because they are closed under multiplication by nonzero scalars; either way `Nat.card` is zero. -/
theorem natCard_eigenvectors_of_infinite [Infinite K] (A : Matrix n n K) :
    Nat.card A.eigenvectors = 0 := by
  rcases A.eigenvectors.eq_empty_or_nonempty with h | ⟨v, hv⟩
  · simp [h]
  rw [mem_eigenvectors] at hv
  obtain ⟨hv0, c, hc⟩ := hv
  have := (Set.finite_singleton (0 : K)).infinite_compl.to_subtype
  refine Set.Infinite.card_eq_zero (Set.infinite_of_injective_forall_mem
    (f := fun a : ↥({0}ᶜ : Set K) ↦ (a : K) • v)
    (fun a b hab ↦ Subtype.ext (smul_left_injective K hv0 hab))
    fun a ↦ mem_eigenvectors.mpr ⟨smul_ne_zero (Set.mem_compl_singleton_iff.mp a.2) hv0, c, ?_⟩)
  rw [mulVec_smul, hc, smul_comm]

/-- A matrix and its transpose have equally many nonzero eigenvectors. Over an infinite field both
counts are zero, as `Nat.card` of an infinite or empty set. -/
theorem natCard_eigenvectors_transpose (A : Matrix n n K) :
    Nat.card Aᵀ.eigenvectors = Nat.card A.eigenvectors := by
  cases finite_or_infinite K
  case inr => rw [natCard_eigenvectors_of_infinite, natCard_eigenvectors_of_infinite]
  have := Fintype.ofFinite K
  -- Sort the nonzero eigenvectors by their eigenvalue, which a nonzero vector determines.
  have hsigma (B : Matrix n n K) : Nat.card B.eigenvectors =
      ∑ c : K, Nat.card {v : n → K // Module.End.HasEigenvector B.mulVecLin c v} := by
    rw [← Nat.card_sigma]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : Σ c : K, {v : n → K // Module.End.HasEigenvector B.mulVecLin c v} ↦
        (⟨p.2.1, p.1, p.2.2⟩ : B.eigenvectors)) ⟨?_, ?_⟩)).symm
    · rintro ⟨c, v, hc⟩ ⟨c', v', hc'⟩ h
      obtain rfl : v = v' := congrArg Subtype.val h
      exact Sigma.subtype_ext (smul_left_injective K (Module.End.hasEigenvector_iff.mp hc).2
        (hc.apply_eq_smul.symm.trans hc'.apply_eq_smul)) rfl
    · rintro ⟨v, c, hc⟩
      exact ⟨⟨c, v, hc⟩, rfl⟩
  -- Removing the zero vector from each eigenspace lowers its size by one.
  have hzero (B : Matrix n n K) (c : K) :
      Nat.card {v : n → K // Module.End.HasEigenvector B.mulVecLin c v} =
        Nat.card (Module.End.eigenspace B.mulVecLin c) - 1 := by
    calc Nat.card {v : n → K // Module.End.HasEigenvector B.mulVecLin c v}
        = Nat.card ↥((Module.End.eigenspace B.mulVecLin c : Set (n → K)) \ {0}) :=
          Nat.card_congr (Equiv.subtypeEquivRight fun v ↦ by
            simp [Module.End.hasEigenvector_iff])
      _ = Nat.card (Module.End.eigenspace B.mulVecLin c : Set (n → K)) - 1 := by
          rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_sdiff_singleton_of_mem (by simp)
      _ = Nat.card (Module.End.eigenspace B.mulVecLin c) - 1 := by rw [SetLike.coe_sort_coe]
  rw [hsigma, hsigma]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [hzero, hzero, natCard_eigenspace_transpose]

namespace GeneralLinearGroup

variable [DecidableEq n]

/-- Membership in `Matrix.eigenvectors` for an invertible matrix, in terms of its action on
vectors. -/
theorem mem_eigenvectors_iff [CommRing R] {g : GL n R} {v : n → R} :
    v ∈ eigenvectors (g : Matrix n n R) ↔ v ≠ 0 ∧ ∃ c : R, g • v = c • v := by
  simp [Units.smul_def, Matrix.smul_eq_mulVec]

open Pointwise in
/-- An invertible matrix and its inverse have the same nonzero eigenvectors: both are the nonzero
vectors whose line it stabilizes. -/
@[simp]
theorem eigenvectors_inv (g : GL n K) :
    eigenvectors (g : Matrix n n K)⁻¹ = eigenvectors (g : Matrix n n K) := by
  ext v
  rw [← coe_units_inv, mem_eigenvectors_iff, mem_eigenvectors_iff]
  refine and_congr_right fun _ ↦ ?_
  have key (h : GL n K) : h • (K ∙ v) = K ∙ v ↔ ∃ c : K, h • v = c • v :=
    Submodule.smul_span_singleton_eq_iff
  rw [← key, ← key, inv_smul_eq_iff, eq_comm]

end GeneralLinearGroup

end Matrix
