/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Nonnegative sums of permutation matrices

Each permutation's weight bounds the entries on its diagonal in a nonnegative weighted
sum of permutation matrices. This lets support arguments recover a whole permutation
diagonal from a positive weight. The uniform average over a nonempty set of permutations, each
lying in the support of a matrix `K` and together covering it, has the zero pattern of `K`.
-/

public section

namespace Equiv.Perm

/-- Every entry of a permutation matrix is nonnegative. -/
theorem permMatrix_nonneg {n R : Type*} [DecidableEq n]
    [Zero R] [One R] [Preorder R] [ZeroLEOneClass R] (σ : Equiv.Perm n) (i j : n) :
    0 ≤ σ.permMatrix R i j := by
  simp only [PEquiv.toMatrix_toPEquiv_apply]
  exact (Pi.single_nonneg (α := fun _ : n ↦ R)).2 zero_le_one _

end Equiv.Perm

namespace Matrix

variable {n R : Type*} [DecidableEq n]
  [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-- A nonnegative weighted sum of permutation matrices has entries on each included
permutation diagonal at least as large as that permutation's weight. -/
theorem weight_le_sum_permMatrix (s : Finset (Equiv.Perm n)) (w : Equiv.Perm n → R)
    (hw : ∀ τ ∈ s, 0 ≤ w τ) {σ : Equiv.Perm n} (hσ : σ ∈ s) (k : n) :
    w σ ≤ (∑ τ ∈ s, w τ • τ.permMatrix R) k (σ k) := by
  simpa [Matrix.sum_apply, smul_apply, smul_eq_mul, PEquiv.toMatrix_toPEquiv_apply] using
    (Finset.single_le_sum (f := fun τ ↦ w τ * τ.permMatrix R k (σ k))
      (fun τ hτ ↦ mul_nonneg (hw τ hτ) (τ.permMatrix_nonneg k (σ k))) hσ)

end Matrix

namespace Matrix

/-- The average of the permutation matrices over a nonempty set `s` of permutations, each of which
stays inside the support of `K` and which together cover the support, has the zero pattern of
`K`. -/
theorem average_permMatrix_apply_eq_zero_iff {n R : Type*} [DecidableEq n]
    [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] {K : Matrix n n R}
    {s : Finset (Equiv.Perm n)} (hs : s.Nonempty) (hsub : ∀ σ ∈ s, ∀ k, K k (σ k) ≠ 0)
    (hcover : ∀ i j, K i j ≠ 0 → ∃ σ ∈ s, σ i = j) (i j : n) :
    (∑ σ ∈ s, (s.card : R)⁻¹ • σ.permMatrix R) i j = 0 ↔ K i j = 0 := by
  have hentry : (∑ σ ∈ s, (s.card : R)⁻¹ • σ.permMatrix R) i j
      = ∑ σ ∈ s, (s.card : R)⁻¹ * σ.permMatrix R i j := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · intro hzero
    by_contra hij
    obtain ⟨σ, hσmem, hσij⟩ := hcover i j hij
    have hle : (s.card : R)⁻¹ ≤ (∑ σ ∈ s, (s.card : R)⁻¹ • σ.permMatrix R) i j := by
      simpa only [hσij] using
        weight_le_sum_permMatrix s (fun _ ↦ (s.card : R)⁻¹)
          (fun _ _ ↦ by positivity) hσmem i
    have hpos : 0 < (s.card : R)⁻¹ := inv_pos.2 (by exact_mod_cast hs.card_pos)
    exact (hpos.trans_le hle).ne' hzero
  · intro hij
    rw [hentry]
    apply Finset.sum_eq_zero
    intro σ hσ
    have hσij : σ i ≠ j := by
      intro heq
      exact hsub σ hσ i (heq ▸ hij)
    simp only [PEquiv.toMatrix_toPEquiv_apply]
    simp [hσij]

end Matrix
