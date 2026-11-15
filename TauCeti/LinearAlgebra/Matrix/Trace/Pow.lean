/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Entries and traces of matrix powers as sums over walks

For a square matrix `A` over a commutative semiring, the `(i, j)` entry of `A ^ (k + 1)` is the
sum, over all walks `i = v₀ → v₁ → ⋯ → vₖ → vₖ₊₁ = j` of `k + 1` steps, of the products
`A v₀ v₁ * A v₁ v₂ * ⋯ * A vₖ vₖ₊₁` of the entries along the walk. Taking the trace closes the
walks up: for `k ≠ 0`,

`trace (A ^ k) = ∑ w : Fin k → ι, ∏ t, A (w t) (w (t + 1))`,

where the indices of the closed walk `w` are read cyclically through `finRotate k`.

This is the trace-word expansion on which the moment method for random matrices rests: the
expected moments of a random matrix are expanded into expectations of products of entries
indexed by closed walks, which are then analysed combinatorially.

## Main results

* `Matrix.pow_succ_apply_eq_sum_prod`: the entries of `A ^ (k + 1)` as sums over walks.
* `Matrix.trace_pow_eq_sum_prod`: the trace of `A ^ k`, `k ≠ 0`, as a sum over closed walks.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3.
-/

public section

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The `(i, j)` entry of `A ^ (k + 1)` is the sum, over the interior vertices `w` of the walks
of `k + 1` steps from `i` to `j`, of the product of the entries of `A` along the walk
`i, w 0, …, w (k - 1), j`. -/
theorem pow_succ_apply_eq_sum_prod (A : Matrix ι ι R) (k : ℕ) (i j : ι) :
    (A ^ (k + 1)) i j = ∑ w : Fin k → ι,
      ∏ t : Fin (k + 1),
        A ((Fin.cons i w : Fin (k + 1) → ι) t) ((Fin.snoc w j : Fin (k + 1) → ι) t) := by
  induction k generalizing i with
  | zero => simp [Fin.snoc]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, ← (Fin.consEquiv fun _ ↦ ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Fin.consEquiv_apply, ← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ (n := k + 1)]
    simp

/-- **Trace-word expansion.** For `k ≠ 0`, the trace of `A ^ k` is the sum, over all closed walks
`w : Fin k → ι` of length `k`, of the product of the entries of `A` along the steps
`w t → w (t + 1)`, the indices being read cyclically. For `k = 0` the left side is the size of `ι`
while the right side is `1`. -/
theorem trace_pow_eq_sum_prod (A : Matrix ι ι R) {k : ℕ} (hk : k ≠ 0) :
    (A ^ k).trace = ∑ w : Fin k → ι, ∏ t, A (w t) (w (finRotate k t)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp_rw [trace, diag_apply, pow_succ_apply_eq_sum_prod, Fin.snoc_eq_cons_rotate]
  rw [← (Fin.consEquiv fun _ ↦ ι).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv_apply]

end Matrix
