/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# Path weights of a square matrix

For a square matrix `M` indexed by `α` and a word `w` of length `n + 1` in `α`, the path weight
`M.pathWeight w` is the product `∏ k, M (w k) (w (k + 1))` of the entries of `M` along `w`.
Summing the path weights of the words starting at `i` gives the `i`-th row sum `(M ^ n *ᵥ 1) i`
of `M ^ n`: prepending `i` to a word starting at `j` multiplies its weight by `M i j`, which is the
recursion `M ^ (n + 1) *ᵥ 1 = M *ᵥ (M ^ n *ᵥ 1)`.

## Main definitions

* `Matrix.pathWeight M w`: the product `∏ k, M (w k) (w (k + 1))` along a word `w`.

## Main results

* `Matrix.sum_pathWeight_cons`: the path weights of words starting at `i` sum to `(M ^ n *ᵥ 1) i`.
* `Matrix.sum_pathWeight`: all path weights of words of length `n + 1` sum to
  `∑ i, (M ^ n *ᵥ 1) i`.
-/

public section

open scoped Matrix

namespace Matrix

variable {α R : Type*}

section CommMonoid

variable [CommMonoid R]

/-- The product `∏ k, M (w k) (w (k + 1))` of the entries of `M` along a word `w` of length
`n + 1`. -/
def pathWeight (M : Matrix α α R) {n : ℕ} (w : Fin (n + 1) → α) : R :=
  ∏ k : Fin n, M (w k.castSucc) (w k.succ)

theorem pathWeight_def (M : Matrix α α R) {n : ℕ} (w : Fin (n + 1) → α) :
    M.pathWeight w = ∏ k : Fin n, M (w k.castSucc) (w k.succ) :=
  (rfl)

/-- A word of length `1` has no transitions, so its path weight is the empty product `1`. -/
@[simp]
theorem pathWeight_fin_one (M : Matrix α α R) (w : Fin 1 → α) : M.pathWeight w = 1 := by
  simp [pathWeight_def]

@[simp]
theorem pathWeight_cons (M : Matrix α α R) {n : ℕ} (i : α) (w : Fin (n + 1) → α) :
    M.pathWeight (Fin.cons i w : Fin (n + 2) → α) = M i (w 0) * M.pathWeight w := by
  simp only [pathWeight_def, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.castSucc_succ, Fin.cons_succ]

end CommMonoid

variable [Fintype α] [DecidableEq α] [CommSemiring R]

/-- The path weights of the words of length `n + 1` starting at `i` sum to `(M ^ n *ᵥ 1) i`. -/
theorem sum_pathWeight_cons (M : Matrix α α R) (n : ℕ) (i : α) :
    ∑ w : Fin n → α, M.pathWeight (Fin.cons i w : Fin (n + 1) → α) = (M ^ n *ᵥ 1) i := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, mulVec, dotProduct, ← (Fin.consEquiv fun _ ↦ α).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Fin.consEquiv_apply, pathWeight_cons, Fin.cons_zero, ← Finset.mul_sum, ih]

/-- All path weights of words of length `n + 1` sum to `∑ i, (M ^ n *ᵥ 1) i`. -/
theorem sum_pathWeight (M : Matrix α α R) (n : ℕ) :
    ∑ w : Fin (n + 1) → α, M.pathWeight w = ∑ i, (M ^ n *ᵥ 1) i := by
  rw [← (Fin.consEquiv fun _ ↦ α).sum_comp, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [Fin.consEquiv_apply, sum_pathWeight_cons]

end Matrix
