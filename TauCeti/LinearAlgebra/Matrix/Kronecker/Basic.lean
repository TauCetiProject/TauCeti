/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Products of Kronecker products with matrix units

A Kronecker product `Matrix.single i j 1 ⊗ₖ X` is the block matrix carrying `X` in the block from
`j` to `i` and zero elsewhere. Such block matrices multiply along chains: the product of
`single (a t) (b t) 1 ⊗ₖ X t` over a chain in which each block starts where the next one ends is
the single block of the product of the `X t`.

## Main results

* `Matrix.single_one_kronecker_mul_single_one_kronecker`: two block matrices multiply blockwise.
* `Matrix.list_prod_ofFn_single_kronecker`: the product of the block matrices along a chain.
-/

public section

open scoped Kronecker

namespace Matrix

variable {R l m : Type*} [Semiring R] [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]

omit [Fintype l] [Fintype m] [DecidableEq m] in
/-- Two block matrices multiply blockwise when the first block ends where the second starts.
Unlike `Matrix.mul_kronecker_mul`, this needs no commutativity: the entries of a matrix unit are
central. -/
theorem single_one_kronecker_mul_single_one_kronecker {l' l'' m' m'' : Type*} [DecidableEq l']
    [DecidableEq l''] [Fintype l'] [Fintype m'] (i : l) (j : l') (k : l'') (X : Matrix m m' R)
    (Y : Matrix m' m'' R) :
    (single i j (1 : R) ⊗ₖ X) * (single j k 1 ⊗ₖ Y) = single i k 1 ⊗ₖ (X * Y) := by
  ext ⟨i', a⟩ ⟨k', c⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [single_apply, Matrix.mul_apply, ite_and]
  split_ifs <;> rfl

/-- **A product of block matrices along a chain.** If each block `X t` sits in the block from `b t`
to `a t`, and each starts where the next one ends, then the product is the block of the product of
the `X t`, from the start `b (Fin.last n)` of the last block to the end `a 0` of the first. -/
theorem list_prod_ofFn_single_kronecker {n : ℕ} (a b : Fin (n + 1) → l)
    (X : Fin (n + 1) → Matrix m m R) (h : ∀ i : Fin n, b i.castSucc = a i.succ) :
    (List.ofFn fun t ↦ single (a t) (b t) (1 : R) ⊗ₖ X t).prod =
      single (a 0) (b (Fin.last n)) 1 ⊗ₖ (List.ofFn X).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : b 0 = a (Fin.succ 0) := h 0
    -- Peel off the first block only, so that `ih` applies to the remaining chain.
    rw [List.ofFn_succ, List.prod_cons, ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)
      (fun i ↦ X i.succ) (fun i ↦ h i.succ)]
    simp [h0, single_one_kronecker_mul_single_one_kronecker, List.ofFn_succ]

end Matrix
