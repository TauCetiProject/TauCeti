/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Vertex.VertexOperator
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Module

/-!
# Extensionality and locality of vertex operators

A vertex operator `A(z) = ∑ₙ A₍ₙ₎ z^{-n-1}` on an `R`-module `V` (Mathlib's `VertexOperator R V`)
is determined by its normalized coefficients `A₍ₙ₎ = A[[n]]`
(`VertexOperator.ext_ncoeff`).

Two vertex operators `A` and `B` are *mutually local of order at most `N`* if

`(z - w)ᴺ [A(z), B(w)] = 0`

as a formal distribution in two variables. Expanding `(z - w)ᴺ` by the binomial theorem and taking
the coefficient of `z^{-m-1} w^{-n-1}`, this says that for all integers `m` and `n`

`∑_{i + j = N} (-1)ʲ (N choose i) [A₍ₘ₊ᵢ₎, B₍ₙ₊ⱼ₎] = 0`

in `Module.End R V` (`VertexOperator.IsLocalOfOrder`). This coefficientwise form needs no product
of formal distributions in two variables, which for `A(z) B(w)` and `B(w) A(z)` live in Hahn series
over the two opposite lexicographic orders on `ℤ × ℤ`. Locality is the defining property of the
fields of a vertex algebra and of its modules. Locality of order `N` implies locality of every
larger order (`VertexOperator.IsLocalOfOrder.mono`), and it is symmetric in `A` and `B`
(`VertexOperator.IsLocalOfOrder.symm`).

## Main definitions

* `VertexOperator.IsLocalOfOrder`: mutual locality of order at most `N`.

## Main results

* `VertexOperator.ext_ncoeff`: vertex operators with the same normalized coefficients are equal.
* `VertexOperator.IsLocalOfOrder.mono`, `VertexOperator.IsLocalOfOrder.symm`: locality is
  monotone in the order and symmetric.
* `VertexOperator.IsLocalOfOrder.zero_left`, `VertexOperator.IsLocalOfOrder.add_left`,
  `VertexOperator.IsLocalOfOrder.smul_left` (and right/neg/sub variants): mutual locality is
  closed under `R`-linear combinations in either argument.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §2.3, for formal distributions and
  locality.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2.
* S. Carnahan, leanprover-community/mathlib4#25822, a prospective Mathlib development of vertex
  algebras, whose order-bounded locality predicate `IsLocalToOrderLeq`, stated through
  compositions of two-variable Hahn series, is mirrored coefficientwise by
  `VertexOperator.IsLocalOfOrder`.
-/

public section

noncomputable section

open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Extensionality.** Vertex operators with the same normalized coefficients are equal. -/
theorem ext_ncoeff {A B : VertexOperator R V} (h : ∀ n : ℤ, A[[n]] = B[[n]]) : A = B := by
  refine HVertexOperator.coeff_inj (funext fun n ↦ ?_)
  rw [coeff_eq_ncoeff, coeff_eq_ncoeff, h]

/-- Vertex operators are equal exactly when their normalized coefficients are. -/
theorem ext_ncoeff_iff {A B : VertexOperator R V} : A = B ↔ ∀ n : ℤ, A[[n]] = B[[n]] :=
  ⟨fun h _ ↦ h ▸ rfl, ext_ncoeff⟩

/-- Every vector is killed by all sufficiently high normalized coefficients of a field. -/
theorem exists_forall_ncoeff_apply_eq_zero (A : VertexOperator R V) (v : V) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → (A[[n]]) v = 0 := by
  refine ⟨(-((HahnModule.of R).symm (A v)).order + 1).toNat, fun n hn ↦ ?_⟩
  apply ncoeff_eq_zero_of_lt_order
  omega

/-- `A` and `B` are **mutually local of order at most `N`**: `(z - w)ᴺ [A(z), B(w)] = 0`. In
normalized coefficients, for all integers `m` and `n`,
`∑_{i + j = N} (-1)ʲ (N choose i) [A₍ₘ₊ᵢ₎, B₍ₙ₊ⱼ₎] = 0`. -/
def IsLocalOfOrder (A B : VertexOperator R V) (N : ℕ) : Prop :=
  ∀ m n : ℤ, ∑ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
    (A[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A[[m + ij.1]]) = 0

/-- Unfolding mutual locality of order at most `N` into normalized coefficients. -/
theorem isLocalOfOrder_iff {A B : VertexOperator R V} {N : ℕ} :
    A.IsLocalOfOrder B N ↔ ∀ m n : ℤ, ∑ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
      (A[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A[[m + ij.1]]) = 0 :=
  Iff.rfl

namespace IsLocalOfOrder

variable {A B : VertexOperator R V} {N : ℕ}

/-- Locality of order `N` implies locality of order `N + 1`: the sum for `N + 1` at `(m, n)` is
the sum for `N` at `(m + 1, n)` minus the sum for `N` at `(m, n + 1)`. -/
theorem succ (h : A.IsLocalOfOrder B N) : A.IsLocalOfOrder B (N + 1) := by
  intro m n
  rw [sum_antidiagonal_choose_succ_nsmul
    (fun i j ↦ (-1 : ℤ) ^ j • (A[[m + i]] * B[[n + j]] - B[[n + j]] * A[[m + i]])) N]
  have h₁ := h m (n + 1)
  have h₂ := h (m + 1) n
  -- Rewrite each rank-`N + 1` sum as a rank-`N` sum at shifted indices.
  have e₁ : ∀ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ (ij.2 + 1) •
      (A[[m + ij.1]] * B[[n + ↑(ij.2 + 1)]] - B[[n + ↑(ij.2 + 1)]] * A[[m + ij.1]]) =
      -(N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[m + ij.1]] * B[[n + 1 + ij.2]] - B[[n + 1 + ij.2]] * A[[m + ij.1]])) := by
    intro ij _
    rw [show n + ↑(ij.2 + 1) = n + 1 + ij.2 by push_cast; ring, pow_succ]
    module
  have e₂ : ∀ ij ∈ antidiagonal N, N.choose ij.2 • (-1 : ℤ) ^ ij.2 •
      (A[[m + ↑(ij.1 + 1)]] * B[[n + ij.2]] - B[[n + ij.2]] * A[[m + ↑(ij.1 + 1)]]) =
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[m + 1 + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A[[m + 1 + ij.1]]) := by
    intro ij hij
    rw [Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm,
      show m + ↑(ij.1 + 1) = m + 1 + ij.1 by push_cast; ring]
  rw [sum_congr rfl e₁, sum_congr rfl e₂, sum_neg_distrib, h₁, h₂, neg_zero, add_zero]

/-- Locality is monotone in the order. -/
theorem mono (h : A.IsLocalOfOrder B N) {N' : ℕ} (hN : N ≤ N') : A.IsLocalOfOrder B N' := by
  induction hN with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- Locality is symmetric: if `A` is local to `B` of order `N`, then `B` is local to `A` of the
same order. -/
theorem symm (h : A.IsLocalOfOrder B N) : B.IsLocalOfOrder A N := by
  intro n m
  rw [← Nat.sum_antidiagonal_swap]
  have e : ∀ ij ∈ antidiagonal N, N.choose ij.swap.1 • (-1 : ℤ) ^ ij.swap.2 •
      (B[[n + ij.swap.1]] * A[[m + ij.swap.2]] - A[[m + ij.swap.2]] * B[[n + ij.swap.1]]) =
      (-(-1 : ℤ) ^ N) • (N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A[[m + ij.1]])) := by
    intro ij hij
    have hN : (-1 : ℤ) ^ ij.1 = (-1) ^ N * (-1) ^ ij.2 := by
      rw [← mem_antidiagonal.1 hij]
      simp [pow_add, mul_assoc, ← mul_pow]
    rw [Prod.fst_swap, Prod.snd_swap, Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm, hN]
    module
  rw [sum_congr rfl e, ← smul_sum, h m n, smul_zero]

/-- The zero vertex operator is local of every order with any field on the right. -/
theorem zero_left (B : VertexOperator R V) (N : ℕ) :
    (0 : VertexOperator R V).IsLocalOfOrder B N :=
  isLocalOfOrder_iff.2 fun _ _ ↦ sum_eq_zero fun _ _ ↦ by simp

/-- Any field is local of every order with the zero vertex operator on the right. -/
theorem zero_right (A : VertexOperator R V) (N : ℕ) :
    A.IsLocalOfOrder (0 : VertexOperator R V) N :=
  (zero_left A N).symm

/-- Sums of fields local with `B` are local with `B` of order `max N₁ N₂`. -/
theorem add_left {A₁ A₂ B : VertexOperator R V} {N₁ N₂ : ℕ}
    (h₁ : A₁.IsLocalOfOrder B N₁) (h₂ : A₂.IsLocalOfOrder B N₂) :
    (A₁ + A₂).IsLocalOfOrder B (max N₁ N₂) := by
  have h₁' := isLocalOfOrder_iff.1 (h₁.mono (le_max_left N₁ N₂))
  have h₂' := isLocalOfOrder_iff.1 (h₂.mono (le_max_right N₁ N₂))
  refine isLocalOfOrder_iff.2 fun m n ↦ ?_
  have hsplit (ij : ℕ × ℕ) :
      ((A₁ + A₂)[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * (A₁ + A₂)[[m + ij.1]]) =
        (A₁[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A₁[[m + ij.1]]) +
          (A₂[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A₂[[m + ij.1]]) := by
    rw [map_add, Pi.add_apply, add_mul, mul_add]
    abel
  simp only [hsplit, smul_add, sum_add_distrib, h₁' m n, h₂' m n, add_zero]

/-- Locality with `A` on the left is preserved by addition on the right. -/
theorem add_right {A B₁ B₂ : VertexOperator R V} {N₁ N₂ : ℕ}
    (h₁ : A.IsLocalOfOrder B₁ N₁) (h₂ : A.IsLocalOfOrder B₂ N₂) :
    A.IsLocalOfOrder (B₁ + B₂) (max N₁ N₂) :=
  (h₁.symm.add_left h₂.symm).symm

/-- Scalar multiples of a field local with `B` remain local with `B` of the same order. -/
theorem smul_left (r : R) (h : A.IsLocalOfOrder B N) : (r • A).IsLocalOfOrder B N := by
  refine isLocalOfOrder_iff.2 fun m n ↦ ?_
  have h' := congrArg (r • ·) (isLocalOfOrder_iff.1 h m n)
  rw [smul_zero, smul_sum] at h'
  rw [← h']
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [map_smul, Pi.smul_apply, smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_comm r,
    smul_comm r ((-1 : ℤ) ^ ij.2)]

/-- Locality with `A` on the left is preserved by scalar multiplication on the right. -/
theorem smul_right (r : R) (h : A.IsLocalOfOrder B N) : A.IsLocalOfOrder (r • B) N :=
  (h.symm.smul_left r).symm

/-- Negating the left field preserves mutual locality of order `N`. -/
theorem neg_left (h : A.IsLocalOfOrder B N) : (-A).IsLocalOfOrder B N := by
  rw [← neg_one_smul R A]
  exact h.smul_left (-1)

/-- Negating the right field preserves mutual locality of order `N`. -/
theorem neg_right (h : A.IsLocalOfOrder B N) : A.IsLocalOfOrder (-B) N :=
  h.symm.neg_left.symm

/-- Differences of fields local with `B` are local with `B` of order `max N₁ N₂`. -/
theorem sub_left {A₁ A₂ B : VertexOperator R V} {N₁ N₂ : ℕ}
    (h₁ : A₁.IsLocalOfOrder B N₁) (h₂ : A₂.IsLocalOfOrder B N₂) :
    (A₁ - A₂).IsLocalOfOrder B (max N₁ N₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add_left h₂.neg_left

/-- Locality with `A` on the left is preserved by subtraction on the right. -/
theorem sub_right {A B₁ B₂ : VertexOperator R V} {N₁ N₂ : ℕ}
    (h₁ : A.IsLocalOfOrder B₁ N₁) (h₂ : A.IsLocalOfOrder B₂ N₂) :
    A.IsLocalOfOrder (B₁ - B₂) (max N₁ N₂) :=
  (h₁.symm.sub_left h₂.symm).symm

end IsLocalOfOrder

end VertexOperator
