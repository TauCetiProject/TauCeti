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

* `VertexOperator.idField`: the identity field `id_V · z⁰`, with modes `(idField)₍ₙ₎ = δ_{n,-1}`.
* `VertexOperator.IsLocalOfOrder`: mutual locality of order at most `N`.

## Main results

* `VertexOperator.ext_ncoeff`: vertex operators with the same normalized coefficients are equal.
* `VertexOperator.IsLocalOfOrder.mono`, `VertexOperator.IsLocalOfOrder.symm`,
  `VertexOperator.IsLocalOfOrder.add_left`, `VertexOperator.IsLocalOfOrder.smul_left`: locality is
  monotone in the order, symmetric, and `R`-linear in each field.
* `VertexOperator.isLocalOfOrder_idField_left`, `VertexOperator.isLocalOfOrder_idField_right`: the
  identity field is mutually local of order `0` with every field.

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

/-- The identity field `id_V · z⁰`, whose `(-1)`-mode is `1 : Module.End R V` and whose other
normalized modes vanish. -/
def idField : VertexOperator R V :=
  of_coeff (fun m ↦ if m = 0 then 1 else 0) fun _ ↦
    ⟨0, fun m hm ↦ not_lt.mp fun h ↦ hm (by simp [h.ne])⟩

/-- The normalized modes of `idField` are `(idField)₍ₙ₎ = δ_{n,-1}`. -/
theorem ncoeff_idField (n : ℤ) :
    (idField : VertexOperator R V)[[n]] = if n = -1 then 1 else 0 := by
  refine (ncoeff_of_coeff _ _ n).trans ?_
  congr 1
  exact propext ⟨fun h ↦ by omega, fun h ↦ by omega⟩

/-- The `(-1)`-mode of `idField` is the identity endomorphism. -/
@[simp]
theorem ncoeff_neg_one_idField : (idField : VertexOperator R V)[[-1]] = 1 := by
  simp [ncoeff_idField]

/-- All normalized modes of `idField` other than `-1` vanish. -/
@[simp]
theorem ncoeff_idField_of_ne {n : ℤ} (hn : n ≠ -1) :
    (idField : VertexOperator R V)[[n]] = 0 := by
  simp [ncoeff_idField, hn]

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

/-- Zero is local of every order with any field on the right. -/
@[simp]
theorem isLocalOfOrder_zero_left (B : VertexOperator R V) (N : ℕ) :
    (0 : VertexOperator R V).IsLocalOfOrder B N := fun _ _ ↦ by simp

/-- Zero is local of every order with any field on the left. -/
@[simp]
theorem isLocalOfOrder_zero_right (A : VertexOperator R V) (N : ℕ) :
    A.IsLocalOfOrder 0 N := fun _ _ ↦ by simp

namespace IsLocalOfOrder

variable {A A₁ A₂ B B₁ B₂ : VertexOperator R V} {N : ℕ}

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

/-- Locality of order `N` is closed under addition in the first field. -/
theorem add_left (h₁ : A₁.IsLocalOfOrder B N) (h₂ : A₂.IsLocalOfOrder B N) :
    (A₁ + A₂).IsLocalOfOrder B N := fun m n ↦ by
  have e : ∀ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
      ((A₁ + A₂)[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * (A₁ + A₂)[[m + ij.1]]) =
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A₁[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A₁[[m + ij.1]]) +
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A₂[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A₂[[m + ij.1]]) := fun ij _ ↦ by
    simp only [map_add, Pi.add_apply, add_mul, mul_add]
    module
  rw [sum_congr rfl e, sum_add_distrib, h₁ m n, h₂ m n, add_zero]

/-- Locality of order `N` is closed under addition in the second field. -/
theorem add_right (h₁ : A.IsLocalOfOrder B₁ N) (h₂ : A.IsLocalOfOrder B₂ N) :
    A.IsLocalOfOrder (B₁ + B₂) N :=
  (h₁.symm.add_left h₂.symm).symm

/-- Locality of order `N` is closed under `R`-scalar multiplication in the first field. -/
theorem smul_left (h : A.IsLocalOfOrder B N) (r : R) :
    (r • A).IsLocalOfOrder B N := fun m n ↦ by
  have e : ∀ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
      ((r • A)[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * (r • A)[[m + ij.1]]) =
      r • (N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A[[m + ij.1]])) := fun ij _ ↦ by
    simp only [map_smul, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]
    module
  rw [sum_congr rfl e, ← smul_sum, h m n, smul_zero]

/-- Locality of order `N` is closed under `R`-scalar multiplication in the second field. -/
theorem smul_right (h : A.IsLocalOfOrder B N) (r : R) :
    A.IsLocalOfOrder (r • B) N :=
  (h.symm.smul_left r).symm

end IsLocalOfOrder

/-- The identity field is local of order `N` with any field on the right. -/
@[simp]
theorem isLocalOfOrder_idField_left (B : VertexOperator R V) (N : ℕ) :
    (idField : VertexOperator R V).IsLocalOfOrder B N :=
  IsLocalOfOrder.mono (N := 0) (fun _ _ ↦ by simp [ncoeff_idField]) (Nat.zero_le N)

/-- The identity field is local of order `N` with any field on the left. -/
@[simp]
theorem isLocalOfOrder_idField_right (A : VertexOperator R V) (N : ℕ) :
    A.IsLocalOfOrder idField N :=
  (isLocalOfOrder_idField_left A N).symm

end VertexOperator
