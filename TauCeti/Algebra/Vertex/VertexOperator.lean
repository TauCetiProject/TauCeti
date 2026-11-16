/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Vertex.VertexOperator
public import Mathlib.Data.Nat.Choose.Sum
public import TauCeti.RingTheory.HahnSeries.Multiplication
import Mathlib.Tactic.Module

/-!
# Extensionality and locality of vertex operators

A vertex operator `A(z) = ∑ₙ A₍ₙ₎ z^{-n-1}` on an `R`-module `V` (Mathlib's `VertexOperator R V`)
is determined by its normalized coefficients `A₍ₙ₎ = A[[n]]`
(`VertexOperator.ext_ncoeff`). The constant identity field `Id_V z⁰` is `VertexOperator.id R V`,
whose only nonzero normalized mode is `(VertexOperator.id R V)[[-1]] = 1`.

Two vertex operators `A` and `B` are *mutually local of order at most `N`* if

`(z - w)ᴺ [A(z), B(w)] = 0`

as a formal distribution in two variables. Expanding `(z - w)ᴺ` by the binomial theorem and taking
the coefficient of `z^{-m-1} w^{-n-1}`, this says that for all integers `m` and `n`

`∑_{i + j = N} (-1)ʲ (N choose i) [A₍ₘ₊ᵢ₎, B₍ₙ₊ⱼ₎] = 0`

in `Module.End R V` (`VertexOperator.IsLocalOfOrder`). This coefficientwise form needs no product
of formal distributions in two variables, which for `A(z) B(w)` and `B(w) A(z)` live in Hahn series
over the two opposite lexicographic orders on `ℤ × ℤ`. Locality is the defining property of the
fields of a vertex algebra and of its modules. Locality of order `N` implies locality of every
larger order (`VertexOperator.IsLocalOfOrder.mono`), it is symmetric in `A` and `B`
(`VertexOperator.IsLocalOfOrder.symm`), and the fields local to a given field form an `R`-submodule
containing `VertexOperator.id R V`.

## Main definitions

* `VertexOperator.id`: the identity vertex operator `Id_V z⁰`.
* `VertexOperator.IsLocalOfOrder`: mutual locality of order at most `N`.

## Main results

* `VertexOperator.ext_ncoeff`: vertex operators with the same normalized coefficients are equal.
* `VertexOperator.ncoeff_id`: the normalized modes of `VertexOperator.id` are `δ_{n,-1}`.
* `VertexOperator.IsLocalOfOrder.mono`, `VertexOperator.IsLocalOfOrder.symm`: locality is
  monotone in the order and symmetric.
* `VertexOperator.IsLocalOfOrder.id_left`, `id_right`, `zero_left`, `zero_right`, `add_left`,
  `add_right`, `smul_left`, `smul_right`: identity and linear closure of mutual locality.

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

/-- The identity field `Id_V z⁰`, whose `(-1)`-st normalized mode is `1` and all other modes are
`0`. -/
protected def id (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] : VertexOperator R V :=
  (HahnModule.ofLinearEquiv R).toLinearMap ∘ₗ HahnSeries.single.linearMap (0 : ℤ)

/-- Applying the identity field to `v` yields the constant Laurent series `v z⁰`. -/
@[simp] theorem id_apply (v : V) :
    VertexOperator.id R V v = HahnModule.of R (HahnSeries.single 0 v) := by
  simp [VertexOperator.id]; rfl

/-- The normalized modes of `VertexOperator.id` are `δ_{n,-1}`. -/
theorem ncoeff_id (n : ℤ) : (VertexOperator.id R V)[[n]] = if n = -1 then 1 else 0 := by
  ext v
  rw [ncoeff_apply, HVertexOperator.coeff_apply_apply, id_apply, Equiv.symm_apply_apply,
    HahnSeries.coeff_single]
  split_ifs <;> first | rfl | omega

/-- The `(-1)`-st normalized mode of the identity field is the identity endomorphism. -/
@[simp] theorem ncoeff_neg_one_id : (VertexOperator.id R V)[[-1]] = 1 := by simp [ncoeff_id]

/-- Every normalized mode of the identity field other than `-1` vanishes. -/
@[simp] theorem ncoeff_id_of_ne {n : ℤ} (hn : n ≠ -1) : (VertexOperator.id R V)[[n]] = 0 := by
  simp [ncoeff_id, hn]

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

/-- The identity field commutes with every field, hence is local of order `0`. -/
theorem id_left (B : VertexOperator R V) : (VertexOperator.id R V).IsLocalOfOrder B 0 :=
  isLocalOfOrder_iff.mpr fun m n ↦ by
    simp only [Nat.antidiagonal_zero, sum_singleton, Nat.choose_self, Nat.cast_zero, add_zero,
      pow_zero, one_smul, ncoeff_id]; split_ifs <;> simp

/-- Every field is local of order `0` with the identity field. -/
theorem id_right (A : VertexOperator R V) : A.IsLocalOfOrder (VertexOperator.id R V) 0 :=
  (id_left A).symm

/-- Zero is local of order `0` to every vertex operator. -/
theorem zero_left (C : VertexOperator R V) : (0 : VertexOperator R V).IsLocalOfOrder C 0 :=
  isLocalOfOrder_iff.mpr fun _ _ ↦ by simp

/-- Every vertex operator is local of order `0` to zero. -/
theorem zero_right (A : VertexOperator R V) : A.IsLocalOfOrder (0 : VertexOperator R V) 0 :=
  (zero_left A).symm

/-- Sums of vertex operators local to `C` are local to `C`. -/
theorem add_left {A₁ A₂ C : VertexOperator R V} {N₁ N₂ : ℕ}
    (h₁ : A₁.IsLocalOfOrder C N₁) (h₂ : A₂.IsLocalOfOrder C N₂) :
    (A₁ + A₂).IsLocalOfOrder C (max N₁ N₂) :=
  isLocalOfOrder_iff.mpr fun m n ↦ by
    simp_rw [map_add, Pi.add_apply, add_mul, mul_add, ← sub_add_sub_comm, smul_add]
    rw [sum_add_distrib, isLocalOfOrder_iff.mp (h₁.mono (le_max_left N₁ N₂)) m n,
      isLocalOfOrder_iff.mp (h₂.mono (le_max_right N₁ N₂)) m n, add_zero]

/-- A vertex operator local to `B₁` and `B₂` is local to `B₁ + B₂`. -/
theorem add_right {A B₁ B₂ : VertexOperator R V} {N₁ N₂ : ℕ}
    (h₁ : A.IsLocalOfOrder B₁ N₁) (h₂ : A.IsLocalOfOrder B₂ N₂) :
    A.IsLocalOfOrder (B₁ + B₂) (max N₁ N₂) :=
  (h₁.symm.add_left h₂.symm).symm

/-- Scalar multiples of a vertex operator local to `C` remain local to `C` of the same order. -/
theorem smul_left {A C : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder C N) (r : R) : (r • A).IsLocalOfOrder C N :=
  isLocalOfOrder_iff.mpr fun m n ↦ by
    simp_rw [map_smul, Pi.smul_apply, smul_mul_assoc, mul_smul_comm, ← smul_sub,
      smul_comm ((-1 : ℤ) ^ _) r, smul_comm (_ : ℕ) r]
    rw [← smul_sum, isLocalOfOrder_iff.mp h m n, smul_zero]

/-- A vertex operator local to `B` remains local to `r • B` of the same order. -/
theorem smul_right {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (r : R) : A.IsLocalOfOrder (r • B) N :=
  (h.symm.smul_left r).symm

end IsLocalOfOrder

end VertexOperator
