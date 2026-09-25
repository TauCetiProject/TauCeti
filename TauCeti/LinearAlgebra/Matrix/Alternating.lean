/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs

/-!
# Matrices equal to the negative of their transpose

A matrix satisfying `Mᵀ = -M` is determined by its entries above the diagonal, once its diagonal
is known to vanish: the entries below are the negatives of their mirror images. The diagonal does
vanish as soon as the value ring has no element that is its own negative apart from zero, which
covers every ring of odd characteristic.

## Main results

* `Matrix.transpose_single_sub_single`: transposing the difference of two opposite matrix units
  negates it.
* `Matrix.transpose_map_of_transpose_eq_neg`: the condition passes to the image of the matrix
  under an additive morphism of the entry types.
* `Matrix.diag_eq_zero_of_transpose_eq_neg`: the diagonal vanishes when doubling is injective at
  zero, with `Matrix.diag_eq_zero_of_transpose_eq_neg_of_charP` reading that off an odd
  characteristic.
* `Matrix.ext_of_lt_of_transpose_eq_neg`: two such matrices with vanishing diagonals agree as soon
  as they agree above the diagonal.
-/

public section

namespace Matrix

variable {n : Type*} {S T : Type*}

/-- Transposing the difference of two opposite matrix units negates it. -/
theorem transpose_single_sub_single {K ι : Type*} [AddGroupWithOne K] [DecidableEq ι]
    (i j : ι) :
    (single i j (1 : K) - single j i 1).transpose =
      -(single i j 1 - single j i 1) := by
  simp only [transpose_sub, transpose_single, neg_sub]

/-- **The condition `Mᵀ = -M` passes to the image of the matrix** under an additive morphism of
the entry types. -/
theorem transpose_map_of_transpose_eq_neg [AddGroup S] [SubtractionMonoid T] {F : Type*}
    [FunLike F S T] [AddMonoidHomClass F S T] (f : F) {M : Matrix n n S} (hM : Mᵀ = -M) :
    (M.map f)ᵀ = -M.map f := by
  ext a b
  have h := congrFun (congrFun hM a) b
  rw [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, Matrix.map_apply, h, map_neg]

/-- **The diagonal of a matrix equal to the negative of its transpose vanishes**, as soon as zero
is the only entry that doubles to zero. -/
theorem diag_eq_zero_of_transpose_eq_neg [AddGroup S] {M : Matrix n n S} (hM : Mᵀ = -M)
    (h2 : ∀ x : S, x + x = 0 → x = 0) (a : n) : M a a = 0 := by
  refine h2 _ ?_
  have h := congrFun (congrFun hM a) a
  rw [Matrix.transpose_apply, Matrix.neg_apply] at h
  nth_rewrite 1 [h]
  rw [neg_add_cancel]

/-- **In a ring of odd characteristic the diagonal of a matrix equal to the negative of its
transpose vanishes**: odd characteristic implies that doubling is injective at zero, which
is what the diagonal entries need. -/
theorem diag_eq_zero_of_transpose_eq_neg_of_charP [Ring S] (p : ℕ) [CharP S p] (hp : Odd p)
    {M : Matrix n n S} (hM : Mᵀ = -M) (a : n) : M a a = 0 := by
  obtain ⟨k, hk⟩ := hp
  refine diag_eq_zero_of_transpose_eq_neg hM (fun x hx => ?_) a
  have hpz : ((2 * k + 1 : ℕ) : S) = 0 := by rw [← hk]; exact CharP.cast_eq_zero S p
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hpz
  have hx2 : (2 : S) * x = 0 := by rw [two_mul]; exact hx
  have key : ((2 : S) * (k : S) + 1) * x - (k : S) * ((2 : S) * x) = x := by
    rw [add_mul, one_mul, ← mul_assoc, (Nat.cast_commute k 2).eq, add_sub_cancel_left]
  rw [← key, hpz, hx2, zero_mul, mul_zero, sub_zero]

/-- **Two matrices equal to the negatives of their transposes agree as soon as they agree above
the diagonal**, provided both diagonals vanish: the entries below the diagonal are the negatives
of their mirror images. -/
theorem ext_of_lt_of_transpose_eq_neg [LinearOrder n] [Zero S] [Neg S] {M N : Matrix n n S}
    (hM : Mᵀ = -M) (hN : Nᵀ = -N) (hMd : ∀ a, M a a = 0) (hNd : ∀ a, N a a = 0)
    (h : ∀ a b : n, a < b → M a b = N a b) : M = N := by
  have hskew : ∀ K : Matrix n n S, Kᵀ = -K → ∀ a b, K b a = -K a b := by
    intro K hK a b
    have hab := congrFun (congrFun hK a) b
    rw [Matrix.transpose_apply, Matrix.neg_apply] at hab
    exact hab
  ext a b
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact h a b hab
  · rw [hMd a, hNd a]
  · rw [hskew M hM b a, hskew N hN b a, h b a hab]

end Matrix
