/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Matrices equal to the negative of their transpose

A matrix satisfying `Mᵀ = -M` is determined by its entries above the diagonal, once its diagonal
is known to vanish: the entries below are the negatives of their mirror images. The diagonal does
vanish as soon as the value ring has no element that is its own negative apart from zero, which
covers every ring of odd characteristic.

## Main results

* `Matrix.transpose_single_sub_single`: transposing the difference of two opposite singleton
  matrices with the same coefficient negates it.
* `Matrix.transpose_map_of_transpose_eq_neg`: the condition passes to the image of the matrix
  under an additive morphism of the entry types.
* `Matrix.diag_eq_zero_of_transpose_eq_neg`: the diagonal vanishes when doubling is injective at
  zero, with `Matrix.diag_eq_zero_of_transpose_eq_neg_of_charP` reading that off an odd
  characteristic.
* `Matrix.trace_eq_zero_of_transpose_eq_neg`: the trace vanishes when `2` is invertible.
* `Matrix.ext_of_lt_of_transpose_eq_neg`: two such matrices with vanishing diagonals agree as soon
  as they agree above the diagonal.
* `Matrix.natCard_transpose_eq_neg`: when doubling is injective at zero, the `Nat.card` of such
  matrices with entries in an additive subgroup `I` is `(Nat.card I) ^ (k.choose 2)`, for an
  index type of cardinality `k`; for finite `I` this is the number of such matrices.
-/

public section

namespace Matrix

variable {n : Type*} {S T : Type*}

/-- Transposing the difference of two opposite singleton matrices with the same coefficient
negates it. -/
theorem transpose_single_sub_single {K ι : Type*} [AddGroup K] [DecidableEq ι]
    (i j : ι) (a : K) :
    (single i j a - single j i a).transpose = -(single i j a - single j i a) := by
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

/-- A skew-symmetric matrix has trace zero when `2` is invertible. -/
theorem trace_eq_zero_of_transpose_eq_neg {R : Type*} [Fintype n] [Ring R]
    [Invertible (2 : R)] (X : Matrix n n R) (hX : Xᵀ = -X) : trace X = 0 := by
  have h2 : ∀ x : R, x + x = 0 → x = 0 := by
    intro x hx
    calc
      x = ⅟(2 : R) * ((2 : R) * x) := by simp
      _ = 0 := by rw [two_mul, hx, mul_zero]
  exact Finset.sum_eq_zero fun a _ => diag_eq_zero_of_transpose_eq_neg hX h2 a

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

/-- **Counting matrices equal to the negative of their transpose with entries in a subgroup.**
When zero is the only element that doubles to zero, such a matrix is determined by its entries
above the diagonal, and these are arbitrary elements of the subgroup; for an index type of
cardinality `k` there are `k.choose 2` of them. As an identity of `Nat.card`s this holds for
every subgroup; when the subgroup is finite it counts the matrices. -/
theorem natCard_transpose_eq_neg [Fintype n] [AddCommGroup S] (I : AddSubgroup S)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    Nat.card {M : Matrix n n S // (∀ i j, M i j ∈ I) ∧ Mᵀ = -M} =
      Nat.card I ^ (Fintype.card n).choose 2 := by
  classical
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  have hpairs : Nat.card {q : n × n // q.1 < q.2} = (Fintype.card n).choose 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt]
  have hskew : ∀ M : Matrix n n S, Mᵀ = -M → ∀ i j, M j i = -M i j := fun M hM i j => by
    simpa only [transpose_apply, neg_apply] using congrFun (congrFun hM i) j
  rw [← hpairs, ← Nat.card_fun]
  refine Nat.card_congr
    { toFun := fun M q => ⟨M.1 q.1.1 q.1.2, M.2.1 _ _⟩
      invFun := fun g => ⟨of fun i j => if h : i < j then (g ⟨(i, j), h⟩ : S)
          else if h' : j < i then -(g ⟨(j, i), h'⟩ : S) else 0, fun i j => ?_, ?_⟩
      left_inv := fun M => Subtype.ext ?_
      right_inv := fun g => funext fun q => Subtype.ext ?_ }
  · rw [of_apply]
    split_ifs
    exacts [(g _).2, I.neg_mem (g _).2, I.zero_mem]
  · ext i j
    simp only [transpose_apply, neg_apply, of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp
    · simp [h, h.not_gt]
  · ext i j
    simp only [of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp [diag_eq_zero_of_transpose_eq_neg M.2.2 h2 i]
    · simp [h, h.not_gt, hskew M.1 M.2.2 j i]
  · simp [q.2]

end Matrix
