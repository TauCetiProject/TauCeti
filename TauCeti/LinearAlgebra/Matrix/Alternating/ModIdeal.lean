/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IdealEntries

/-!
# Matrices alternating modulo an ideal

A square matrix `N` over a commutative semiring is *alternating modulo an ideal* `I`
(`Matrix.IsAltMod`) when its diagonal entries and its symmetric sums `N i j + N j i` lie in `I`.
Then the quadratic expression `xᵀ N x` lies in `I` for every vector `x`
(`Matrix.IsAltMod.dotProduct_mulVec_mem`), and `Pᵀ N P` is again alternating modulo `I` for every
matrix `P`, square or not (`Matrix.IsAltMod.transpose_mul_mul`), since the quadratic expression of
`Pᵀ N P` at `x` is that of `N` at `P x` (`Matrix.dotProduct_transpose_mul_mul_mulVec`). Over a
commutative ring the converse holds (`Matrix.isAltMod_iff_forall_dotProduct_mulVec_mem`), and
modulo `⊥` it says exactly that the quadratic form `x ↦ xᵀ N x` vanishes
(`Matrix.isAltMod_bot_iff`).

This is the condition that cuts the orthogonal group scheme of a quadratic form out of `GLₙ` in
every characteristic: `g` preserves the form with coefficient matrix `M` exactly when
`gᵀ M g - M` is alternating, which is weaker than `gᵀ M g = M` when `M` is not symmetric.

## Main declarations

* `Matrix.IsAltMod`: alternating modulo an ideal, with `Matrix.isAltMod_iff`,
  `Matrix.IsAltMod.of_mem`, `Matrix.IsAltMod.diag_mem` and `Matrix.IsAltMod.add_transpose_mem`.
* `Matrix.IsAltMod.sum_mul_mul_mem` and `Matrix.IsAltMod.dotProduct_mulVec_mem`: the quadratic
  expression of such a matrix lies in the ideal.
* `Matrix.isAltMod_iff_forall_dotProduct_mulVec_mem`: the converse, over a commutative ring.
* `Matrix.dotProduct_transpose_mul_mul_mulVec`: the quadratic expression of a framed matrix.
* `Matrix.IsAltMod.transpose_mul_mul`: stability under framing `N ↦ Pᵀ N P`.
* `Matrix.IsAltMod.map`: stability under a ring morphism carrying the ideal into another.
* `Matrix.isAltMod_bot_iff`: alternating modulo `⊥` means the quadratic form vanishes.
-/

public section

open scoped Matrix

namespace Matrix

/-- The quadratic expression of a framed matrix `Pᵀ N P` at `x` is that of `N` at `P x`. -/
theorem dotProduct_transpose_mul_mul_mulVec {ι κ S : Type*} [CommSemiring S] [Fintype ι]
    [Fintype κ] (N : Matrix ι ι S) (P : Matrix ι κ S) (x : κ → S) :
    x ⬝ᵥ ((Pᵀ * N * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (N *ᵥ (P *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

variable {ι κ S : Type*}

section CommSemiring

variable [CommSemiring S]

/-- A square matrix is **alternating modulo an ideal** `I` when its diagonal entries and its
symmetric sums `N i j + N j i` lie in `I`. For finite `ι` over a commutative ring this says that
`xᵀ N x ∈ I` for every vector `x` (`Matrix.isAltMod_iff_forall_dotProduct_mulVec_mem`). -/
def IsAltMod (I : Ideal S) (N : Matrix ι ι S) : Prop :=
  (∀ i, N i i ∈ I) ∧ ∀ i j, N i j + N j i ∈ I

/-- Unfolding `Matrix.IsAltMod`: the diagonal entries and the symmetric sums lie in the ideal. -/
theorem isAltMod_iff {I : Ideal S} {N : Matrix ι ι S} :
    IsAltMod I N ↔ (∀ i, N i i ∈ I) ∧ ∀ i j, N i j + N j i ∈ I :=
  Iff.rfl

namespace IsAltMod

variable {I J : Ideal S} {N N' : Matrix ι ι S}

/-- A matrix whose diagonal entries and symmetric sums lie in `I` is alternating modulo `I`. -/
theorem of_mem (hdiag : ∀ i, N i i ∈ I) (hsum : ∀ i j, N i j + N j i ∈ I) : IsAltMod I N :=
  ⟨hdiag, hsum⟩

/-- The diagonal entries of a matrix alternating modulo `I` lie in `I`. -/
theorem diag_mem (hN : IsAltMod I N) (i : ι) : N i i ∈ I :=
  hN.1 i

/-- The symmetric sums `N i j + N j i` of a matrix alternating modulo `I` lie in `I`. -/
theorem add_transpose_mem (hN : IsAltMod I N) (i j : ι) : N i j + N j i ∈ I :=
  hN.2 i j

/-- The zero matrix is alternating modulo every ideal. -/
theorem zero : IsAltMod I (0 : Matrix ι ι S) :=
  of_mem (fun _ => by simp) fun _ _ => by simp

/-- The quadratic expression `Σᵢ Σⱼ aᵢ aⱼ Nᵢⱼ` of a matrix alternating modulo `I` lies in `I`. -/
theorem sum_mul_mul_mem [Fintype ι] (hN : IsAltMod I N) (a : ι → S) :
    ∑ i, ∑ j, a i * a j * N i j ∈ I := by
  classical
  suffices h : ∀ s : Finset ι, ∑ i ∈ s, ∑ j ∈ s, a i * a j * N i j ∈ I from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    -- Split off the row and the column of the new index `k`.
    have hsplit : ∑ i ∈ insert k s, ∑ j ∈ insert k s, a i * a j * N i j =
        a k * a k * N k k + ∑ j ∈ s, a k * a j * (N k j + N j k) +
          ∑ i ∈ s, ∑ j ∈ s, a i * a j * N i j := by
      simp only [Finset.sum_insert hk, Finset.sum_add_distrib, mul_add]
      have hcol : ∑ i ∈ s, a i * a k * N i k = ∑ j ∈ s, a k * a j * N j k :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [hcol]
      ring
    rw [hsplit]
    exact add_mem (add_mem (I.mul_mem_left _ (hN.diag_mem k))
      (Ideal.sum_mem _ fun j _ => I.mul_mem_left _ (hN.add_transpose_mem k j))) ih

/-- The quadratic expression `xᵀ N x` of a matrix alternating modulo `I` lies in `I`. -/
theorem dotProduct_mulVec_mem [Fintype ι] (hN : IsAltMod I N) (x : ι → S) :
    x ⬝ᵥ (N *ᵥ x) ∈ I := by
  have hform : x ⬝ᵥ (N *ᵥ x) = ∑ i, ∑ j, x i * x j * N i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  exact hform ▸ hN.sum_mul_mul_mem x

/-- A matrix alternating modulo `I` stays so when framed by any matrix, square or not:
`Pᵀ N P`. -/
theorem transpose_mul_mul [Fintype ι] (hN : IsAltMod I N) (P : Matrix ι κ S) :
    IsAltMod I (Pᵀ * N * P) := by
  refine of_mem (fun k => ?_) fun k l => ?_
  · -- The diagonal entry at `k` is the quadratic expression at the `k`-th column of `P`.
    convert hN.dotProduct_mulVec_mem (P.col k) using 1
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
      Matrix.col_apply]
  · have hsum : (Pᵀ * N * P) k l + (Pᵀ * N * P) l k = (Pᵀ * (N + Nᵀ) * P) k l := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      congr 1
      rw [← Matrix.transpose_apply (Pᵀ * N * P) k l, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [hsum]
    exact Matrix.mul_mul_apply_mem (fun i j => hN.add_transpose_mem i j) _ _ k l

/-- The sum of two matrices alternating modulo `I` is alternating modulo `I`. -/
theorem add (hN : IsAltMod I N) (hN' : IsAltMod I N') : IsAltMod I (N + N') :=
  of_mem (fun i => by simpa using add_mem (hN.diag_mem i) (hN'.diag_mem i))
    fun i j => by
      rw [Matrix.add_apply, Matrix.add_apply, add_add_add_comm]
      exact add_mem (hN.add_transpose_mem i j) (hN'.add_transpose_mem i j)

/-- A multiple `c • N` of a matrix alternating modulo `I` is alternating modulo `I`. -/
theorem smul (hN : IsAltMod I N) (c : S) : IsAltMod I (c • N) :=
  of_mem (fun i => by simpa using I.mul_mem_left c (hN.diag_mem i))
    fun i j => by
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_add]
      exact I.mul_mem_left c (hN.add_transpose_mem i j)

/-- Being alternating modulo an ideal is inherited by every larger ideal. -/
theorem mono (hIJ : I ≤ J) (hN : IsAltMod I N) : IsAltMod J N :=
  of_mem (fun i => hIJ (hN.diag_mem i)) fun i j => hIJ (hN.add_transpose_mem i j)

/-- A ring morphism carrying `I` into `J` carries matrices alternating modulo `I` to matrices
alternating modulo `J`. -/
theorem map {T F : Type*} [CommSemiring T] [FunLike F S T] [RingHomClass F S T] {J : Ideal T}
    (hN : IsAltMod I N) (f : F) (hIJ : I.map f ≤ J) : IsAltMod J (N.map f) :=
  of_mem (fun i => hIJ (Ideal.mem_map_of_mem f (hN.diag_mem i)))
    fun i j => by
      rw [Matrix.map_apply, Matrix.map_apply, ← map_add]
      exact hIJ (Ideal.mem_map_of_mem f (hN.add_transpose_mem i j))

end IsAltMod

end CommSemiring

section CommRing

variable [CommRing S]

/-- The negative of a matrix alternating modulo `I` is alternating modulo `I`. -/
theorem IsAltMod.neg {I : Ideal S} {N : Matrix ι ι S} (hN : IsAltMod I N) : IsAltMod I (-N) :=
  IsAltMod.of_mem (fun i => by simpa using neg_mem (hN.diag_mem i))
    fun i j => by
      rw [Matrix.neg_apply, Matrix.neg_apply, ← neg_add]
      exact neg_mem (hN.add_transpose_mem i j)

/-- A matrix is alternating modulo `I` exactly when its quadratic expression `xᵀ N x` lies in `I`
for every vector `x`. -/
theorem isAltMod_iff_forall_dotProduct_mulVec_mem [Fintype ι] {I : Ideal S}
    (N : Matrix ι ι S) : IsAltMod I N ↔ ∀ x : ι → S, x ⬝ᵥ (N *ᵥ x) ∈ I := by
  classical
  have hsingle (i j : ι) : (Pi.single i 1 : ι → S) ⬝ᵥ (N *ᵥ Pi.single j 1) = N i j := by
    simp
  refine ⟨fun h x => h.dotProduct_mulVec_mem x, fun h => IsAltMod.of_mem
    (fun i => hsingle i i ▸ h _) fun i j => ?_⟩
  -- Test on `eᵢ + eⱼ` and cancel the two diagonal terms.
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, hsingle] at hij
  have hsum : N i j + N j i = (N i i + N j i + (N i j + N j j)) - N i i - N j j := by ring
  rw [hsum]
  exact sub_mem (sub_mem hij (hsingle i i ▸ h _)) (hsingle j j ▸ h _)

/-- A matrix is alternating modulo `⊥` exactly when its quadratic form `x ↦ xᵀ N x` vanishes. -/
theorem isAltMod_bot_iff [Fintype ι] (N : Matrix ι ι S) :
    IsAltMod ⊥ N ↔ ∀ x : ι → S, x ⬝ᵥ (N *ᵥ x) = 0 := by
  simp only [isAltMod_iff_forall_dotProduct_mulVec_mem, Ideal.mem_bot]

end CommRing

end Matrix
