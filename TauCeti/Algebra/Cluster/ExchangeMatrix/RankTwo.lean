/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.CartanCompanion
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Word.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
public import TauCeti.SetTheory.Cardinal.Finite

import Mathlib.Data.Set.Finite.Basic

/-!
# Mutation classes with at most two indices

Mutation of a skew-symmetrizable matrix on at most two indices negates it. A word acts
by the sign `(-1)^length` and its full mutation class is `{B, -B}`. For arbitrary integer
matrices on at most two indices, the Cartan companion and every off-diagonal product
`bᵢⱼ bⱼᵢ` are still invariant. This includes empty and singleton index types.
Any uniform off-diagonal bound `|b'ᵢⱼ b'ⱼᵢ| ≤ bound` over the mutation class is equivalent
to the same bound on `|bᵢⱼ bⱼᵢ|` at the initial matrix. In particular, the Fomin–Zelevinsky
two-finiteness condition uses `bound = 3`.
These statements concern matrix mutation classes, not finiteness of cluster variables:
skew-symmetrizable matrices with off-diagonal entry product of absolute value at least four
also have finite matrix mutation classes on two indices.

For a skew-symmetrizable matrix on at most two indices, the Cartan companion is of finite
type exactly when the absolute off-diagonal products are at most three. Consequently some
companion in the mutation class is of finite type exactly when the whole class satisfies
that product bound.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), §1, Theorem 1.8 and the rank-two discussion.
-/

public section

open Matrix

namespace TauCeti

variable {K : Type*} [DecidableEq K] [Finite K]

/-- On at most two indices, mutation negates every off-diagonal entry of any matrix. -/
theorem matrixMutation_refl_apply_of_card_le_two_of_ne (hK : Nat.card K ≤ 2)
    (B : Matrix K K ℤ) (k : K) {i j : K} (hij : i ≠ j) :
    matrixMutation (Function.Embedding.refl K) B k i j = -B i j := by
  rcases Finite.eq_or_eq_of_card_le_two hK hij k with rfl | rfl <;>
    simp [matrixMutation_apply]

/-- A single mutation preserves the companion of any matrix on at most two indices. -/
theorem cartanCompanion_matrixMutation_of_card_le_two (hK : Nat.card K ≤ 2)
    (B : Matrix K K ℤ) (k : K) :
    (matrixMutation (Function.Embedding.refl K) B k).cartanCompanion = B.cartanCompanion := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, matrixMutation_refl_apply_of_card_le_two_of_ne hK B k hij]

/-- Every mutation word preserves the companion of any matrix on at most two indices. -/
theorem cartanCompanion_foldl_matrixMutation_of_card_le_two (hK : Nat.card K ≤ 2)
    (B : Matrix K K ℤ) (w : List K) :
    (w.foldl (matrixMutation (Function.Embedding.refl K)) B).cartanCompanion =
      B.cartanCompanion := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    rw [List.foldl_cons, ih, cartanCompanion_matrixMutation_of_card_le_two hK B k]

/-- Every mutation word preserves each off-diagonal product of transposed entries of any
matrix on at most two indices. -/
theorem foldl_matrixMutation_apply_mul_apply_of_card_le_two_of_ne (hK : Nat.card K ≤ 2)
    (B : Matrix K K ℤ) (w : List K) {i j : K} (hij : i ≠ j) :
    w.foldl (matrixMutation (Function.Embedding.refl K)) B i j *
      w.foldl (matrixMutation (Function.Embedding.refl K)) B j i = B i j * B j i := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    rw [List.foldl_cons, ih, matrixMutation_refl_apply_of_card_le_two_of_ne hK B k hij,
      matrixMutation_refl_apply_of_card_le_two_of_ne hK B k hij.symm, neg_mul_neg]

/-- Uniform off-diagonal product bounds over the mutation class of any matrix on at most
two indices are equivalent to the initial entry bounds. -/
theorem forall_abs_foldl_matrixMutation_mul_le_iff_of_card_le_two (hK : Nat.card K ≤ 2)
    (B : Matrix K K ℤ) (bound : ℤ) :
    (∀ w : List K, ∀ i j : K, i ≠ j →
      |w.foldl (matrixMutation (Function.Embedding.refl K)) B i j *
        w.foldl (matrixMutation (Function.Embedding.refl K)) B j i| ≤ bound) ↔
      ∀ i j : K, i ≠ j → |B i j * B j i| ≤ bound := by
  refine ⟨fun h i j hij ↦ h [] i j hij, fun h w i j hij ↦ ?_⟩
  rw [foldl_matrixMutation_apply_mul_apply_of_card_le_two_of_ne hK B w hij]
  exact h i j hij

/-- Given two distinct indices, a uniform off-diagonal product bound for any matrix on at
most two indices is equivalent to checking their product alone. -/
theorem forall_abs_foldl_matrixMutation_mul_le_iff_of_card_le_two_of_ne
    (hK : Nat.card K ≤ 2) (B : Matrix K K ℤ) (bound : ℤ) {i₀ j₀ : K} (hij₀ : i₀ ≠ j₀) :
    (∀ w : List K, ∀ i j : K, i ≠ j →
      |w.foldl (matrixMutation (Function.Embedding.refl K)) B i j *
        w.foldl (matrixMutation (Function.Embedding.refl K)) B j i| ≤ bound) ↔
      |B i₀ j₀ * B j₀ i₀| ≤ bound := by
  rw [forall_abs_foldl_matrixMutation_mul_le_iff_of_card_le_two hK B]
  refine ⟨fun h ↦ h i₀ j₀ hij₀, fun hb i j hij ↦ ?_⟩
  rcases Finite.eq_or_eq_of_card_le_two hK hij₀ i with rfl | rfl <;>
    rcases Finite.eq_or_eq_of_card_le_two hK hij₀ j with rfl | rfl <;> simp_all [mul_comm]

/-- On `Fin 2` the uniform bound for any integer matrix is the bound on entries `(0,1)` and
`(1,0)`. -/
theorem forall_abs_foldl_matrixMutation_fin_two_mul_le_iff
    (B : Matrix (Fin 2) (Fin 2) ℤ) (bound : ℤ) :
    (∀ w : List (Fin 2), ∀ i j : Fin 2, i ≠ j →
      |w.foldl (matrixMutation (Function.Embedding.refl (Fin 2))) B i j *
        w.foldl (matrixMutation (Function.Embedding.refl (Fin 2))) B j i| ≤ bound) ↔
      |B 0 1 * B 1 0| ≤ bound :=
  forall_abs_foldl_matrixMutation_mul_le_iff_of_card_le_two_of_ne (by simp) B bound (by decide)

end TauCeti

namespace Matrix.IsSkewSymmetrizer

open TauCeti

variable {K : Type*} [DecidableEq K] [Finite K]

/-- Mutation on at most two indices negates a skew-symmetrizable matrix. -/
theorem matrixMutation_eq_neg_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) (k : K) :
    matrixMutation (Function.Embedding.refl K) B k = -B := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [(h.matrixMutation k).apply_self, Matrix.neg_apply, h.apply_self, neg_zero]
  · simpa only [Matrix.neg_apply] using
      matrixMutation_refl_apply_of_card_le_two_of_ne hK B k hij

/-- On at most two indices a mutation word acts on a skew-symmetrizable matrix by its
length parity. -/
theorem foldl_matrixMutation_eq_neg_one_pow_length_smul_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) (w : List K) :
    w.foldl (matrixMutation (Function.Embedding.refl K)) B = (-1 : ℤ) ^ w.length • B := by
  induction w generalizing B with
  | nil => simp
  | cons k w ih =>
    rw [List.foldl_cons, h.matrixMutation_eq_neg_of_card_le_two hK, ih h.neg]
    simp [pow_succ]

/-- Every mutation word sends a skew-symmetrizable matrix on at most two indices to itself or
its negative. -/
theorem foldl_matrixMutation_eq_or_eq_neg_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) (w : List K) :
    w.foldl (matrixMutation (Function.Embedding.refl K)) B = B ∨
      w.foldl (matrixMutation (Function.Embedding.refl K)) B = -B := by
  rw [h.foldl_matrixMutation_eq_neg_one_pow_length_smul_of_card_le_two hK]
  rcases neg_one_pow_eq_or ℤ w.length with hp | hp <;> simp [hp]

/-- The complete mutation class of a skew-symmetrizable matrix on at most two indices
consists of the matrix and its negative. If there are no indices, these two matrices coincide. -/
theorem range_foldl_matrixMutation_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) :
    Set.range (fun w : List K ↦ w.foldl (matrixMutation (Function.Embedding.refl K)) B) =
      {B, -B} := by
  ext A
  constructor
  · rintro ⟨w, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      h.foldl_matrixMutation_eq_or_eq_neg_of_card_le_two hK w
  · intro hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact ⟨[], rfl⟩
    · cases isEmpty_or_nonempty K with
      | inl h =>
        exact ⟨[], by ext i; exact (h.false i).elim⟩
      | inr hne =>
        obtain ⟨k⟩ := hne
        exact ⟨[k], by simpa using h.matrixMutation_eq_neg_of_card_le_two hK k⟩

/-- A skew-symmetrizable matrix on at most two indices has a finite mutation class,
independently of its entry sizes. -/
theorem finite_range_foldl_matrixMutation_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) :
    (Set.range (fun w : List K ↦
      w.foldl (matrixMutation (Function.Embedding.refl K)) B)).Finite := by
  rw [h.range_foldl_matrixMutation_of_card_le_two hK]
  exact (Set.finite_singleton (-B)).insert B

/-- Every mutation word preserves each product of transposed entries of a skew-symmetrizable
matrix on at most two indices, including the diagonal products. -/
theorem foldl_matrixMutation_apply_mul_apply_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2)
    (w : List K) (i j : K) :
    w.foldl (matrixMutation (Function.Embedding.refl K)) B i j *
      w.foldl (matrixMutation (Function.Embedding.refl K)) B j i = B i j * B j i := by
  rcases h.foldl_matrixMutation_eq_or_eq_neg_of_card_le_two hK w with hw | hw <;> simp [hw]

/-- For a skew-symmetrizable matrix on at most two indices, the Cartan companion is of finite
type exactly when every off-diagonal entry product has absolute value at most three. -/
theorem isFiniteType_cartanCompanion_iff_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) :
    IsFiniteType B.cartanCompanion ↔ ∀ i j, i ≠ j → |B i j * B j i| ≤ 3 := by
  constructor
  · intro hB i j hij
    have hprod := hB.apply_mul_apply_mem_of_ne hij
    simp only [cartanCompanion_apply_of_ne _ hij, cartanCompanion_apply_of_ne _ hij.symm,
      neg_mul_neg, ← abs_mul, Set.mem_insert_iff, Set.mem_singleton_iff] at hprod
    omega
  · intro hbound
    let A := B.cartanCompanion
    let d (i : K) : ℚ := s i
    have hd (i : K) : 0 < d i := by
      dsimp only [d]
      exact_mod_cast h.pos i
    have hsym (i j : K) : d i * (A i j : ℚ) = d j * (A j i : ℚ) := by
      dsimp only [d, A]
      exact_mod_cast h.mul_cartanCompanion_apply i j
    have hsmall (i j : K) (hij : i ≠ j) : (A i j : ℚ) * (A j i : ℚ) ≤ 3 := by
      have hp : A i j * A j i ≤ 3 := by
        simpa only [A, cartanCompanion_apply_of_ne _ hij,
          cartanCompanion_apply_of_ne _ hij.symm, neg_mul_neg, ← abs_mul] using hbound i j hij
      exact_mod_cast hp
    let M := Matrix.of fun i j ↦ d i * (A i j : ℚ)
    have hM : M.IsSymm := Matrix.IsSymm.ext fun i j ↦ hsym j i
    have hdiag (i : K) : M i i = 2 * d i := by simp [M, A, mul_comm]
    have hdM (i : K) : 0 < M i i := by
      rw [hdiag]
      exact mul_pos (by norm_num) (hd i)
    refine isFiniteType_of B.cartanCompanion_apply_self
      (fun _ _ hij ↦ B.cartanCompanion_nonpos_of_ne hij) hd
      (hM.posDef_of_card_le_two hK hdM ?_)
    intro i j hij
    have hdet : M i i * M j j - M i j * M j i =
        d i * d j * (4 - (A i j : ℚ) * (A j i : ℚ)) := by
      rw [hdiag i, hdiag j]
      simp only [M, Matrix.of_apply]
      ring
    rw [hdet]
    exact mul_pos (mul_pos (hd i) (hd j)) (by linarith [hsmall i j hij])

/-- On at most two indices, the mutation class has a finite-type Cartan companion exactly
when every off-diagonal product in the class has absolute value at most three. -/
theorem exists_isFiniteType_cartanCompanion_matrixMutationWord_iff_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) :
    (∃ w, IsFiniteType (matrixMutationWord (Function.Embedding.refl K) B w).cartanCompanion) ↔
      ∀ w : List K, ∀ i j, i ≠ j →
        |matrixMutationWord (Function.Embedding.refl K) B w i j *
          matrixMutationWord (Function.Embedding.refl K) B w j i| ≤ 3 := by
  simp only [matrixMutationWord_eq_foldl, cartanCompanion_foldl_matrixMutation_of_card_le_two hK,
    exists_const, forall_abs_foldl_matrixMutation_mul_le_iff_of_card_le_two hK]
  exact h.isFiniteType_cartanCompanion_iff_of_card_le_two hK

end Matrix.IsSkewSymmetrizer
