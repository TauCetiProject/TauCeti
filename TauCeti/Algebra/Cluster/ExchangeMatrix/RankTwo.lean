/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import TauCeti.Algebra.Cluster.ExchangeMatrix.CartanCompanion
public import Mathlib.SetTheory.Cardinal.NatCard

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Mutation classes with at most two indices

Mutation of a skew-symmetrizable matrix on at most two indices negates it. A word acts
by the sign `(-1)^length`, its full mutation class is `{B, -B}`, and its Cartan companion
and each product `bᵢⱼ bⱼᵢ` are invariant. This includes empty and singleton index types.
The bound at most three throughout this class is equivalent to the bound at the initial matrix.
These statements concern matrix mutation classes, not finiteness of cluster variables:
matrices with off-diagonal entry product of absolute value at least four also have finite
matrix mutation classes on two indices.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), §1, Theorem 1.8 and the rank-two discussion.
-/

public section

open Matrix

namespace TauCeti

variable {K : Type*} [DecidableEq K] [Finite K]

omit [DecidableEq K] in
private theorem eq_or_eq_of_card_le_two (hK : Nat.card K ≤ 2) {i j : K} (hij : i ≠ j)
    (k : K) : k = i ∨ k = j := by
  classical
  let := Fintype.ofFinite K
  by_contra hk
  push Not at hk
  have hlt := Fintype.two_lt_card_iff.mpr ⟨k, i, j, hk.1, hk.2, hij⟩
  rw [← Nat.card_eq_fintype_card] at hlt
  omega

/-- Mutation on at most two indices negates a skew-symmetrizable matrix. -/
theorem matrixMutation_eq_neg_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (k : K) :
    matrixMutation (Function.Embedding.refl K) B k = -B := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [(h.matrixMutation k).apply_self, Matrix.neg_apply, h.apply_self, neg_zero]
  · rcases eq_or_eq_of_card_le_two hK hij k with rfl | rfl <;>
      simp [matrixMutation_apply]

/-- A single mutation preserves the companion when there are at most two indices. -/
theorem cartanCompanion_matrixMutation_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (k : K) :
    (matrixMutation (Function.Embedding.refl K) B k).cartanCompanion = B.cartanCompanion := by
  rw [matrixMutation_eq_neg_of_card_le_two hK h, cartanCompanion_neg]

/-- On at most two indices a mutation word acts by its length parity. -/
theorem foldl_matrixMutation_eq_sign_smul_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (w : List K) :
    w.foldl (matrixMutation (Function.Embedding.refl K)) B = (-1 : ℤ) ^ w.length • B := by
  induction w generalizing B with
  | nil => simp
  | cons k w ih =>
    rw [List.foldl_cons, matrixMutation_eq_neg_of_card_le_two hK h, ih h.neg]
    simp [pow_succ]

/-- Every mutation word on at most two indices reaches the matrix or its negative. -/
theorem foldl_matrixMutation_eq_or_eq_neg_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (w : List K) :
    w.foldl (matrixMutation (Function.Embedding.refl K)) B = B ∨
      w.foldl (matrixMutation (Function.Embedding.refl K)) B = -B := by
  rw [foldl_matrixMutation_eq_sign_smul_of_card_le_two hK h]
  rcases neg_one_pow_eq_or ℤ w.length with hp | hp <;> simp [hp]

/-- Every mutation word preserves the companion when there are at most two indices. -/
theorem cartanCompanion_foldl_matrixMutation_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (w : List K) :
    (w.foldl (matrixMutation (Function.Embedding.refl K)) B).cartanCompanion =
      B.cartanCompanion := by
  rcases foldl_matrixMutation_eq_or_eq_neg_of_card_le_two hK h w with hw | hw <;> simp [hw]

/-- The complete mutation class on at most two indices consists of the matrix and its
negative. If there are no indices, these two matrices coincide. -/
theorem range_foldl_matrixMutation_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) :
    Set.range (fun w : List K ↦ w.foldl (matrixMutation (Function.Embedding.refl K)) B) =
      {B, -B} := by
  ext A
  constructor
  · rintro ⟨w, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      foldl_matrixMutation_eq_or_eq_neg_of_card_le_two hK h w
  · intro hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact ⟨[], rfl⟩
    · cases isEmpty_or_nonempty K with
      | inl h =>
        exact ⟨[], by ext i; exact (h.false i).elim⟩
      | inr hne =>
        obtain ⟨k⟩ := hne
        exact ⟨[k], by simpa using matrixMutation_eq_neg_of_card_le_two hK h k⟩

/-- A skew-symmetrizable matrix on at most two indices has a finite mutation class,
independently of its entry sizes. -/
theorem finite_range_foldl_matrixMutation_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) :
    (Set.range (fun w : List K ↦
      w.foldl (matrixMutation (Function.Embedding.refl K)) B)).Finite := by
  rw [range_foldl_matrixMutation_of_card_le_two hK h]
  exact (Set.finite_singleton (-B)).insert B

/-- Every mutation word preserves each product of transposed entries when there are at
most two indices, including the diagonal products. -/
theorem foldl_matrixMutation_apply_mul_apply_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (w : List K) (i j : K) :
    w.foldl (matrixMutation (Function.Embedding.refl K)) B i j *
      w.foldl (matrixMutation (Function.Embedding.refl K)) B j i = B i j * B j i := by
  rcases foldl_matrixMutation_eq_or_eq_neg_of_card_le_two hK h w with hw | hw <;> simp [hw]

/-- Uniform off-diagonal product bounds over the mutation class on at most two indices
are equivalent to the initial entry bounds. -/
theorem forall_abs_foldl_matrixMutation_mul_le_iff_of_card_le_two (hK : Nat.card K ≤ 2)
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (bound : ℤ) :
    (∀ w : List K, ∀ i j : K, i ≠ j →
      |w.foldl (matrixMutation (Function.Embedding.refl K)) B i j *
        w.foldl (matrixMutation (Function.Embedding.refl K)) B j i| ≤ bound) ↔
      ∀ i j : K, i ≠ j → |B i j * B j i| ≤ bound := by
  simp only [foldl_matrixMutation_apply_mul_apply_of_card_le_two hK h, forall_const]

/-- Given two distinct indices, a uniform off-diagonal product bound is equivalent to
checking their product alone. -/
theorem forall_abs_foldl_matrixMutation_mul_le_iff_of_ne_of_card_le_two
    (hK : Nat.card K ≤ 2) {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s)
    (bound : ℤ) {i₀ j₀ : K} (hij₀ : i₀ ≠ j₀) :
    (∀ w : List K, ∀ i j : K, i ≠ j →
      |w.foldl (matrixMutation (Function.Embedding.refl K)) B i j *
        w.foldl (matrixMutation (Function.Embedding.refl K)) B j i| ≤ bound) ↔
      |B i₀ j₀ * B j₀ i₀| ≤ bound := by
  rw [forall_abs_foldl_matrixMutation_mul_le_iff_of_card_le_two hK h]
  refine ⟨fun h ↦ h i₀ j₀ hij₀, fun hb i j hij ↦ ?_⟩
  rcases eq_or_eq_of_card_le_two hK hij₀ i with rfl | rfl <;>
    rcases eq_or_eq_of_card_le_two hK hij₀ j with rfl | rfl <;> simp_all [mul_comm]

/-- On `Fin 2` the uniform bound is the bound on entries `(0,1)` and `(1,0)`. -/
theorem forall_abs_foldl_matrixMutation_fin_two_mul_le_iff
    {B : Matrix (Fin 2) (Fin 2) ℤ} {s : Fin 2 → ℤ} (h : B.IsSkewSymmetrizer s) (bound : ℤ) :
    (∀ w : List (Fin 2), ∀ i j : Fin 2, i ≠ j →
      |w.foldl (matrixMutation (Function.Embedding.refl (Fin 2))) B i j *
        w.foldl (matrixMutation (Function.Embedding.refl (Fin 2))) B j i| ≤ bound) ↔
      |B 0 1 * B 1 0| ≤ bound :=
  forall_abs_foldl_matrixMutation_mul_le_iff_of_ne_of_card_le_two (by simp) h bound (by decide)

end TauCeti
