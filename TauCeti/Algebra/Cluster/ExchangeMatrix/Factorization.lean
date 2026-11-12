/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.RowCol

import Mathlib.Tactic.LinearCombination

/-!
# Signed factorization of matrix mutation

An extended matrix with vanishing mutable diagonal admits the factorization
`μₖ(B) = Eε * B * Fε` for either sign `ε = ±1`. The integral matrices `Eε` and `Fε`
are involutions. Thus mutation preserves rational rank and independence of the columns,
including for rectangular matrices with frozen rows. The factorization also supplies the
change of lattice basis used to mutate compatible alternating forms.

The factors are defined without finiteness assumptions; only their products require finite
index types. No skew-symmetrizability assumption is needed beyond the vanishing diagonal
entry in the factorization theorem.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195
  (2005), §3, equations (3.2)–(3.4).
* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Mathematical Journal 126 (2005), §1.
-/

public section

namespace TauCeti

open Matrix

variable {I K I' K' : Type*} [DecidableEq I] [DecidableEq K]

/-- The left mutation factor `Eε`: the identity with column `row k` replaced by
`-1` on its diagonal and `[-ε * B i k]₊` elsewhere. -/
def matrixMutationLeft (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (ε : ℤ) : Matrix I I ℤ :=
  (1 : Matrix I I ℤ).updateCol (row k) fun i ↦
    if i = row k then -1 else (-ε * B i k)⁺

/-- The right mutation factor `Fε`: the identity with row `k` replaced by `-1` on
its diagonal and `[ε * B (row k) j]₊` elsewhere. -/
def matrixMutationRight (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (ε : ℤ) : Matrix K K ℤ :=
  (1 : Matrix K K ℤ).updateRow k fun j ↦
    if j = k then -1 else (ε * B (row k) j)⁺

variable (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (ε : ℤ)

omit [DecidableEq K] in
/-- The entries of the left mutation factor. -/
theorem matrixMutationLeft_apply (i j : I) :
    matrixMutationLeft row B k ε i j =
      if j = row k then (if i = row k then -1 else (-ε * B i k)⁺) else (1 : Matrix I I ℤ) i j := by
  simp [matrixMutationLeft, updateCol_apply]

omit [DecidableEq I] in
/-- The entries of the right mutation factor. -/
theorem matrixMutationRight_apply (i j : K) :
    matrixMutationRight row B k ε i j =
      if i = k then (if j = k then -1 else (ε * B (row k) j)⁺) else (1 : Matrix K K ℤ) i j := by
  simp [matrixMutationRight, updateRow_apply]

omit [DecidableEq K] in
@[simp]
theorem matrixMutationLeft_apply_col (i : I) :
    matrixMutationLeft row B k ε i (row k) = if i = row k then -1 else (-ε * B i k)⁺ := by
  simp [matrixMutationLeft_apply]

omit [DecidableEq I] in
@[simp]
theorem matrixMutationRight_apply_row (j : K) :
    matrixMutationRight row B k ε k j = if j = k then -1 else (ε * B (row k) j)⁺ := by
  simp [matrixMutationRight_apply]

omit [DecidableEq K] in
@[simp]
theorem matrixMutationLeft_apply_of_ne (i : I) {j : I} (hj : j ≠ row k) :
    matrixMutationLeft row B k ε i j = (1 : Matrix I I ℤ) i j := by
  simp [matrixMutationLeft_apply, hj]

omit [DecidableEq I] in
@[simp]
theorem matrixMutationRight_apply_of_ne {i : K} (hi : i ≠ k) (j : K) :
    matrixMutationRight row B k ε i j = (1 : Matrix K K ℤ) i j := by
  simp [matrixMutationRight_apply, hi]

omit [DecidableEq K] in
/-- Left mutation factors commute with injective restriction of rows and compatible
relabelling of mutable indices. -/
theorem matrixMutationLeft_submatrix [DecidableEq I'] {row' : K' ↪ I'} {f : I' → I}
    {g : K' → K} (hf : Function.Injective f) (h : ∀ a, f (row' a) = row (g a))
    (k : K') :
    matrixMutationLeft row' (B.submatrix f g) k ε =
      (matrixMutationLeft row B (g k) ε).submatrix f f := by
  ext i j
  have hrow (a : I') : f a = row (g k) ↔ a = row' k := by rw [← h, hf.eq_iff]
  simp only [matrixMutationLeft_apply, submatrix_apply, Matrix.one_apply, hrow, hf.eq_iff]

omit [DecidableEq I] in
/-- Right mutation factors commute with injective restriction of mutable indices and
compatible relabelling of rows. -/
theorem matrixMutationRight_submatrix [DecidableEq K'] {row' : K' ↪ I'} {f : I' → I}
    {g : K' → K} (hg : Function.Injective g) (h : ∀ a, f (row' a) = row (g a))
    (k : K') :
    matrixMutationRight row' (B.submatrix f g) k ε =
      (matrixMutationRight row B (g k) ε).submatrix g g := by
  ext i j
  simp only [matrixMutationRight_apply, submatrix_apply, Matrix.one_apply, hg.eq_iff, h]

section Products

variable [Fintype I] [Fintype K]

omit [DecidableEq K] [Fintype K] in
/-- Left multiplication by `Eε` negates the selected row and adds a multiple of that row
to every other row. -/
theorem matrixMutationLeft_mul_apply {J : Type*} (A : Matrix I J ℤ) (i : I) (j : J) :
    (matrixMutationLeft row B k ε * A) i j =
      if i = row k then -A i j else A i j + (-ε * B i k)⁺ * A (row k) j := by
  by_cases hi : i = row k
  · subst i
    simp +contextual [Matrix.mul_apply, matrixMutationLeft_apply, ite_mul, eq_comm]
  · have hrow (l : I) : matrixMutationLeft row B k ε i l =
        (1 : Matrix I I ℤ) i l + if l = row k then (-ε * B i k)⁺ else 0 := by
      by_cases hl : l = row k <;> simp [matrixMutationLeft_apply, hl, hi, Matrix.one_apply]
    simp [Matrix.mul_apply, hrow, add_mul, Finset.sum_add_distrib, ite_mul, hi, Matrix.one_apply]

omit [DecidableEq I] [Fintype I] in
/-- Right multiplication by `Fε` negates the selected column and adds a multiple of that
column to every other column. -/
theorem mul_matrixMutationRight_apply {J : Type*} (A : Matrix J K ℤ) (i : J) (j : K) :
    (A * matrixMutationRight row B k ε) i j =
      if j = k then -A i j else A i j + A i k * (ε * B (row k) j)⁺ := by
  by_cases hj : j = k
  · subst j
    simp +contextual [Matrix.mul_apply, matrixMutationRight_apply, mul_ite]
  · have hcol (l : K) : matrixMutationRight row B k ε l j =
        (1 : Matrix K K ℤ) l j + if l = k then (ε * B (row k) j)⁺ else 0 := by
      by_cases hl : l = k <;> simp_all [Matrix.one_apply, eq_comm]
    simp [Matrix.mul_apply, hcol, mul_add, Finset.sum_add_distrib, mul_ite, hj, Matrix.one_apply]

omit [DecidableEq K] [Fintype K] in
/-- The left mutation factor is its own inverse, for every integer parameter. -/
@[simp]
theorem matrixMutationLeft_mul_self :
    matrixMutationLeft row B k ε * matrixMutationLeft row B k ε = 1 := by
  ext i j
  rw [matrixMutationLeft_mul_apply]
  by_cases hi : i = row k <;> by_cases hj : j = row k <;>
    simp [matrixMutationLeft_apply, hi, hj, Matrix.one_apply, eq_comm]

omit [DecidableEq I] [Fintype I] in
/-- The right mutation factor is its own inverse, for every integer parameter. -/
@[simp]
theorem matrixMutationRight_mul_self :
    matrixMutationRight row B k ε * matrixMutationRight row B k ε = 1 := by
  ext i j
  rw [mul_matrixMutationRight_apply]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp_all [matrixMutationRight_apply, Matrix.one_apply, eq_comm]

/-- Signed factorization of extended matrix mutation. Only the selected mutable diagonal
entry must vanish; the other entries need not be skew-symmetrizable. -/
theorem matrixMutation_eq_mul (hkk : B (row k) k = 0) (hε : ε = 1 ∨ ε = -1) :
    matrixMutation row B k = matrixMutationLeft row B k ε * B * matrixMutationRight row B k ε := by
  ext i j
  rw [mul_matrixMutationRight_apply, matrixMutationLeft_mul_apply,
    matrixMutationLeft_mul_apply]
  by_cases hi : i = row k
  · subst i
    by_cases hj : j = k <;> simp [hkk, hj]
  by_cases hj : j = k
  · simp [hj, hi, hkk]
  simp only [hi, hj, ite_false, hkk, mul_zero, add_zero,
    matrixMutation_apply_of_ne hi hj]
  rcases hε with rfl | rfl
  · simp only [neg_mul, one_mul]
    rw [posPart_neg]
    linear_combination (B (row k) j)⁺ * (posPart_sub_negPart (B i k)) +
      (B i k)⁻ * (posPart_sub_negPart (B (row k) j))
  · simp only [neg_neg, one_mul, neg_one_mul, posPart_neg]
    linear_combination (B (row k) j)⁻ * (posPart_sub_negPart (B i k)) +
      (B i k)⁺ * (posPart_sub_negPart (B (row k) j))

omit [Fintype I] in
/-- Mutation preserves rank after scalar change to any commutative ring. In particular,
choosing `R = ℚ` gives preservation of rational column rank. -/
theorem rank_matrixMutation [Finite I] {R : Type*} [CommRing R] (hkk : B (row k) k = 0) :
    ((matrixMutation row B k).map (Int.castRingHom R)).rank =
      (B.map (Int.castRingHom R)).rank := by
  let := Fintype.ofFinite I
  have hL : IsUnit ((matrixMutationLeft row B k 1).map (Int.castRingHom R)).det := by
    apply Matrix.isUnit_det_of_left_inverse
    rw [← Matrix.map_mul, matrixMutationLeft_mul_self]
    simp
  have hF : IsUnit ((matrixMutationRight row B k 1).map (Int.castRingHom R)).det := by
    apply Matrix.isUnit_det_of_left_inverse
    rw [← Matrix.map_mul, matrixMutationRight_mul_self]
    simp
  rw [matrixMutation_eq_mul row B k 1 hkk (Or.inl rfl), Matrix.map_mul, Matrix.map_mul,
    rank_mul_eq_left_of_isUnit_det _ _ hF, rank_mul_eq_right_of_isUnit_det _ _ hL]

omit [Fintype I] [Fintype K] in
/-- Mutation preserves independence of the columns after scalar change. This applies in
particular to rational independence, with no full-rank assumption on the mutable block. -/
theorem linearIndependent_col_matrixMutation_iff [Finite I] [Finite K] {R : Type*}
    [CommRing R] [Nontrivial R]
    (hkk : B (row k) k = 0) :
    LinearIndependent R ((matrixMutation row B k).map (Int.castRingHom R)).col ↔
      LinearIndependent R (B.map (Int.castRingHom R)).col := by
  let := Fintype.ofFinite I
  let := Fintype.ofFinite K
  simp_rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
    ← rank_eq_finrank_span_cols, rank_matrixMutation row B k hkk]

end Products

/-- For a nonsymmetric rank-two exchange matrix, the positive-sign left factor contains
the negative part of the mutable column. -/
example : matrixMutationLeft (Function.Embedding.refl (Fin 2)) !![0, 1; -2, 0] 0 1 =
    !![-1, 0; 2, 1] := by
  decide

/-- The positive-sign right factor contains the positive part of the mutable row. -/
example : matrixMutationRight (Function.Embedding.refl (Fin 2)) !![0, 1; -2, 0] 0 1 =
    !![-1, 1; 0, 1] := by
  decide

/-- The extended rank-one column remains rationally independent after mutation. -/
example : LinearIndependent ℚ
    ((matrixMutation (Fin.castSuccEmb (n := 1)) !![0; 1] 0).map (Int.castRingHom ℚ)).col := by
  rw [linearIndependent_col_matrixMutation_iff _ _ _ (by decide), linearIndependent_unique_iff]
  intro h
  have h1 := congrArg (fun v ↦ v (1 : Fin 2)) h
  norm_num [Matrix.col] at h1

end TauCeti
