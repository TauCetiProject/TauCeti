/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclic

/-!
# Permutation matrices and the signed cyclic shift

Provides:
* Nonnegative weighted sums of permutation matrices (`Matrix.weight_le_sum_permMatrix`,
  `Matrix.sum_smul_permMatrix_apply_eq_zero_iff`).
* Basis-vector and row actions of `Matrix.permMatrixHom`, and products of adjacent-swap matrices
  (`Matrix.prod_finRange_permMatrixHom_adjSwap`, `Matrix.prod_finRange_succ_adjSwap`).
* The signed `n`-cycle matrix `Matrix.negCycleMatrix`, its basis action, `n`-th power `-1`,
  characteristic polynomial `X^n + 1`, and multiplicative order `2 * n`.
-/

public section

namespace Equiv.Perm

/-- Every entry of a permutation matrix is nonnegative. -/
theorem permMatrix_nonneg {n R : Type*} [DecidableEq n]
    [Zero R] [One R] [Preorder R] [ZeroLEOneClass R] (σ : Equiv.Perm n) (i j : n) :
    0 ≤ σ.permMatrix R i j := by
  simp only [PEquiv.toMatrix_toPEquiv_apply]
  exact (Pi.single_nonneg (α := fun _ : n ↦ R)).2 zero_le_one _

end Equiv.Perm

namespace Matrix

variable {n R : Type*} [DecidableEq n]
  [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-- A nonnegative weighted sum of permutation matrices has entries on each included
permutation diagonal at least as large as that permutation's weight. -/
theorem weight_le_sum_permMatrix (s : Finset (Equiv.Perm n)) (w : Equiv.Perm n → R)
    (hw : ∀ τ ∈ s, 0 ≤ w τ) {σ : Equiv.Perm n} (hσ : σ ∈ s) (k : n) :
    w σ ≤ (∑ τ ∈ s, w τ • τ.permMatrix R) k (σ k) := by
  simpa [Matrix.sum_apply, smul_apply, smul_eq_mul, PEquiv.toMatrix_toPEquiv_apply] using
    (Finset.single_le_sum (f := fun τ ↦ w τ * τ.permMatrix R k (σ k))
      (fun τ hτ ↦ mul_nonneg (hw τ hτ) (τ.permMatrix_nonneg k (σ k))) hσ)

end Matrix

namespace Matrix

/-- A combination of permutation matrices over a set `s` of permutations with positive weights
`w`, each of which stays inside the support of `K` and which together cover the support, has the
zero pattern of `K`. -/
theorem sum_smul_permMatrix_apply_eq_zero_iff {n α R : Type*} [DecidableEq n] [Zero α]
    [Semiring R] [PartialOrder R] [IsOrderedRing R] {K : Matrix n n α}
    {s : Finset (Equiv.Perm n)} {w : Equiv.Perm n → R} (hw : ∀ σ ∈ s, 0 < w σ)
    (hsub : ∀ σ ∈ s, ∀ k, K k (σ k) ≠ 0) (hcover : ∀ i j, K i j ≠ 0 → ∃ σ ∈ s, σ i = j)
    (i j : n) :
    (∑ σ ∈ s, w σ • σ.permMatrix R) i j = 0 ↔ K i j = 0 := by
  constructor
  · intro hzero
    by_contra hij
    obtain ⟨σ, hσmem, hσij⟩ := hcover i j hij
    have hle : w σ ≤ (∑ σ ∈ s, w σ • σ.permMatrix R) i j := by
      simpa only [hσij] using
        weight_le_sum_permMatrix s w (fun τ hτ ↦ (hw τ hτ).le) hσmem i
    exact ((hw σ hσmem).trans_le hle).ne' hzero
  · intro hij
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro σ hσ
    have hσij : σ i ≠ j := by
      intro heq
      exact hsub σ hσ i (heq ▸ hij)
    simp only [PEquiv.toMatrix_toPEquiv_apply]
    simp [hσij]

section PermMatrixHom

/-- Applying `permMatrixHom σ` to a standard basis vector `eⱼ` gives `e_{σ j}`. -/
theorem permMatrixHom_mulVec_single {κ R : Type*} [Fintype κ] [DecidableEq κ] [Semiring R]
    (σ : Equiv.Perm κ) (j : κ) :
    (permMatrixHom σ : Matrix κ κ R) *ᵥ Pi.single j 1 = Pi.single (σ j) 1 := by
  ext i
  rw [mulVec_single_one, col_apply, permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_apply]
  simp [Pi.single_apply, Equiv.eq_symm_apply, eq_comm]

/-- Left-multiplying `M` by `permMatrixHom σ` permutes the rows of `M` by `σ.symm`. -/
theorem permMatrixHom_mul_apply {κ₁ κ₂ R : Type*} [Fintype κ₁] [DecidableEq κ₁] [Semiring R]
    (σ : Equiv.Perm κ₁) (M : Matrix κ₁ κ₂ R) (r : κ₁) (j : κ₂) :
    ((permMatrixHom σ : Matrix κ₁ κ₁ R) * M) r j = M (σ.symm r) j := by
  rw [permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    Matrix.submatrix_apply, id_eq, Equiv.Perm.inv_def]

/-- Left-multiplying `M` by the swap matrix `permMatrixHom (Equiv.swap a b)` exchanges rows `a`
and `b`. -/
theorem permMatrixHom_swap_mul_apply {κ₁ κ₂ R : Type*} [Fintype κ₁] [DecidableEq κ₁] [Semiring R]
    (a b : κ₁) (M : Matrix κ₁ κ₂ R) (r : κ₁) (j : κ₂) :
    ((permMatrixHom (Equiv.swap a b) : Matrix κ₁ κ₁ R) * M) r j = M (Equiv.swap a b r) j := by
  rw [permMatrixHom_mul_apply, Equiv.symm_swap]

/-- The product of the first `k` adjacent-swap permutation matrices `(0, 1), …, (k - 1, k)` on
`Fin N` is `permMatrixHom (Fin.cycleRange k)`. -/
theorem prod_finRange_permMatrixHom_adjSwap {N : ℕ} {R : Type*} [Semiring R] (k : ℕ)
    (hk : k < N) :
    ((List.finRange k).map fun i : Fin k =>
        (permMatrixHom (Equiv.swap (⟨i.val, by omega⟩ : Fin N) ⟨i.val + 1, by omega⟩) :
          Matrix (Fin N) (Fin N) R)).prod =
      permMatrixHom (Fin.cycleRange ⟨k, hk⟩) := by
  rw [← Fin.prod_finRange_swap_eq_cycleRange k hk, map_list_prod, List.map_map]
  rfl

/-- Factoring the product of `m + 1` matrices on `Fin (m + 1)` whose first `m` factors are
adjacent-swap permutation matrices as `permMatrixHom (finRotate (m + 1))` followed by the last
factor. -/
theorem prod_finRange_succ_adjSwap {m : ℕ} {R : Type*} [Semiring R]
    (S : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hS : ∀ i : Fin m, S i.castSucc = permMatrixHom (Equiv.swap i.castSucc i.succ)) :
    ((List.finRange (m + 1)).map S).prod =
      permMatrixHom (finRotate (m + 1)) * S (Fin.last m) := by
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    List.map_singleton, List.prod_singleton, ← Fin.prod_finRange_swap_castSucc_succ m,
    map_list_prod, List.map_map]
  congr 1
  exact congrArg List.prod (List.map_congr_left fun i _ => hS i)

end PermMatrixHom

section NegCycleMatrix

open Polynomial

/-- The signed `n`-cycle matrix sending `eⱼ ↦ eⱼ₊₁` for `j + 1 < n` and `eₙ₋₁ ↦ -e₀`. -/
@[expose] def negCycleMatrix (n : ℕ) {R : Type*} [Zero R] [One R] [Neg R] :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r j =>
    if j.val + 1 < n then (if r.val = j.val + 1 then 1 else 0)
    else (if r.val = 0 then -1 else 0)

/-- Entrywise formula for `Matrix.negCycleMatrix`. -/
@[simp]
theorem negCycleMatrix_apply (n : ℕ) {R : Type*} [Zero R] [One R] [Neg R] (r j : Fin n) :
    (negCycleMatrix n : Matrix (Fin n) (Fin n) R) r j =
      if j.val + 1 < n then (if r.val = j.val + 1 then 1 else 0)
      else (if r.val = 0 then -1 else 0) :=
  rfl

/-- Applying the signed `n`-cycle matrix to the `j`-th standard basis vector shifts it to `j + 1`,
or sends the last basis vector `eₙ₋₁` to `-e₀`. -/
theorem negCycleMatrix_mulVec_single {n : ℕ} {R : Type*} [Ring R] (j : Fin n) :
    (negCycleMatrix n : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single j 1 =
      if hj : j.val + 1 < n then Pi.single ⟨j.val + 1, hj⟩ 1
      else -Pi.single ⟨0, by have := j.isLt; omega⟩ 1 := by
  ext r
  by_cases hj : j.val + 1 < n
  · simp [Matrix.mulVec_single, negCycleMatrix_apply, hj, Pi.single_apply, Fin.ext_iff]
  · by_cases hr : r.val = 0 <;>
      simp [Matrix.mulVec_single, negCycleMatrix_apply, hj, hr, Pi.single_apply, Fin.ext_iff]

/-- Powers of the signed `n`-cycle matrix shift `eⱼ` forward by `m` steps while `j + m < n`. -/
theorem negCycleMatrix_pow_mulVec_single {n : ℕ} {R : Type*} [Ring R] (j : Fin n) (m : ℕ)
    (hm : j.val + m < n) :
    (negCycleMatrix n : Matrix (Fin n) (Fin n) R) ^ m *ᵥ Pi.single j 1 =
      Pi.single ⟨j.val + m, hm⟩ 1 := by
  induction m generalizing j with
  | zero => rw [pow_zero, Matrix.one_mulVec]; congr 1
  | succ m ih =>
    have hj1 : j.val + 1 < n := by omega
    rw [pow_succ, ← Matrix.mulVec_mulVec, negCycleMatrix_mulVec_single,
      dite_eq_left_of_eq_true (eq_true hj1), ih ⟨j.val + 1, hj1⟩ (by simp; omega)]
    congr 1; ext; simp; omega

/-- The `n`-th power of the signed `n`-cycle matrix is `-1` (`1 ≤ n`). -/
theorem negCycleMatrix_pow_self {n : ℕ} {R : Type*} [Ring R] (hn : 1 ≤ n) :
    (negCycleMatrix n : Matrix (Fin n) (Fin n) R) ^ n = -1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have hsplit : j.val + (1 + (n - 1 - j.val)) = n := by have := j.isLt; omega
  have hpow := congrArg ((negCycleMatrix n : Matrix (Fin n) (Fin n) R) ^ ·) hsplit.symm
  rw [hpow, pow_add, pow_add, pow_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    negCycleMatrix_pow_mulVec_single j (n - 1 - j.val) (by have := j.isLt; omega),
    negCycleMatrix_mulVec_single,
    dite_eq_right_of_eq_false (eq_false (by have := j.isLt; simp; omega)),
    Matrix.mulVec_neg, negCycleMatrix_pow_mulVec_single ⟨0, by omega⟩ j.val (by simp),
    Matrix.neg_mulVec, Matrix.one_mulVec]
  congr 2; ext; simp

/-- The characteristic polynomial of the signed `n`-cycle matrix is `X^n + 1` (`1 ≤ n`). -/
theorem charpoly_negCycleMatrix {n : ℕ} {R : Type*} [CommRing R] (hn : 1 ≤ n) :
    (negCycleMatrix n : Matrix (Fin n) (Fin n) R).charpoly = X ^ n + 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  have hmon : ((X : R[X]) ^ n + 1).IsMonicOfDegree n :=
    (isMonicOfDegree_X_pow R n).add_right (by simpa using Nat.pos_of_ne_zero (by omega))
  refine charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_pow_mulVec_single
    (by omega) hmon (by simp [negCycleMatrix_pow_self hn]) fun m hm => ?_
  simpa using
    negCycleMatrix_pow_mulVec_single (R := R) (⟨0, by omega⟩ : Fin n) m (by simpa using hm)

/-- The multiplicative order of the signed `n`-cycle matrix is `2 * n` (`1 ≤ n`, when `2 ≠ 0`). -/
theorem orderOf_negCycleMatrix {n : ℕ} {R : Type*} [Ring R] [NeZero (2 : R)] (hn : 1 ≤ n) :
    orderOf (negCycleMatrix n : Matrix (Fin n) (Fin n) R) = 2 * n := by
  have h10 : (1 : R) ≠ 0 := fun h1 => NeZero.ne (2 : R) (by rw [← one_add_one_eq_two, h1, add_zero])
  refine (orderOf_eq_iff (by omega)).2 ⟨?_, fun m hm hpos h1 => ?_⟩
  · rw [mul_comm, pow_mul, negCycleMatrix_pow_self hn, neg_one_sq]
  · rcases lt_trichotomy m n with hlt | rfl | hgt
    · have hv := congrFun (negCycleMatrix_pow_mulVec_single (R := R) (⟨0, by omega⟩ : Fin n) m
        (by simpa using hlt)) ⟨0, by omega⟩
      simp [h1, Fin.ext_iff, hpos.ne', h10] at hv
    · have h0 := congrFun₂ (negCycleMatrix_pow_self (R := R) hn ▸ h1) ⟨0, by omega⟩ ⟨0, by omega⟩
      simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h0
      exact NeZero.ne (2 : R) (by rw [← one_add_one_eq_two]; nth_rw 2 [← h0]; rw [add_neg_cancel])
    · have hm_split : m = n + (m - n) := by omega
      have hm_pos : m - n ≠ 0 := by omega
      have hneg1 : (negCycleMatrix n : Matrix (Fin n) (Fin n) R) ^ (m - n) = -1 := by
        rw [hm_split, pow_add, negCycleMatrix_pow_self hn, neg_one_mul] at h1
        exact neg_eq_iff_eq_neg.mp h1
      have hv := congrFun (negCycleMatrix_pow_mulVec_single (R := R) (⟨0, by omega⟩ : Fin n) (m - n)
        (by simp; omega)) ⟨0, by omega⟩
      simp [hneg1, Fin.ext_iff, hm_pos, h10] at hv

end NegCycleMatrix

end Matrix
