/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Matrix.Permutation
import TauCeti.GroupTheory.Perm.Fin

/-!
# Permutation matrices: multiplication, basis action, and nonnegative sums

Multiplying a matrix on the left by `Matrix.permMatrixHom σ` permutes its rows by `σ.symm`, and
multiplying on the right permutes its columns by `σ`. In the standard basis
`Finsupp.basisSingleOne`, `Matrix.permMatrixHom σ` is the matrix of the permutation endomorphism
`Finsupp.lmapDomain R R σ`.

Each permutation's weight bounds the entries on its diagonal in a nonnegative weighted
sum of permutation matrices. This lets support arguments recover a whole permutation
diagonal from a positive weight. A positively weighted combination of permutations, each
lying in the support of a matrix `K` and together covering it, has the zero pattern of `K`.

## Main results

* `Equiv.Perm.permMatrix_nonneg`: every entry of a permutation matrix is nonnegative.
* `Matrix.permMatrixHom_mul`, `Matrix.permMatrixHom_mul_apply`: multiplying on the left by
  `permMatrixHom σ` permutes rows by `σ.symm`.
* `Matrix.mul_permMatrixHom`, `Matrix.mul_permMatrixHom_apply`: multiplying on the right by
  `permMatrixHom σ` permutes columns by `σ`.
* `LinearMap.toMatrix_basisSingleOne_lmapDomain`: in `Finsupp.basisSingleOne`, the matrix of
  `Finsupp.lmapDomain R R σ` is `Matrix.permMatrixHom σ`.
* `Matrix.weight_le_sum_permMatrix`: a nonnegative weighted sum of permutation matrices has entries
  on each included diagonal at least as large as that permutation's weight.
* `Matrix.sum_smul_permMatrix_apply_eq_zero_iff`: a positively weighted sum of permutations
  covering the support of `K` has the zero pattern of `K`.
* `Matrix.permMatrixHom_mulVec_single`,
  `Matrix.prod_finRange_permMatrixHom_swap_eq_permMatrixHom_cycleRange`,
  `Matrix.prod_finRange_succ_map_eq_permMatrixHom_finRotate_mul`: basis-vector action and
  products of adjacent-swap permutation matrices.
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

/-- Multiplying a matrix on the left by `permMatrixHom σ` permutes its rows by `σ.symm`. -/
theorem permMatrixHom_mul {m k R : Type*} [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (σ : Equiv.Perm m) (M : Matrix m k R) :
    permMatrixHom (R := R) σ * M = M.submatrix σ.symm id := by
  rw [permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.inv_def]

/-- Entrywise form of `Matrix.permMatrixHom_mul`:
`(permMatrixHom σ * M) i j = M (σ.symm i) j`. -/
theorem permMatrixHom_mul_apply {m k R : Type*} [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (σ : Equiv.Perm m) (M : Matrix m k R) (i : m) (j : k) :
    (permMatrixHom (R := R) σ * M) i j = M (σ.symm i) j := by
  rw [permMatrixHom_mul, submatrix_apply, id]

/-- Multiplying a matrix on the right by `permMatrixHom σ` permutes its columns by `σ`. -/
theorem mul_permMatrixHom {l m R : Type*} [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (M : Matrix l m R) (σ : Equiv.Perm m) :
    M * permMatrixHom (R := R) σ = M.submatrix id σ := by
  rw [permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, Equiv.Perm.inv_def,
    Equiv.symm_symm]

/-- Entrywise form of `Matrix.mul_permMatrixHom`: `(M * permMatrixHom σ) i j = M i (σ j)`. -/
theorem mul_permMatrixHom_apply {l m R : Type*} [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (M : Matrix l m R) (σ : Equiv.Perm m) (i : l) (j : m) :
    (M * permMatrixHom (R := R) σ) i j = M i (σ j) := by
  rw [mul_permMatrixHom, submatrix_apply, id]

end Matrix

namespace LinearMap

/-- In the standard basis `Finsupp.basisSingleOne`, the matrix of the permutation endomorphism
`Finsupp.lmapDomain R R σ` is `Matrix.permMatrixHom σ`. -/
theorem toMatrix_basisSingleOne_lmapDomain {n R : Type*} [CommSemiring R] [Fintype n]
    [DecidableEq n] (σ : Equiv.Perm n) :
    LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
      (Finsupp.lmapDomain R R σ) = Matrix.permMatrixHom (R := R) σ := by
  ext p q
  simp [LinearMap.toMatrix_apply, Finsupp.single_apply, Matrix.permMatrixHom_apply,
    PEquiv.toMatrix_apply, Equiv.Perm.inv_def, Equiv.eq_symm_apply, eq_comm]

end LinearMap

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
  rw [permMatrixHom_apply, Equiv.Perm.permMatrix, Equiv.Perm.inv_def,
    PEquiv.toMatrix_toPEquiv_mulVec σ.symm (Pi.single j 1), Pi.single_comp_equiv, Equiv.symm_symm]

/-- The product of the first `k` adjacent-swap permutation matrices `(0, 1), …, (k - 1, k)` on
`Fin N` is `permMatrixHom (Fin.cycleRange k)`. -/
theorem prod_finRange_permMatrixHom_swap_eq_permMatrixHom_cycleRange {N : ℕ} {R : Type*}
    [Semiring R] (k : ℕ) (hk : k < N) :
    ((List.finRange k).map fun i : Fin k =>
        (permMatrixHom (Equiv.swap (⟨i.val, by omega⟩ : Fin N) ⟨i.val + 1, by omega⟩) :
          Matrix (Fin N) (Fin N) R)).prod =
      permMatrixHom (Fin.cycleRange ⟨k, hk⟩) := by
  rw [← Fin.prod_finRange_swap_eq_cycleRange k hk, map_list_prod, List.map_map]
  rfl

/-- Factoring the product of `m + 1` matrices on `Fin (m + 1)` whose first `m` factors are
adjacent-swap permutation matrices as `permMatrixHom (finRotate (m + 1))` followed by the last
factor. -/
theorem prod_finRange_succ_map_eq_permMatrixHom_finRotate_mul {m : ℕ} {R : Type*} [Semiring R]
    (S : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hS : ∀ i : Fin m, S i.castSucc = permMatrixHom (Equiv.swap i.castSucc i.succ)) :
    ((List.finRange (m + 1)).map S).prod =
      permMatrixHom (finRotate (m + 1)) * S (Fin.last m) := by
  have hcyc : ((List.finRange m).map fun i : Fin m =>
      Equiv.swap i.castSucc i.succ).prod = finRotate (m + 1) :=
    (Fin.prod_finRange_swap_eq_cycleRange m (Nat.lt_succ_self m)).trans (Fin.cycleRange_last m)
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    List.map_singleton, List.prod_singleton, ← hcyc, map_list_prod, List.map_map]
  congr 1
  exact congrArg List.prod (List.map_congr_left fun i _ => hS i)

end PermMatrixHom

end Matrix
