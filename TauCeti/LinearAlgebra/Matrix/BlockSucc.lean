/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Placing a square matrix in the upper-left block of the next size

A square matrix of size `n` becomes one of size `n + 1` by putting it in the upper-left block and
filling the last row and column with those of the identity matrix.  This file builds that map,
`Matrix.blockSucc`, and shows it is multiplicative, unital and injective, and that it leaves the
determinant unchanged while adding `1` to the trace.

The construction is written with `Fin.snoc` rather than as `Matrix.fromBlocks M 0 0 1` reindexed
along `finSumFinEquiv`, because `Fin (n + 1)` is the index type the general linear groups and their
standard representations are stated over: a `Fin n ⊕ Fin 1` presentation would have to be
reindexed away again at once.

`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/BlockSucc.lean` deduces from this the **block
inclusion** `TauCeti.glBlockSucc : GL (Fin n) k →* GL (Fin (n + 1)) k`, the embedding that fixes
the last basis vector.

## Main definitions

* `Matrix.blockSucc`: a square matrix placed in the upper-left block of the next size, with the
  last row and column of the identity matrix.
* `Matrix.blockSuccMonoidHom`: the same map, bundled as a monoid homomorphism.  It is *not*
  additive: the last diagonal entry is `1` for every `M`, so `blockSucc 0` is not `0`.

## Main results

* `Matrix.blockSucc_mulVec`: the extended matrix acts on the first `n` coordinates by `M` and
  fixes the last one.
* `Matrix.trace_blockSucc` and `Matrix.det_blockSucc`: the trace grows by one and the determinant
  is unchanged.
-/

public section

universe u

namespace Matrix

variable {k : Type u} {n : ℕ}

section Semiring

variable [Semiring k]

/-- A square matrix of size `n`, placed in the upper-left block of a square matrix of size `n + 1`
whose last row and column are those of the identity matrix. -/
def blockSucc (M : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  .of (Fin.snoc (fun i => Fin.snoc (M i) 0) (Fin.snoc 0 1))

@[simp]
theorem blockSucc_castSucc_castSucc (M : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    blockSucc M i.castSucc j.castSucc = M i j := by
  simp [blockSucc]

@[simp]
theorem blockSucc_castSucc_last (M : Matrix (Fin n) (Fin n) k) (i : Fin n) :
    blockSucc M i.castSucc (Fin.last n) = 0 := by
  simp [blockSucc]

@[simp]
theorem blockSucc_last_castSucc (M : Matrix (Fin n) (Fin n) k) (j : Fin n) :
    blockSucc M (Fin.last n) j.castSucc = 0 := by
  simp [blockSucc]

@[simp]
theorem blockSucc_last_last (M : Matrix (Fin n) (Fin n) k) :
    blockSucc M (Fin.last n) (Fin.last n) = 1 := by
  simp [blockSucc]

@[simp]
theorem blockSucc_one : blockSucc (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [(Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [(Fin.castSucc_lt_last i).ne]
    | cast j => simp [Matrix.one_apply, Fin.castSucc_inj]

/-- Extending a product is the product of the extensions: the last row and column of
`Matrix.blockSucc M` are those of the identity matrix, so the extra index contributes only its own
diagonal entry.  This is what makes `Matrix.blockSuccMonoidHom` and hence the block inclusion
`TauCeti.glBlockSucc` multiplicative. -/
theorem blockSucc_mul (M N : Matrix (Fin n) (Fin n) k) :
    blockSucc (M * N) = blockSucc M * blockSucc N := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [Matrix.mul_apply]

/-- The upper-left block embedding of matrices, bundled as a monoid homomorphism.  It is unital
because the last row and column of `Matrix.blockSucc M` are those of the identity matrix, and for
the same reason it is not additive. -/
def blockSuccMonoidHom (k : Type u) (n : ℕ) [Semiring k] :
    Matrix (Fin n) (Fin n) k →* Matrix (Fin (n + 1)) (Fin (n + 1)) k where
  toFun := blockSucc
  map_one' := blockSucc_one
  map_mul' := blockSucc_mul

@[simp]
theorem blockSuccMonoidHom_apply (M : Matrix (Fin n) (Fin n) k) :
    blockSuccMonoidHom k n M = blockSucc M :=
  (rfl)

/-- Extending a matrix loses no information: `Matrix.blockSucc` is injective, because the
upper-left block of `Matrix.blockSucc M` is `M`.  Use it to transfer an equation between extended
matrices back to the original size; `TauCeti.glBlockSucc_injective` is the group-level form. -/
theorem blockSucc_injective : Function.Injective (blockSucc (k := k) (n := n)) := by
  intro M N h
  ext i j
  simpa using congrArg (fun A => A i.castSucc j.castSucc) h

/-- The extended matrix acts by `M` on the first `n` coordinates and fixes the last one. -/
@[simp]
theorem blockSucc_mulVec (M : Matrix (Fin n) (Fin n) k) (v : Fin (n + 1) → k) :
    blockSucc M *ᵥ v = Fin.snoc (M *ᵥ Fin.init v) (v (Fin.last n)) := by
  funext i
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [Matrix.mulVec, dotProduct, Fin.init]

/-- Extending a matrix adds `1` to its trace: the new diagonal entry is the last diagonal entry of
the identity matrix. -/
@[simp]
theorem trace_blockSucc (M : Matrix (Fin n) (Fin n) k) :
    (blockSucc M).trace = M.trace + 1 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_castSucc]

end Semiring

section CommRing

variable [CommRing k]

/-- Extending a matrix leaves its determinant unchanged, so it takes matrices of determinant `1`
to matrices of determinant `1`. -/
@[simp]
theorem det_blockSucc (M : Matrix (Fin n) (Fin n) k) : (blockSucc M).det = M.det := by
  have hsub : (blockSucc M).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = M := by
    ext i j
    simp
  rw [Matrix.det_succ_row _ (Fin.last n),
    Finset.sum_eq_single (Fin.last n) (fun j _ hj => ?_) fun h => absurd (Finset.mem_univ _) h]
  · rw [hsub, blockSucc_last_last, mul_one, Fin.val_last,
      Even.neg_one_pow (⟨n, rfl⟩ : Even (n + n)), one_mul]
  · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
    simp

end CommRing

end Matrix
