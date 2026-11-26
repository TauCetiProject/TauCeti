/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.LinearAlgebra.Matrix.CornerBlockSucc
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# Existence of Smith normal forms

Over a commutative ring in which divisibility is total (`PreValuationRing`), for instance a
valuation domain such as a discrete valuation ring or the non-noetherian valuation ring of a valued
field such as `ℂ` with the absolute value pulled back from `PadicAlgCl ℓ`, or `ZMod (p ^ n)` for a
prime `p`, every square matrix has a Smith normal form: unimodular row and column operations bring
it to a diagonal matrix whose entries form a divisibility chain `s₀ ∣ s₁ ∣ ⋯`. Singular matrices
are included: zero entries appear at the end of the chain.

The proof is elimination. Of finitely many elements of such a ring one divides all the others,
since divisibility is total. Move such an entry of the matrix to the corner, clear its row and
column, and treat the block that is left, all of whose entries are multiples of the corner entry.

Over a principal ideal domain, `Matrix.exists_mul_mul_eq_diagonal` in
`TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Diagonal` diagonalises without a divisibility chain;
its refinement over `ℤ`, with transformations of determinant `1` and a positive diagonal, is in
`TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Int`. The characterisation of the invariant
factors by minors is in `TauCeti.LinearAlgebra.Matrix.InvariantFactor`.

## Main results

* `Matrix.exists_smith_normal_form_of_preValuationRing`: over a commutative ring with total
  divisibility, a square matrix is equivalent to a diagonal matrix whose entries form a
  divisibility chain.
* `Matrix.exists_mul_mul_eq_diagonal_of_preValuationRing`: the same for matrices indexed by any
  finite type, without the divisibility chain.
* `Matrix.exists_mul_mul_eq_of_mul_submatrix_mul_eq`: over any commutative ring, if a matrix with
  permuted rows and columns is equivalent to `D` by transformations of unit determinant, so is the
  matrix itself.

## References

The elimination proof is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic PBC) at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
`grh/src/Lib/General/LinearAlgebra/IntegralLattices.lean`: `New.IsValuationPair.smith_normal_form`
(induction on the size, bringing a pivot that divides every entry to the corner) and its
elimination step `New.exists_eq_mul_diagonal_mul_of_pivot_dvd` (clearing the pivot's row and
column). There the subring is a valuation pair inside a larger ring and the pivot comes from
`New.IsValuationPair.exists_pivot_dvd`; here the ring is any commutative ring in which divisibility
is total (`PreValuationRing`), the pivot is chosen by
`TauCeti.PreValuationRing.exists_forall_dvd`, and the divisibility chain `s₀ ∣ s₁ ∣ ⋯`, which
grh-lean does not state, is added.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- **Equivalence is unchanged by permuting rows and columns.** If `L * A.submatrix σ τ * Q = D`
with `L`, `Q` of unit determinant, then `L' * A * Q' = D` for some `L'`, `Q'` of unit determinant,
namely `L` with its columns permuted by `σ⁻¹` and `Q` with its rows permuted by `τ⁻¹`, whose
determinants are those of `L` and `Q` up to sign. The matrix `D` is arbitrary. -/
theorem exists_mul_mul_eq_of_mul_submatrix_mul_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A L Q D : Matrix n n R} (σ τ : Equiv.Perm n) (hL : IsUnit L.det) (hQ : IsUnit Q.det)
    (h : L * A.submatrix σ τ * Q = D) :
    ∃ L' Q' : Matrix n n R, IsUnit L'.det ∧ IsUnit Q'.det ∧ L' * A * Q' = D := by
  refine ⟨L.submatrix id σ.symm, Q.submatrix τ.symm id, ?_, ?_, ?_⟩
  · rw [det_permute']
    exact ((Equiv.Perm.sign σ.symm).isUnit.map (Int.castRingHom R)).mul hL
  · rw [det_permute]
    exact ((Equiv.Perm.sign τ.symm).isUnit.map (Int.castRingHom R)).mul hQ
  · rw [← h]
    calc _ = (L.submatrix id σ.symm).submatrix id σ * A.submatrix σ τ *
          (Q.submatrix τ.symm id).submatrix τ id := by
          rw [submatrix_mul_equiv, submatrix_mul_equiv]
          simp
      _ = _ := by simp

/-- One elimination step. If every entry of `A` is the multiple `A 0 0 * w k l` of the corner
entry, then unimodular row and column operations bring `A` to the block diagonal matrix
`diag(A 0 0, A 0 0 • B)`, where `B k l = w (k + 1) (l + 1) - w (k + 1) 0 * w 0 (l + 1)`. -/
private theorem exists_mul_mul_eq_cornerBlockSucc {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (w : Fin (n + 1) → Fin (n + 1) → R) (hw : ∀ k l, A k l = A 0 0 * w k l) :
    ∃ L Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R, L.det = 1 ∧ Q.det = 1 ∧
      L * A * Q = cornerBlockSucc (A 0 0)
        (A 0 0 • of fun k l ↦ w k.succ l.succ - w k.succ 0 * w 0 l.succ) := by
  -- subtract `w k 0` times row `0` from row `k`, and `w 0 l` times column `0` from column `l`
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    1 - of fun k m ↦ if m = 0 ∧ k ≠ 0 then w k 0 else 0
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    1 - of fun m l ↦ if m = 0 ∧ l ≠ 0 then w 0 l else 0
  have hL : L.det = 1 := by
    rw [det_of_isLowerTriangular L fun i j (hij : i < j) ↦ ?_]
    · simp [L]
    · simp [L, one_apply_ne hij.ne, Fin.ne_zero_of_lt hij]
  have hQ : Q.det = 1 := by
    rw [det_of_isUpperTriangular (M := Q) fun i j (hij : j < i) ↦ ?_]
    · simp [Q]
    · simp [Q, one_apply_ne hij.ne', Fin.ne_zero_of_lt hij]
  refine ⟨L, Q, hL, hQ, ?_⟩
  refine ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_)
  · simp [L, Q, Matrix.sub_mul, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [L, Q, Matrix.sub_mul, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply,
      hw 0 j.succ, mul_sub]
  · simp [L, Q, Matrix.sub_mul, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply,
      Fin.succ_ne_zero, hw i.succ 0, mul_comm]
  · simp [L, Q, Matrix.sub_mul, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, hw i.succ 0, hw 0 j.succ,
      hw i.succ j.succ]
    ring

/-- **Smith normal form over a valuation ring.** Every square matrix over a commutative ring in
which divisibility is total, for instance a valuation domain such as a discrete valuation ring, has
a Smith normal form: there are `L`, `Q` of unit determinant and a divisibility chain
`s₀ ∣ s₁ ∣ ⋯` with `L * A * Q = diagonal s`. Zero diagonal entries are allowed. -/
theorem exists_smith_normal_form_of_preValuationRing [PreValuationRing R] :
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
      ∃ (L Q : Matrix (Fin n) (Fin n) R) (s : Fin n → R), IsUnit L.det ∧ IsUnit Q.det ∧
        (∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j) ∧ L * A * Q = diagonal s
  | 0, _ => ⟨1, 1, 0, by simp, by simp, fun i ↦ i.elim0, Subsingleton.elim _ _⟩
  | n + 1, A => by
    -- move an entry dividing all the others to the corner
    obtain ⟨⟨i, j⟩, hij⟩ :=
      TauCeti.PreValuationRing.exists_forall_dvd fun p : Fin (n + 1) × Fin (n + 1) ↦ A p.1 p.2
    set A' := A.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j) with hA'
    have hdvd (k l : Fin (n + 1)) : A' 0 0 ∣ A' k l := by simpa [hA'] using hij (_, _)
    choose w hw using hdvd
    obtain ⟨L₁, Q₁, hL₁, hQ₁, h₁⟩ := exists_mul_mul_eq_cornerBlockSucc w hw
    -- a Smith normal form of the remaining block, scaled by the corner entry
    obtain ⟨L', Q', s', hL', hQ', hs', h'⟩ := exists_smith_normal_form_of_preValuationRing
      (of fun k l : Fin n ↦ w k.succ l.succ - w k.succ 0 * w 0 l.succ)
    refine exists_mul_mul_eq_of_mul_submatrix_mul_eq (Equiv.swap 0 i) (Equiv.swap 0 j)
      (L := cornerBlockSucc 1 L' * L₁) (Q := Q₁ * cornerBlockSucc 1 Q')
      (D := diagonal (Fin.cons (A' 0 0) (A' 0 0 • s'))) ?_ ?_ ?_ |>.imp fun L ⟨Q, h⟩ ↦
      ⟨Q, Fin.cons (A' 0 0) (A' 0 0 • s'), h.1, h.2.1, fun a b hab ↦ ?_, h.2.2⟩
    · rw [det_mul, hL₁, mul_one, det_cornerBlockSucc, one_mul]
      exact hL'
    · rw [det_mul, hQ₁, one_mul, det_cornerBlockSucc, one_mul]
      exact hQ'
    · calc cornerBlockSucc 1 L' * L₁ * A' * (Q₁ * cornerBlockSucc 1 Q')
          = cornerBlockSucc 1 L' * (L₁ * A' * Q₁) * cornerBlockSucc 1 Q' := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [h₁, cornerBlockSucc_mul_cornerBlockSucc, cornerBlockSucc_mul_cornerBlockSucc,
              Matrix.mul_smul, Matrix.smul_mul, h', ← cornerBlockSucc_diagonal]
            simp
    · induction a using Fin.cases with
      | zero => induction b using Fin.cases <;> simp
      | succ a =>
        induction b using Fin.cases with
        | zero => exact absurd hab (by simp [Fin.succ_ne_zero])
        | succ b => simpa using mul_dvd_mul_left _ (hs' (Fin.succ_le_succ_iff.1 hab))

/-- Over a commutative ring in which divisibility is total, for instance a valuation domain, every
square matrix indexed by a finite type is equivalent to a diagonal matrix by transformations of
unit determinant. Zero diagonal entries are allowed. -/
theorem exists_mul_mul_eq_diagonal_of_preValuationRing [PreValuationRing R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) :
    ∃ (L Q : Matrix ι ι R) (d : ι → R), IsUnit L.det ∧ IsUnit Q.det ∧
      L * A * Q = diagonal d := by
  let e := Fintype.equivFin ι
  obtain ⟨L, Q, s, hL, hQ, -, h⟩ := exists_smith_normal_form_of_preValuationRing (reindex e e A)
  refine ⟨L.submatrix e e, Q.submatrix e e, s ∘ e, by simpa using hL, by simpa using hQ, ?_⟩
  have := congrArg (submatrix · e e) h
  simp only [reindex_apply, submatrix_diagonal_equiv] at this
  rw [← this, ← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e]
  simp

end Matrix
