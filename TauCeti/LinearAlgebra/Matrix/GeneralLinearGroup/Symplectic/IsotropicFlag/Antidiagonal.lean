/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.IsotropicFlag.Basic

/-!
# The antidiagonal symplectic form

Flag varieties and their Schubert cells are usually written for the symplectic group of the
antidiagonal form

```text
           [  0   H ]
    Q  =   [        ]        (`TauCeti.JAntidiag m R`),
           [ -H   0 ]
```

on `R^(m + m)`, where `H` is the `m × m` matrix with ones on its antidiagonal. With the basis
vectors `u_i = e_i` and `f_i = e_(2m-1-i)` (zero-based) one has `Q(u_i, f_j) = δ_ij`, and the
standard isotropic flag `⟨u_0⟩ ⊂ ⟨u_0, u_1⟩ ⊂ ⋯` is spanned by initial segments of the standard
basis: its stabilizer consists of the symplectic matrices that are upper triangular in these
coordinates (`TauCeti.GLSymplecticFin.IsotropicFlag.matrixSubgroup`). The symplectic carriers are
instead built on Mathlib's `Matrix.J`, the form `[[0, -1], [1, 0]]` on `Fin m ⊕ Fin m`, and on its
transport `TauCeti.JFin` to `Fin (m + m)`.

This file compares the two conventions. The reindexing `TauCeti.antidiagEquiv m`, sending
`inl i` to `u_i` and `inr i` to `f_i`, carries `Q` to `-Matrix.J` (the global negation records
`Q(u_i, f_i) = 1` against `J(inl i, inr i) = -1`), and equivalently `Q` is `-JFin` permuted by the
self-dual flag order `TauCeti.GLSymplecticFin.IsotropicFlag.flagOrder`. Hence a matrix preserves
`Q` exactly when its reindexing is a symplectic matrix in Mathlib's sense, in the column form
`gᵀ Q g = Q` of `SymplecticGroup.mem_iff'` as well as in the row form; on the general linear group
this identifies the matrices preserving `Q` with `TauCeti.GLSymplecticFin` after the flag-order
reindexing.

For `m = r + s`, the reordering `TauCeti.isotropicBlockEquiv r s` lists the basis as
`u_0, …, u_(r-1); u_r, …, u_(m-1), f_r, …, f_(m-1); f_0, …, f_(r-1)`, the basis adapted to the
isotropic subspace `U = ⟨u_0, …, u_(r-1)⟩` and its orthogonal `U ⊕ W₀`. Writing `C` for the matrix
with these columns, `Cᵀ Q C` is the block form

```text
               [  0    0    1 ]
    J_(r,s) =  [  0    J₀   0 ],     J₀ = [[0, 1], [-1, 0]] = -Matrix.J (Fin s) R,
               [ -1    0    0 ]
```

the coordinates in which the stabilizer of `U` is studied as a block-triangular parabolic.
Everything holds over an arbitrary commutative ring, including characteristic `2` and the cases
`r = 0`, `s = 0` and `m = 0`.

## Main declarations

* `TauCeti.JAntidiag`: the antidiagonal alternating form `[[0, H], [-H, 0]]` on `Fin (m + m)`.
* `TauCeti.antidiagEquiv`: the reindexing `Fin m ⊕ Fin m ≃ Fin (m + m)`, `inl i ↦ i`,
  `inr i ↦ 2m - 1 - i`.
* `TauCeti.isotropicBlockEquiv`: the reordering of `Fin (r + s) ⊕ Fin (r + s)` adapted to a
  rank-`r` isotropic subspace.

## Main results

* `TauCeti.JAntidiag_submatrix_antidiagEquiv`: `Q` reindexed by `antidiagEquiv` is `-Matrix.J`.
* `TauCeti.JAntidiag_eq_neg_submatrix_flagOrder`: `Q` is `-JFin` permuted by the flag order.
* `TauCeti.transpose_mul_JAntidiag_mul_self_iff` and `TauCeti.mul_JAntidiag_mul_transpose_iff`: a
  matrix preserves `Q` exactly when its reindexing lies in `Matrix.symplecticGroup`.
* `TauCeti.GLSymplecticFin.mem_iff_JAntidiag`: membership in `GLSymplecticFin` is preservation of
  `Q` after the flag-order reindexing.
* `TauCeti.neg_J_submatrix_isotropicBlockEquiv` and
  `TauCeti.toMatrix_mul_JAntidiag_mul_transpose_isotropicBlockEquiv`: the Gram matrix of the
  reordered basis is `J_(r,s)`, in sum coordinates and as `Cᵀ Q C` in `Fin (m + m)` coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6 (symplectic groups and isotropic flags).
-/

public section

open Matrix

namespace TauCeti

open GLSymplecticFin.IsotropicFlag

variable (m : ℕ) (R : Type*) [CommRing R]

/-! ### The antidiagonal form and its reindexing -/

/-- The **antidiagonal alternating form** `[[0, H], [-H, 0]]` on `Fin (m + m)`, where `H` is the
`m × m` matrix with ones on its antidiagonal. With `u_i = e_i` and `f_i = e_(2m-1-i)` it pairs
`u_i` with `f_j` to `δ_ij` (`TauCeti.JAntidiag_castAdd_rev_addNat`). -/
def JAntidiag : Matrix (Fin (m + m)) (Fin (m + m)) R :=
  (fromBlocks 0 (of fun i j : Fin m ↦ if i = j.rev then 1 else 0)
    (-of fun i j : Fin m ↦ if i = j.rev then 1 else 0) 0).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm

/-- The reindexing from Mathlib's symplectic coordinates `Fin m ⊕ Fin m` to the antidiagonal
coordinates: `inl i` goes to `u_i = e_i` and `inr i` to `f_i = e_(2m-1-i)`. It is
`finSumFinEquiv` followed by the self-dual flag order. -/
def antidiagEquiv : Fin m ⊕ Fin m ≃ Fin (m + m) :=
  finSumFinEquiv.trans (flagOrder m)

variable {m}

@[simp]
theorem antidiagEquiv_inl (i : Fin m) : antidiagEquiv m (Sum.inl i) = i.castAdd m := by
  simp [antidiagEquiv]

@[simp]
theorem antidiagEquiv_inr (i : Fin m) : antidiagEquiv m (Sum.inr i) = i.rev.addNat m := by
  simp [antidiagEquiv, Fin.natAdd_eq_addNat]

@[simp]
theorem antidiagEquiv_symm_castAdd (i : Fin m) :
    (antidiagEquiv m).symm (i.castAdd m) = Sum.inl i := by
  rw [Equiv.symm_apply_eq, antidiagEquiv_inl]

@[simp]
theorem antidiagEquiv_symm_addNat (i : Fin m) :
    (antidiagEquiv m).symm (i.addNat m) = Sum.inr i.rev := by
  rw [Equiv.symm_apply_eq, antidiagEquiv_inr, Fin.rev_rev]

/-- The self-dual flag order undoes the reversal in `antidiagEquiv`. -/
@[simp]
theorem flagOrder_antidiagEquiv (x : Fin m ⊕ Fin m) :
    flagOrder m (antidiagEquiv m x) = finSumFinEquiv x := by
  rw [← flagOrder_symm, antidiagEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp]
theorem JAntidiag_castAdd_castAdd (i j : Fin m) :
    JAntidiag m R (i.castAdd m) (j.castAdd m) = 0 := by
  simp [JAntidiag]

@[simp]
theorem JAntidiag_addNat_addNat (i j : Fin m) :
    JAntidiag m R (i.addNat m) (j.addNat m) = 0 := by
  simp [JAntidiag, ← Fin.natAdd_eq_addNat]

@[simp]
theorem JAntidiag_castAdd_addNat (i j : Fin m) :
    JAntidiag m R (i.castAdd m) (j.addNat m) = if i = j.rev then 1 else 0 := by
  simp [JAntidiag, ← Fin.natAdd_eq_addNat]

@[simp]
theorem JAntidiag_addNat_castAdd (i j : Fin m) :
    JAntidiag m R (i.addNat m) (j.castAdd m) = -if i = j.rev then 1 else 0 := by
  simp [JAntidiag, ← Fin.natAdd_eq_addNat]

/-- `Q(u_i, f_j) = δ_ij`. -/
theorem JAntidiag_castAdd_rev_addNat (i j : Fin m) :
    JAntidiag m R (i.castAdd m) (j.rev.addNat m) = if i = j then 1 else 0 := by
  simp

/-- `Q(f_i, u_j) = -δ_ij`. -/
theorem JAntidiag_rev_addNat_castAdd (i j : Fin m) :
    JAntidiag m R (i.rev.addNat m) (j.castAdd m) = -if i = j then 1 else 0 := by
  simp [Fin.rev_eq_iff]

/-- **The antidiagonal form is `-Matrix.J` in Mathlib's coordinates.** Reindexed by
`antidiagEquiv`, which sends `inl i` to `u_i` and `inr i` to `f_i`, the form `Q` becomes `-J`:
`Q(u_i, f_i) = 1`, whereas `J(inl i, inr i) = -1`. -/
@[simp]
theorem JAntidiag_submatrix_antidiagEquiv :
    (JAntidiag m R).submatrix (antidiagEquiv m) (antidiagEquiv m) = -J (Fin m) R := by
  ext (i | i) (j | j) <;> simp [J, Matrix.one_apply]

/-- The antidiagonal form is `-Matrix.J` reindexed back along `antidiagEquiv`. -/
theorem JAntidiag_eq_submatrix :
    JAntidiag m R = (-J (Fin m) R).submatrix (antidiagEquiv m).symm (antidiagEquiv m).symm := by
  have h := congrArg (fun M ↦ M.submatrix (antidiagEquiv m).symm (antidiagEquiv m).symm)
    (JAntidiag_submatrix_antidiagEquiv (m := m) R)
  simpa only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] using h

/-- **The antidiagonal form is the negated `JFin` in the self-dual flag order.** -/
theorem JAntidiag_eq_neg_submatrix_flagOrder :
    JAntidiag m R = -(JFin m R).submatrix (flagOrder m) (flagOrder m) := by
  have h : ⇑(antidiagEquiv m).symm = finSumFinEquiv.symm ∘ flagOrder m := by
    rw [antidiagEquiv, Equiv.symm_trans, flagOrder_symm, Equiv.coe_trans]
  ext i j
  simp [JAntidiag_eq_submatrix, JFin_eq_submatrix, h]

/-- The antidiagonal form for `m = 1`: in the basis `(u₀, f₀)` its Gram matrix is
`[[0, 1], [-1, 0]] = -Matrix.J`. -/
theorem JAntidiag_one : JAntidiag 1 R = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [JAntidiag, finSumFinEquiv, Fin.addCases, fromBlocks]

/-- The antidiagonal form for `m = 2`, written out. -/
theorem JAntidiag_two :
    JAntidiag 2 R = !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [JAntidiag, finSumFinEquiv, Fin.addCases, fromBlocks]

/-- The antidiagonal form is antisymmetric. -/
@[simp]
theorem JAntidiag_transpose : (JAntidiag m R)ᵀ = -JAntidiag m R := by
  rw [JAntidiag_eq_submatrix, transpose_submatrix, transpose_neg, J_transpose]
  ext i j
  simp

/-- The antidiagonal form is invertible. -/
theorem isUnit_JAntidiag : IsUnit (JAntidiag m R) := by
  rw [JAntidiag_eq_submatrix, isUnit_submatrix_equiv]
  exact (isUnit_J (Fin m) R).neg

variable {R} in
/-- Entrywise application of a ring morphism, or of any map preserving addition and `1`, carries
the antidiagonal form to the antidiagonal form. -/
@[simp]
theorem JAntidiag_map {S F : Type*} [CommRing S] [FunLike F R S] [AddMonoidHomClass F R S]
    [OneHomClass F R S] (f : F) : (JAntidiag m R).map f = JAntidiag m S := by
  rw [JAntidiag_eq_submatrix, JAntidiag_eq_submatrix, ← submatrix_map,
    Matrix.map_neg _ (map_neg f), map_J]

/-! ### Comparison of the symplectic groups -/

variable {R}

/-- **A matrix preserves the antidiagonal form exactly when it is symplectic in Mathlib's
coordinates**, in the column form `gᵀ Q g = Q` of `SymplecticGroup.mem_iff'`. -/
theorem transpose_mul_JAntidiag_mul_self_iff {g : Matrix (Fin (m + m)) (Fin (m + m)) R} :
    gᵀ * JAntidiag m R * g = JAntidiag m R ↔
      g.submatrix (antidiagEquiv m) (antidiagEquiv m) ∈ symplecticGroup (Fin m) R := by
  set e := antidiagEquiv m
  have key : (g.submatrix e e)ᵀ * -J (Fin m) R * g.submatrix e e =
      (gᵀ * JAntidiag m R * g).submatrix e e := by
    rw [← JAntidiag_submatrix_antidiagEquiv, transpose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv]
  calc gᵀ * JAntidiag m R * g = JAntidiag m R
        ↔ (gᵀ * JAntidiag m R * g).submatrix e e = (JAntidiag m R).submatrix e e :=
          ((reindex e.symm e.symm).injective.eq_iff).symm
    _ ↔ (g.submatrix e e)ᵀ * -J (Fin m) R * g.submatrix e e = -J (Fin m) R := by
          rw [key, JAntidiag_submatrix_antidiagEquiv]
    _ ↔ _ := by rw [SymplecticGroup.mem_iff', Matrix.mul_neg, Matrix.neg_mul, neg_inj]

/-- A matrix preserves the antidiagonal form in the row form `g Q gᵀ = Q` exactly when it is
symplectic in Mathlib's coordinates. -/
theorem mul_JAntidiag_mul_transpose_iff {g : Matrix (Fin (m + m)) (Fin (m + m)) R} :
    g * JAntidiag m R * gᵀ = JAntidiag m R ↔
      g.submatrix (antidiagEquiv m) (antidiagEquiv m) ∈ symplecticGroup (Fin m) R := by
  rw [← SymplecticGroup.transpose_mem_iff, transpose_submatrix,
    ← transpose_mul_JAntidiag_mul_self_iff, transpose_transpose]

/-- **The `Fin`-indexed symplectic group in antidiagonal coordinates.** An invertible matrix lies
in `TauCeti.GLSymplecticFin` exactly when its reindexing by the self-dual flag order preserves the
antidiagonal form. -/
theorem GLSymplecticFin.mem_iff_JAntidiag {M : GL (Fin (m + m)) R} :
    M ∈ GLSymplecticFin m R ↔
      ((flagOrder m).reindexGL R M : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ * JAntidiag m R *
          ((flagOrder m).reindexGL R M : Matrix (Fin (m + m)) (Fin (m + m)) R) =
        JAntidiag m R := by
  rw [transpose_mul_JAntidiag_mul_self_iff, Equiv.coe_reindexGL, flagOrder_symm,
    submatrix_submatrix]
  have h : (flagOrder m ∘ antidiagEquiv m) = finSumFinEquiv := funext flagOrder_antidiagEquiv
  rw [h, GLSymplecticFin.mem_iff]
  exact ⟨submatrix_mem_symplecticGroup, mul_JFin_mul_transpose_of_submatrix_mem_symplecticGroup⟩

/-! ### The basis adapted to an isotropic subspace -/

variable (r s : ℕ)

/-- For `m = r + s`, the reordering of Mathlib's symplectic coordinates
`u_0, …, u_(m-1), f_0, …, f_(m-1)` (that is, `Fin m ⊕ Fin m`) as
`u_0, …, u_(r-1); u_r, …, u_(m-1), f_r, …, f_(m-1); f_0, …, f_(r-1)`: the basis adapted to the
isotropic subspace `⟨u_0, …, u_(r-1)⟩` and its orthogonal. -/
def isotropicBlockEquiv : Fin r ⊕ (Fin s ⊕ Fin s) ⊕ Fin r ≃ Fin (r + s) ⊕ Fin (r + s) :=
  ((Equiv.refl (Fin r)).sumCongr (Equiv.sumAssoc (Fin s) (Fin s) (Fin r))).trans <|
    (Equiv.sumAssoc (Fin r) (Fin s) (Fin s ⊕ Fin r)).symm.trans <|
      ((Equiv.refl _).sumCongr (Equiv.sumComm (Fin s) (Fin r))).trans <|
        finSumFinEquiv.sumCongr finSumFinEquiv

variable {r s}

@[simp]
theorem isotropicBlockEquiv_inl (i : Fin r) :
    isotropicBlockEquiv r s (Sum.inl i) = Sum.inl (i.castAdd s) := by
  simp [isotropicBlockEquiv]

@[simp]
theorem isotropicBlockEquiv_inr_inl_inl (j : Fin s) :
    isotropicBlockEquiv r s (Sum.inr (Sum.inl (Sum.inl j))) = Sum.inl (j.natAdd r) := by
  simp [isotropicBlockEquiv]

@[simp]
theorem isotropicBlockEquiv_inr_inl_inr (j : Fin s) :
    isotropicBlockEquiv r s (Sum.inr (Sum.inl (Sum.inr j))) = Sum.inr (j.natAdd r) := by
  simp [isotropicBlockEquiv]

@[simp]
theorem isotropicBlockEquiv_inr_inr (i : Fin r) :
    isotropicBlockEquiv r s (Sum.inr (Sum.inr i)) = Sum.inr (i.castAdd s) := by
  simp [isotropicBlockEquiv]

variable (R r s)

/-- **The Gram matrix of the basis adapted to a rank-`r` isotropic subspace**, in Mathlib's
coordinates: reindexed by `isotropicBlockEquiv r s`, the form `-Matrix.J` (the form with
`ω(u_i, f_i) = 1`) becomes `[[0, 0, 1], [0, J₀, 0], [-1, 0, 0]]` with `J₀ = -Matrix.J (Fin s) R`. -/
theorem neg_J_submatrix_isotropicBlockEquiv :
    (-J (Fin (r + s)) R).submatrix (isotropicBlockEquiv r s) (isotropicBlockEquiv r s) =
      fromBlocks 0 (fromCols 0 1) (fromRows 0 (-1)) (fromBlocks (-J (Fin s) R) 0 0 0) := by
  ext (i | (j | j) | i) (i' | (j' | j') | i') <;>
    simp [J, Matrix.one_apply, Fin.ext_iff] <;> omega

/-- The antidiagonal form in the basis adapted to a rank-`r` isotropic subspace, as a reindexing
of `Fin (m + m)`. -/
theorem JAntidiag_submatrix_isotropicBlockEquiv :
    (JAntidiag (r + s) R).submatrix (antidiagEquiv (r + s) ∘ isotropicBlockEquiv r s)
        (antidiagEquiv (r + s) ∘ isotropicBlockEquiv r s) =
      fromBlocks 0 (fromCols 0 1) (fromRows 0 (-1)) (fromBlocks (-J (Fin s) R) 0 0 0) := by
  rw [← submatrix_submatrix, JAntidiag_submatrix_antidiagEquiv,
    neg_J_submatrix_isotropicBlockEquiv]

/-- **`Cᵀ Q C = J_(r,s)`.** Let `P` be the permutation matrix of
`antidiagEquiv ∘ isotropicBlockEquiv`, so that `C = Pᵀ` is the matrix whose columns are the
antidiagonal basis vectors `u_0, …, u_(r-1); u_r, …, u_(m-1), f_r, …, f_(m-1); f_0, …, f_(r-1)`.
Then `Cᵀ Q C = P Q Pᵀ` is the block form `[[0, 0, 1], [0, J₀, 0], [-1, 0, 0]]` with
`J₀ = [[0, 1], [-1, 0]]`. -/
theorem toMatrix_mul_JAntidiag_mul_transpose_isotropicBlockEquiv :
    (((isotropicBlockEquiv r s).trans (antidiagEquiv (r + s))).toPEquiv.toMatrix :
        Matrix (Fin r ⊕ (Fin s ⊕ Fin s) ⊕ Fin r) (Fin ((r + s) + (r + s))) R) *
        JAntidiag (r + s) R *
        ((isotropicBlockEquiv r s).trans (antidiagEquiv (r + s))).toPEquiv.toMatrixᵀ =
      fromBlocks 0 (fromCols 0 1) (fromRows 0 (-1)) (fromBlocks (-J (Fin s) R) 0 0 0) := by
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix, Function.comp_id,
    Function.id_comp]
  exact JAntidiag_submatrix_isotropicBlockEquiv R r s

end TauCeti
