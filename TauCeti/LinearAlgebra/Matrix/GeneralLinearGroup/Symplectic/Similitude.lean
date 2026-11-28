/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
import TauCeti.LinearAlgebra.Matrix.Congruence
import TauCeti.LinearAlgebra.Matrix.SymplecticMultiplier

/-!
# Similitudes of the standard alternating form in `Fin (m + m)` coordinates

A matrix `M` is a similitude of the standard alternating form `Jₘ = TauCeti.JFin m R` with
multiplier `r` when `M Jₘ Mᵀ = r Jₘ`. This file records two facts about this condition. Since
`Jₘ² = -1`, the row convention `M Jₘ Mᵀ = r Jₘ` and the column convention `Mᵀ Jₘ M = r Jₘ` agree
for a unit multiplier. In rank two, `m = 1`, the multiplier is forced to be the determinant: this
is `Matrix.transpose_mul_J_mul_eq_smul_iff` (`TauCeti.LinearAlgebra.Matrix.SymplecticMultiplier`),
read through the reindexing along `finSumFinEquiv` that defines `Jₘ`.

## Main results

* `TauCeti.transpose_mul_JFin_mul_eq_smul`: a similitude `M Jₘ Mᵀ = r Jₘ` with unit multiplier
  is one in the column form `Mᵀ Jₘ M = r Jₘ`.
* `TauCeti.mul_JFin_mul_transpose_eq_smul_iff`: the similitude condition read in
  `Fin m ⊕ Fin m` coordinates.
* `TauCeti.mul_JFin_one_mul_transpose_eq_smul_iff` and
  `Matrix.mul_JFin_one_mul_transpose_eq_det_smul`: in rank two, `M J₁ Mᵀ = d J₁` exactly when
  `det M = d`.
-/

public section

open Matrix

namespace TauCeti

variable {m : ℕ} {R : Type*} [CommRing R]

/-- **The column form of the similitude condition**: if `M Jₘ Mᵀ = r Jₘ` with `r` a unit, then
`Mᵀ Jₘ M = r Jₘ`. -/
theorem transpose_mul_JFin_mul_eq_smul {M : Matrix (Fin (m + m)) (Fin (m + m)) R} (r : Rˣ)
    (h : M * JFin m R * Mᵀ = (r : R) • JFin m R) :
    Mᵀ * JFin m R * M = (r : R) • JFin m R :=
  Matrix.transpose_mul_mul_eq_smul_of_mul_mul_transpose_eq_smul (JFin_mul_self m R) r h

/-- The similitude condition `M Jₘ Mᵀ = d Jₘ` is Mathlib's `Aᵀ J A = d J` for `A = Mᵀ` read in
`Fin m ⊕ Fin m` coordinates. -/
theorem mul_JFin_mul_transpose_eq_smul_iff {M : Matrix (Fin (m + m)) (Fin (m + m)) R} {d : R} :
    M * JFin m R * Mᵀ = d • JFin m R ↔
      (Mᵀ.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * J (Fin m) R *
          Mᵀ.submatrix finSumFinEquiv finSumFinEquiv = d • J (Fin m) R := by
  rw [Matrix.transpose_submatrix, Matrix.transpose_transpose, ← JFin_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  -- `(d • X).submatrix e e` is `d • X.submatrix e e` by `Matrix.submatrix_smul`, which is `rfl`.
  exact (Matrix.submatrix_injective finSumFinEquiv.surjective
    finSumFinEquiv.surjective).eq_iff.symm

/-- **In rank two the similitude multiplier is the determinant**: `M J₁ Mᵀ = d J₁` exactly when
`det M = d`. This is `Matrix.transpose_mul_J_mul_eq_smul_iff` read through the reindexing. -/
theorem mul_JFin_one_mul_transpose_eq_smul_iff
    {M : Matrix (Fin (1 + 1)) (Fin (1 + 1)) R} {d : R} :
    M * JFin 1 R * Mᵀ = d • JFin 1 R ↔ M.det = d := by
  rw [mul_JFin_mul_transpose_eq_smul_iff, Matrix.transpose_mul_J_mul_eq_smul_iff,
    Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

/-- For a `2 × 2` matrix, `M J₁ Mᵀ = det(M) J₁`. -/
theorem _root_.Matrix.mul_JFin_one_mul_transpose_eq_det_smul
    (M : Matrix (Fin (1 + 1)) (Fin (1 + 1)) R) :
    M * JFin 1 R * Mᵀ = M.det • JFin 1 R :=
  mul_JFin_one_mul_transpose_eq_smul_iff.mpr rfl

end TauCeti
