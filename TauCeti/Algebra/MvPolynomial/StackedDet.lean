/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Stacked determinant polynomials under two-sided matrix substitutions

For a commutative ring R and index types Φ, , N, L, consider the multivariate
polynomial ring MvPolynomial (Φ × N × L) R whose indeterminates represent the entries of a
family of N × L matrices x_τ (τ : Φ).

Given a constant matrix B : Matrix a L R and an equivalence e : a ⊕ N ≃ L, the *stacked
determinant* TauCeti.stackedDet τ B e is the determinant of B stacked above the variable
matrix x_τ, with columns ordered by e. Under the two-sided linear substitution
TauCeti.twoSidedMatrixSubst c g sending x_τ ↦ (c τ)ᵀ * x_τ * (g τ)ᵀ, the stacked determinant
for B * (g τ)ᵀ transforms to ((c τ).det * (g τ).det) • stackedDet τ B e, and products of
stacked determinants scale by ∏ τ, ((c τ).det * (g τ).det) ^ Fintype.card (ι τ).

## Main definitions

* TauCeti.stackedDet: determinant of a constant matrix stacked above a matrix of indeterminates.
* TauCeti.twoSidedMatrixSubst: the R-algebra endomorphism x_τ ↦ (c τ)ᵀ * x_τ * (g τ)ᵀ.
* TauCeti.stackedDetProd: finite product of stacked determinants indexed by τ : Φ and k : ι τ.

## Main results

* TauCeti.twoSidedMatrixSubst_one: substituting identity matrices is the identity endomorphism.
* TauCeti.twoSidedMatrixSubst_stackedDet: transformation of a single stacked determinant.
* TauCeti.twoSidedMatrixSubst_stackedDetProd: transformation of a product of stacked determinants.

## Provenance

Adapted from New.Rows.stackedDet (src/New/OneLift/ComparisonOperator/ExchangeData.lean) and
New.Rows.twoSidedSubst, New.Rows.stackedDetProd, New.Rows.twoSidedSubst_stackedDetProd
(src/New/OneLift/ComparisonOperator/DeterminantProducts.lean) of grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), generalized from ℂ to an arbitrary commutative
ring R.
-/

public section

open Matrix MvPolynomial

namespace TauCeti

variable {R Φ a N L : Type*} [CommRing R]

/-- The determinant of a constant matrix B : Matrix a L R stacked above the variable matrix x_τ
in MvPolynomial (Φ × N × L) R, with columns reindexed by e : a ⊕ N → L. -/
noncomputable def stackedDet [Fintype a] [DecidableEq a] [Fintype N] [DecidableEq N]
    (τ : Φ) (B : Matrix a L R) (e : a ⊕ N → L) : MvPolynomial (Φ × N × L) R :=
  (((B.map C).fromRows (Matrix.of fun i j ↦ X (τ, i, j))).submatrix id e).det

/-- The two-sided linear substitution x_τ ↦ (c τ)ᵀ * x_τ * (g τ)ᵀ on MvPolynomial (Φ × N × L) R. -/
noncomputable def twoSidedMatrixSubst [Fintype N] [Fintype L]
    (c : Φ → Matrix N N R) (g : Φ → Matrix L L R) :
    MvPolynomial (Φ × N × L) R →ₐ[R] MvPolynomial (Φ × N × L) R :=
  aeval (R := R) fun (p : Φ × N × L) ↦
    ∑ i : N, ∑ j : L, (c p.fst i p.snd.fst * g p.fst p.snd.snd j) • X (R := R) (p.fst, i, j)

/-- Product of stacked determinants ∏ τ, ∏ k : ι τ, stackedDet τ (M τ k) e. -/
noncomputable def stackedDetProd [Fintype Φ] [Fintype a] [DecidableEq a] [Fintype N] [DecidableEq N]
    {ι : Φ → Type*} [∀ τ, Fintype (ι τ)] (e : a ⊕ N → L) (M : (τ : Φ) → ι τ → Matrix a L R) :
    MvPolynomial (Φ × N × L) R :=
  ∏ τ : Φ, ∏ k : ι τ, stackedDet τ (M τ k) e

/-- Substituting identity matrices on both sides yields the identity endomorphism. -/
theorem twoSidedMatrixSubst_one [Fintype N] [DecidableEq N] [Fintype L] [DecidableEq L] :
    twoSidedMatrixSubst (R := R) (Φ := Φ) (fun _ ↦ (1 : Matrix N N R))
      (fun _ ↦ (1 : Matrix L L R)) =
      AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, i, j⟩
  simp [twoSidedMatrixSubst, Matrix.one_apply]

/-- Substituting x_τ ↦ (c τ)ᵀ * x_τ * (g τ)ᵀ sends stackedDet τ (B * (g τ)ᵀ) e to
((c τ).det * (g τ).det) • stackedDet τ B e. -/
theorem twoSidedMatrixSubst_stackedDet [Fintype a] [DecidableEq a] [Fintype N] [DecidableEq N]
    [Fintype L] [DecidableEq L] (e : a ⊕ N ≃ L) (c : Φ → Matrix N N R) (g : Φ → Matrix L L R)
    (τ : Φ) (B : Matrix a L R) :
    twoSidedMatrixSubst c g (stackedDet τ (B * (g τ)ᵀ) e) =
      ((c τ).det * (g τ).det) • stackedDet τ B e := by
  let A : Matrix (a ⊕ N) (a ⊕ N) (MvPolynomial (Φ × N × L) R) :=
    ((B.map C).fromRows (Matrix.of fun i j ↦ X (τ, i, j))).submatrix id e
  have hleft : twoSidedMatrixSubst c g (stackedDet τ (B * (g τ)ᵀ) e) =
      ((C.mapMatrix (Matrix.fromBlocks 1 0 0 (c τ)))ᵀ *
        (A * (C.mapMatrix ((g τ).submatrix e e))ᵀ)).det := by
    rw [stackedDet, AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i j ↦ ?_
    rcases i with i | i
    · simp [A, Matrix.mul_apply, Matrix.one_apply, ← e.sum_comp]
    · simp [A, twoSidedMatrixSubst, Matrix.mul_apply, Finset.mul_sum, mul_add, mul_assoc,
        mul_comm (X _), ← e.sum_comp, ← C_mul']
  rw [hleft, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
    ← RingHom.map_det, ← RingHom.map_det, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
    Matrix.det_submatrix_equiv_self, stackedDet]
  simp only [A, Algebra.smul_def, map_mul, C_eq_algebraMap]
  ring

/-- Substituting x_τ ↦ (c τ)ᵀ * x_τ * (g τ)ᵀ scales a product of stacked determinants for
M τ k * (g τ)ᵀ by ∏ τ, ((c τ).det * (g τ).det) ^ Fintype.card (ι τ). -/
theorem twoSidedMatrixSubst_stackedDetProd [Fintype Φ] [Fintype a] [DecidableEq a] [Fintype N]
    [DecidableEq N] [Fintype L] [DecidableEq L] {ι : Φ → Type*} [∀ τ, Fintype (ι τ)]
    (e : a ⊕ N ≃ L) (M : (τ : Φ) → ι τ → Matrix a L R) (c : Φ → Matrix N N R)
    (g : Φ → Matrix L L R) :
    twoSidedMatrixSubst c g (stackedDetProd e fun τ k ↦ M τ k * (g τ)ᵀ) =
      (∏ τ : Φ, ((c τ).det * (g τ).det) ^ Fintype.card (ι τ)) • stackedDetProd e M := by
  simp only [stackedDetProd, map_prod, twoSidedMatrixSubst_stackedDet, Finset.prod_smul,
    Finset.prod_const, Finset.card_univ]

end TauCeti
