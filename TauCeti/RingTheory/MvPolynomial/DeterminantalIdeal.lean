/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal
import TauCeti.LinearAlgebra.Matrix.Determinant.PluckerRelation

/-!
# Plücker relations among generic minors

The shuffle and exchange relations among minors of a matrix, specialised to the generic matrix
`Matrix.mvPolynomialX`, are polynomial identities among the generic minors
`Matrix.mvPolynomialMinor`. They hold over every coefficient ring and are compatible with every
change of coefficients through `Matrix.map_mvPolynomialMinor`.

## Main results

* `Matrix.sum_sign_smul_mvPolynomialMinor_comp_mul_mvPolynomialMinor_comp_eq_zero`,
  `Matrix.sum_sign_smul_mvPolynomialMinor_mul_mvPolynomialMinor_eq_zero`: the shuffle relation
  among generic minors on columns `c ∘ j₁` and `c ∘ j₂`, and on the same columns.
* `Matrix.mvPolynomialMinor_comp_mul_mvPolynomialMinor_eq_sum`,
  `Matrix.mvPolynomialMinor_mul_mvPolynomialMinor_eq_sum`: the exchange relation among generic
  minors on nested columns `c ∘ j` and `c`, and on the same columns.
-/

public section

open Equiv

namespace Matrix

variable (R : Type*) [CommRing R] {m n t t₁ t₂ : Type*} [Fintype t] [DecidableEq t] [Fintype t₁]
  [DecidableEq t₁] [Fintype t₂] [DecidableEq t₂]
  {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂]

omit [DecidableEq t] in
/-- **The shuffle relation** among minors of the generic matrix `Matrix.mvPolynomialX` on the
columns `c ∘ j₁` and `c ∘ j₂`; see
`Matrix.sum_sign_smul_det_submatrix_comp_mul_det_submatrix_comp_eq_zero`. -/
theorem sum_sign_smul_mvPolynomialMinor_comp_mul_mvPolynomialMinor_comp_eq_zero (c : t → n)
    (j₁ : t₁ → t) (j₂ : t₂ → t) (e₁ : t₁ ≃ ι₁ ⊕ κ₁) (e₂ : t₂ ≃ ι₂ ⊕ κ₂) (α : ι₁ → m) (β : ι₂ → m)
    (γ : κ₁ ⊕ κ₂ → m) (hcard : Fintype.card t < Fintype.card κ₁ + Fintype.card κ₂)
    {T : Finset (Perm (κ₁ ⊕ κ₂))}
    (hT : Subgroup.IsComplement (T : Set (Perm (κ₁ ⊕ κ₂))) (Perm.sumCongrHom κ₁ κ₂).range) :
    ∑ σ ∈ T, Perm.sign σ •
      (mvPolynomialMinor R (Sum.elim α (γ ∘ σ ∘ Sum.inl) ∘ e₁) (c ∘ j₁) *
        mvPolynomialMinor R (Sum.elim β (γ ∘ σ ∘ Sum.inr) ∘ e₂) (c ∘ j₂)) = 0 := by
  simp only [mvPolynomialMinor_eq_det_submatrix]
  exact sum_sign_smul_det_submatrix_comp_mul_det_submatrix_comp_eq_zero _ c j₁ j₂ e₁ e₂ α β γ
    hcard hT

/-- **The shuffle relation** among minors of the generic matrix `Matrix.mvPolynomialX`; see
`Matrix.sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero`. -/
theorem sum_sign_smul_mvPolynomialMinor_mul_mvPolynomialMinor_eq_zero (c : t → n)
    (e₁ : t ≃ ι₁ ⊕ κ₁) (e₂ : t ≃ ι₂ ⊕ κ₂) (α : ι₁ → m) (β : ι₂ → m) (γ : κ₁ ⊕ κ₂ → m)
    (hcard : Fintype.card t < Fintype.card κ₁ + Fintype.card κ₂)
    {T : Finset (Perm (κ₁ ⊕ κ₂))}
    (hT : Subgroup.IsComplement (T : Set (Perm (κ₁ ⊕ κ₂))) (Perm.sumCongrHom κ₁ κ₂).range) :
    ∑ σ ∈ T, Perm.sign σ •
      (mvPolynomialMinor R (Sum.elim α (γ ∘ σ ∘ Sum.inl) ∘ e₁) c *
        mvPolynomialMinor R (Sum.elim β (γ ∘ σ ∘ Sum.inr) ∘ e₂) c) = 0 :=
  sum_sign_smul_mvPolynomialMinor_comp_mul_mvPolynomialMinor_comp_eq_zero R c id id e₁ e₂ α β γ
    hcard hT

/-- **The exchange relation** between a minor of the generic matrix `Matrix.mvPolynomialX` on the
columns `c ∘ j` and one on the columns `c`; see
`Matrix.det_submatrix_comp_mul_det_submatrix_eq_sum`. -/
theorem mvPolynomialMinor_comp_mul_mvPolynomialMinor_eq_sum (r : t₁ → m) (s : t → m) (c : t → n)
    (j : t₁ → t) (i : t₁) :
    mvPolynomialMinor R r (c ∘ j) * mvPolynomialMinor R s c =
      ∑ k, mvPolynomialMinor R (Function.update r i (s k)) (c ∘ j) *
        mvPolynomialMinor R (Function.update s k (r i)) c := by
  simp only [mvPolynomialMinor_eq_det_submatrix]
  exact det_submatrix_comp_mul_det_submatrix_eq_sum _ r s c j i

/-- **The exchange relation** among minors of the generic matrix `Matrix.mvPolynomialX`; see
`Matrix.det_submatrix_mul_det_submatrix_eq_sum`. -/
theorem mvPolynomialMinor_mul_mvPolynomialMinor_eq_sum (r s : t → m) (c : t → n) (i : t) :
    mvPolynomialMinor R r c * mvPolynomialMinor R s c =
      ∑ k, mvPolynomialMinor R (Function.update r i (s k)) c *
        mvPolynomialMinor R (Function.update s k (r i)) c :=
  mvPolynomialMinor_comp_mul_mvPolynomialMinor_eq_sum R r s c id i

end Matrix
