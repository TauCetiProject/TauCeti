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

* `Matrix.sum_sign_smul_mvPolynomialMinor_mul_mvPolynomialMinor_eq_zero`: the shuffle relation
  among generic minors.
* `Matrix.mvPolynomialMinor_mul_mvPolynomialMinor_eq_sum`: the exchange relation among generic
  minors.
-/

public section

open Equiv

namespace Matrix

variable {R : Type*} [CommRing R] {m n t : Type*} [Fintype t] [DecidableEq t]
  {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂]

/-- **The shuffle relation** among minors of the generic matrix `Matrix.mvPolynomialX`; see
`Matrix.sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero`. -/
theorem sum_sign_smul_mvPolynomialMinor_mul_mvPolynomialMinor_eq_zero (c : t → n)
    (e₁ : t ≃ ι₁ ⊕ κ₁) (e₂ : t ≃ ι₂ ⊕ κ₂) (α : ι₁ → m) (β : ι₂ → m) (γ : κ₁ ⊕ κ₂ → m)
    (hcard : Fintype.card t < Fintype.card κ₁ + Fintype.card κ₂)
    {T : Finset (Perm (κ₁ ⊕ κ₂))}
    (hT : Subgroup.IsComplement (T : Set (Perm (κ₁ ⊕ κ₂))) (Perm.sumCongrHom κ₁ κ₂).range) :
    ∑ σ ∈ T, Perm.sign σ •
      (mvPolynomialMinor R (Sum.elim α (γ ∘ σ ∘ Sum.inl) ∘ e₁) c *
        mvPolynomialMinor R (Sum.elim β (γ ∘ σ ∘ Sum.inr) ∘ e₂) c) = 0 := by
  simp only [mvPolynomialMinor_eq_det_submatrix]
  exact sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero _ c e₁ e₂ α β γ hcard hT

/-- **The exchange relation** among minors of the generic matrix `Matrix.mvPolynomialX`; see
`Matrix.det_submatrix_mul_det_submatrix_eq_sum`. -/
theorem mvPolynomialMinor_mul_mvPolynomialMinor_eq_sum (r s : t → m) (c : t → n) (i : t) :
    mvPolynomialMinor R r c * mvPolynomialMinor R s c =
      ∑ j, mvPolynomialMinor R (Function.update r i (s j)) c *
        mvPolynomialMinor R (Function.update s j (r i)) c := by
  simp only [mvPolynomialMinor_eq_det_submatrix]
  exact det_submatrix_mul_det_submatrix_eq_sum _ r s c i

end Matrix
