/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.Idempotents

/-!
# Multiplication matrices for an idempotent decomposition

The basis adapted to `B ≅ B/(1-e) × B/(e)` makes multiplication block diagonal.
This is the linear algebra used to compute traces on the two factors.

Adapted from `Jacobian/RingTheory/Kaehler/TraceIdempotent.lean`, accepted release
`baef7723da528551b7d2f93bd9a9a53303b04dbc`.
-/

public section

open Matrix

namespace Algebra

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {e : B}

/-- The basis of `B` adapted to the decomposition `B ≅ B ⧸ (1 - e) × B ⧸ (e)`. -/
noncomputable def idempotentBasis (he : IsIdempotentElem e) {ι₁ ι₂ : Type*}
    (b₁ : Module.Basis ι₁ R (B ⧸ Ideal.span {1 - e}))
    (b₂ : Module.Basis ι₂ R (B ⧸ Ideal.span {e})) : Module.Basis (ι₁ ⊕ ι₂) R B :=
  (b₁.prod b₂).map (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
    (sub_add_cancel 1 e) he.one_sub_mul_self).toLinearEquiv.symm

/-- The defining basis transport for the idempotent decomposition. -/
lemma idempotentBasis_def (he : IsIdempotentElem e) {ι₁ ι₂ : Type*}
    (b₁ : Module.Basis ι₁ R (B ⧸ Ideal.span {1 - e}))
    (b₂ : Module.Basis ι₂ R (B ⧸ Ideal.span {e})) :
    idempotentBasis he b₁ b₂ = (b₁.prod b₂).map
      (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
        (sub_add_cancel 1 e) he.one_sub_mul_self).toLinearEquiv.symm := (rfl)

/-- The matrix of multiplication in the basis adapted to `B ≅ B ⧸ (1 - e) × B ⧸ (e)` is block
diagonal. -/
lemma leftMulMatrix_idempotentBasis (he : IsIdempotentElem e) {ι₁ ι₂ : Type*} [Fintype ι₁]
    [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ R (B ⧸ Ideal.span {1 - e}))
    (b₂ : Module.Basis ι₂ R (B ⧸ Ideal.span {e})) (x : B) :
    leftMulMatrix (idempotentBasis he b₁ b₂) x =
      fromBlocks (leftMulMatrix b₁ (Ideal.Quotient.mk _ x)) 0 0
        (leftMulMatrix b₂ (Ideal.Quotient.mk _ x)) := by
  have hrepr (y : B) : (idempotentBasis he b₁ b₂).repr y =
      (b₁.prod b₂).repr ((AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
        (sub_add_cancel 1 e) he.one_sub_mul_self) y) := by
    simp [idempotentBasis_def]
  have hb (j : ι₁ ⊕ ι₂) : (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
      (sub_add_cancel 1 e) he.one_sub_mul_self) (idempotentBasis he b₁ b₂ j) =
      b₁.prod b₂ j := by
    simp [idempotentBasis_def]
  ext i j
  rw [leftMulMatrix_eq_repr_mul, hrepr, map_mul, hb]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr, leftMulMatrix_eq_repr_mul,
      AlgEquiv.prodQuotientOfIsIdempotentElem_apply]

end Algebra
