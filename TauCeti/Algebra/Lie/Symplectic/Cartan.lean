/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Matrix.NegConjTranspose
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.Symplectic.Basic

/-!
# Negative transpose on the symplectic Lie algebra

The symplectic Lie algebra is stable under transpose. Restricting the matrix Lie
automorphism `TauCeti.negTransposeLieEquiv` gives its involution `X ↦ -Xᵀ`.
On symplectic Lie matrices it is conjugation by `J`, just as inverse transpose is
conjugation by `J` on the symplectic group. The fixed and negated vectors are
respectively the skew-symmetric and symmetric symplectic Lie matrices. Over `ℝ` it is the
restriction `LieSubalgebra.restrictNegConjTranspose` of negative conjugate transpose
(`LieAlgebra.Symplectic.restrictNegConjTranspose_sp`), so it is an instance of the matrix Cartan
criterion of `TauCeti.Algebra.Lie.CartanInvolution.Matrix`.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition.
-/

public section

namespace LieAlgebra.Symplectic

open Matrix

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

variable (l R)

/-- The involutive Lie automorphism `X ↦ -Xᵀ` of the symplectic Lie algebra. -/
def cartanInvolution : sp l R ≃ₗ⁅R⁆ sp l R :=
  (sp l R).restrictNegTranspose fun _ ↦ transpose_mem_sp

variable {l R}

/-- The matrix value of the symplectic Lie involution is negative transpose. -/
@[simp]
theorem coe_cartanInvolution (X : sp l R) :
    (cartanInvolution l R X : Matrix (l ⊕ l) (l ⊕ l) R) = -(X : Matrix _ _ R)ᵀ := by
  simp [cartanInvolution]

/-- Applying the symplectic Lie involution twice gives the original vector. -/
@[simp]
theorem cartanInvolution_cartanInvolution (X : sp l R) :
    cartanInvolution l R (cartanInvolution l R X) = X :=
  LieSubalgebra.restrictNegTranspose_restrictNegTranspose _ _ X

/-- The symplectic Lie involution is its own inverse. -/
@[simp]
theorem cartanInvolution_symm : (cartanInvolution l R).symm = cartanInvolution l R :=
  LieSubalgebra.restrictNegTranspose_symm _ _

/-- Fixed vectors of the Lie involution are the skew-symmetric symplectic Lie matrices. -/
@[simp]
theorem cartanInvolution_eq_self_iff (X : sp l R) :
    cartanInvolution l R X = X ↔
      (X : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = -(X : Matrix (l ⊕ l) (l ⊕ l) R) := by
  rw [← Subtype.coe_inj, coe_cartanInvolution, neg_eq_iff_eq_neg]

/-- Negated vectors of the Lie involution are the symmetric symplectic Lie matrices. -/
@[simp]
theorem cartanInvolution_eq_neg_iff (X : sp l R) :
    cartanInvolution l R X = -X ↔ (X : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = X := by
  rw [← Subtype.coe_inj, coe_cartanInvolution]
  exact neg_inj

/-- On the real symplectic Lie algebra, `X ↦ -Xᴴ` is `LieAlgebra.Symplectic.cartanInvolution`. -/
theorem restrictNegConjTranspose_sp :
    (sp l ℝ).restrictNegConjTranspose (fun _ ↦ conjTranspose_mem_sp) = cartanInvolution l ℝ :=
  LieEquiv.ext fun X ↦ Subtype.ext <| by
    rw [LieSubalgebra.coe_restrictNegConjTranspose_apply, coe_cartanInvolution,
      conjTranspose_eq_transpose_of_trivial]

end LieAlgebra.Symplectic
