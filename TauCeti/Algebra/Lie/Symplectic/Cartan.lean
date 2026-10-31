/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.Symplectic.Basic

/-!
# Negative transpose on the symplectic Lie algebra

The symplectic Lie algebra is stable under transpose. Restricting the matrix Lie
automorphism `TauCeti.negTransposeLieEquiv` gives its involution `X ↦ -Xᵀ`.
On symplectic Lie matrices it is conjugation by `J`, just as inverse transpose is
conjugation by `J` on the symplectic group. The fixed and negated vectors are
respectively the skew-symmetric and symmetric symplectic Lie matrices.

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
  (TauCeti.negTransposeLieEquiv (l ⊕ l) R).ofSubalgebras (sp l R) (sp l R) (by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      -- Subalgebra images use the underlying Lie homomorphism. Expose its function
      -- so the public evaluation lemma for negative transpose applies.
      change TauCeti.negTransposeLieEquiv (l ⊕ l) R Y ∈ sp l R
      rw [TauCeti.negTransposeLieEquiv_apply]
      exact (sp l R).neg_mem (transpose_mem_sp hY)
    · intro hX
      refine ⟨-Xᵀ, (sp l R).neg_mem (transpose_mem_sp hX), ?_⟩
      simp)

variable {l R}

/-- The matrix value of the symplectic Lie involution is negative transpose. -/
@[simp]
theorem coe_cartanInvolution (X : sp l R) :
    (cartanInvolution l R X : Matrix (l ⊕ l) (l ⊕ l) R) = -(X : Matrix _ _ R)ᵀ := by
  simp [cartanInvolution]

/-- Applying the symplectic Lie involution twice gives the original vector. -/
@[simp]
theorem cartanInvolution_cartanInvolution (X : sp l R) :
    cartanInvolution l R (cartanInvolution l R X) = X := by
  apply Subtype.ext
  simp

/-- The symplectic Lie involution is its own inverse. -/
@[simp]
theorem cartanInvolution_symm : (cartanInvolution l R).symm = cartanInvolution l R := by
  apply LieEquiv.ext
  intro X
  rw [LieEquiv.symm_apply_eq, cartanInvolution_cartanInvolution]

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

end LieAlgebra.Symplectic
