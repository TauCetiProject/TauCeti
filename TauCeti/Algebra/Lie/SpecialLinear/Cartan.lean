/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.Matrix.NegTranspose

import TauCeti.Algebra.Lie.GeneralLinear.Basic

/-!
# Negative transpose on the special linear Lie algebra

The special linear Lie algebra `sl n R` is stable under negative transpose. Restricting the matrix
Lie automorphism `TauCeti.negTransposeLieEquiv` gives the involutive automorphism `X ↦ -Xᵀ`
(`LieAlgebra.SpecialLinear.cartanInvolution`) over every commutative ring. Its fixed vectors are the
skew-symmetric trace-zero matrices and its negated vectors are the symmetric trace-zero matrices.

## Main definitions

* `LieAlgebra.SpecialLinear.cartanInvolution`: the negative-transpose involution `X ↦ -Xᵀ` on
  `sl n R`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–2.
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n R)

/-- The involutive Lie automorphism `X ↦ -Xᵀ` of the special linear Lie algebra `sl n R`. -/
def cartanInvolution : sl n R ≃ₗ⁅R⁆ sl n R :=
  (TauCeti.negTransposeLieEquiv n R).ofSubalgebras (sl n R) (sl n R) <| by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      -- Expose the underlying function of `negTransposeLieEquiv` to apply its evaluation lemma.
      change TauCeti.negTransposeLieEquiv n R Y ∈ sl n R
      rw [TauCeti.negTransposeLieEquiv_apply, mem_sl_iff, trace_neg, trace_transpose,
        mem_sl_iff.mp hY, neg_zero]
    · intro hX
      refine ⟨-Xᵀ, ?_, by simp⟩
      rw [SetLike.mem_coe, LieSubalgebra.mem_toSubmodule, mem_sl_iff, trace_neg, trace_transpose,
        mem_sl_iff.mp hX, neg_zero]

variable {n R}

/-- The matrix value of `SpecialLinear.cartanInvolution` is negative transpose. -/
@[simp]
theorem coe_cartanInvolution (X : sl n R) :
    (cartanInvolution n R X : Matrix n n R) = -(X : Matrix n n R)ᵀ := by
  simp [cartanInvolution]

/-- Applying `SpecialLinear.cartanInvolution` twice returns the original matrix. -/
@[simp]
theorem cartanInvolution_cartanInvolution (X : sl n R) :
    cartanInvolution n R (cartanInvolution n R X) = X := by
  apply Subtype.ext
  simp

/-- `SpecialLinear.cartanInvolution` is its own inverse. -/
@[simp]
theorem cartanInvolution_symm : (cartanInvolution n R).symm = cartanInvolution n R := by
  apply LieEquiv.ext
  intro X
  rw [LieEquiv.symm_apply_eq, cartanInvolution_cartanInvolution]

/-- Fixed vectors of `SpecialLinear.cartanInvolution` are the skew-symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_self_iff (X : sl n R) :
    cartanInvolution n R X = X ↔ (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_cartanInvolution, neg_eq_iff_eq_neg]

/-- Negated vectors of `SpecialLinear.cartanInvolution` are the symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_neg_iff (X : sl n R) :
    cartanInvolution n R X = -X ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_cartanInvolution, NegMemClass.coe_neg]
  exact neg_inj

end LieAlgebra.SpecialLinear
