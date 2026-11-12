/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.LeftMulMatrixRpow
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Adjoint

/-!
# Real powers of the positive-form norm `g† g`

Let `Q` be a real quadratic form with a real orthonormal basis `b`, and `e_s` the ordered-product
basis of the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` for `1 ⊗ b`. The positive-form adjoint
`x† = complexConj (reverse x)` is the matrix adjoint of left multiplication in the basis `e_s`
(`CliffordAlgebra.toMatrix_mulLeft_complexConj_reverse`), and for a unit `g` the matrix of
`g† g` is strictly positive
(`CliffordAlgebra.isStrictlyPositive_leftMulMatrix_complexConj_reverse_mul_self`). Its real
powers `(g† g) ^ s` are therefore defined through the continuous functional calculus of that
matrix (`Algebra.leftMulMatrixRpow`).

This file proves that these real powers are self-adjoint, and computes the positive-form norm of
`g (g† g) ^ s`. These are the algebraic identities behind the polar decomposition
`g = (g (g† g) ^ (-1/2)) (g† g) ^ (1/2)`.

## Main results

* `CliffordAlgebra.complexConj_reverse_leftMulMatrixRpow_complexConj_reverse_mul_self`: the real
  powers of `g† g` are self-adjoint.
* `CliffordAlgebra.complexConj_reverse_mul_self_mul_leftMulMatrixRpow`: the positive-form norm of
  `g (g† g) ^ s` is `(g† g) ^ (2 s + 1)`, for a unit `g`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace CliffordAlgebra

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder I] [Fintype I]
  {Q : QuadraticForm ℝ V} {b : Module.Basis I ℝ V}

/-- **The real powers of `g† g` are self-adjoint**: `((g† g) ^ s)† = (g† g) ^ s`, where
`g† = complexConj (reverse g)` and the powers are taken through the matrix of `g† * g` in the
ordered-product basis of a real orthonormal basis. -/
theorem complexConj_reverse_leftMulMatrixRpow_complexConj_reverse_mul_self
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1)
    (g : CliffordAlgebra (Q.baseChange ℂ)) (s : ℝ) :
    complexConj Q (reverse (Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse g) * g) s)) =
      Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse g) * g) s := by
  apply Algebra.leftMulMatrix_injective (basis (Q.baseChange ℂ) (b.baseChange ℂ))
  rw [← Algebra.toMatrix_lmul_eq, toMatrix_mulLeft_complexConj_reverse hb hQ,
    Algebra.toMatrix_lmul_eq, Algebra.leftMulMatrix_leftMulMatrixRpow]
  exact CFC.rpow_nonneg.isSelfAdjoint

/-- The positive-form norm of `g (g† g) ^ s` is `(g† g) ^ (2 s + 1)`, for a unit `g`, where
`g† = complexConj (reverse g)` and the powers are taken through the matrix of `g† * g` in the
ordered-product basis of a real orthonormal basis. -/
theorem complexConj_reverse_mul_self_mul_leftMulMatrixRpow
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1)
    {g : CliffordAlgebra (Q.baseChange ℂ)} (hg : IsUnit g) (s : ℝ) :
    complexConj Q (reverse (g * Algebra.leftMulMatrixRpow
        (basis (Q.baseChange ℂ) (b.baseChange ℂ)) (complexConj Q (reverse g) * g) s)) *
        (g * Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
          (complexConj Q (reverse g) * g) s) =
      Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse g) * g) (s + 1 + s) := by
  have hpos := isStrictlyPositive_leftMulMatrix_complexConj_reverse_mul_self hb hQ hg
  have hu : IsUnit (complexConj Q (reverse g) * g) := by
    have hM := hpos.isUnit
    rw [← Algebra.toMatrix_lmul_eq, LinearMap.isUnit_toMatrix_iff] at hM
    exact Algebra.lmul_isUnit_iff.1 hM
  rw [Algebra.leftMulMatrixRpow_add hu, Algebra.leftMulMatrixRpow_add hu,
    Algebra.leftMulMatrixRpow_one hpos.nonneg, reverse.map_mul, map_mul,
    complexConj_reverse_leftMulMatrixRpow_complexConj_reverse_mul_self hb hQ]
  simp only [mul_assoc]

end CliffordAlgebra
