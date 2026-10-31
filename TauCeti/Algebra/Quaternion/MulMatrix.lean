/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.RingTheory.Norm.Defs
import TauCeti.Algebra.Central.Quaternion

/-!
# The matrices of quaternion multiplication

For a quaternion `a = α + iβ + jγ + kδ` over a commutative ring `R`, left multiplication
`Lₐ : q ↦ a * q` and right multiplication `Rₐ : q ↦ q * a` are `R`-linear endomorphisms of the
free module `ℍ[R]`. This file computes their `4 × 4` matrices in the basis `1, i, j, k`, that is,
in the coordinate order `(re, imI, imJ, imK)` used for both input and output:

```text
Lₐ = [[ α, -β, -γ, -δ],        Rₐ = [[ α, -β, -γ, -δ],
      [ β,  α, -δ,  γ],              [ β,  α,  δ, -γ],
      [ γ,  δ,  α, -β],              [ γ, -δ,  α,  β],
      [ δ, -γ,  β,  α]]              [ δ,  γ, -β,  α]]
```

The two matrices share their first row and column and differ exactly in the signs of the six
off-diagonal entries of their lower right `3 × 3` blocks; once `2` is a regular element of `R`,
they agree exactly when `a` is real. Both determinants are the square of the norm
`normSq a = α² + β² + γ² + δ²`, so over `ℝ`, where `normSq a = ‖a‖ ^ 2`, they are `‖a‖ ^ 4`.

These matrices are the real coordinates of quaternionic linear algebra in four real variables:
the derivative of a function `ℍ → ℍ` with a one-sided quotient derivative is one of these
multiplication maps, and the determinant computes the Jacobian of `q ↦ a * q` and `q ↦ q * a` in
changes of variables.

Mathlib already supplies the rest of the matrix calculus: `Algebra.leftMulMatrix_mulVec_repr` and
`LinearMap.toMatrix_mulVec_repr` say that each matrix sends the coordinates of `q` to those of
`a * q` and `q * a`, and `LinearMap.mulLeft_mul`, `LinearMap.mulRight_mul` and
`LinearMap.commute_mulLeft_right` are the composition rules `Lₐ ∘ L_b = L_{ab}`,
`Rₐ ∘ R_b = R_{ba}` and `Lₐ ∘ R_b = R_b ∘ Lₐ`.

The computations follow Mathlib's treatment of `ℂ` over `ℝ`, `Algebra.leftMulMatrix_complex` and
`Algebra.norm_complex_apply`.

## Main results

* `Algebra.leftMulMatrix_quaternion`: the matrix of left multiplication.
* `Quaternion.toMatrix_mulRight`: the matrix of right multiplication.
* `Quaternion.toMatrix_mulRight_eq_leftMulMatrix_iff`: when `2` is regular in `R`, the two
  matrices agree exactly when `a` is real.
* `Quaternion.det_mulLeft`, `Quaternion.det_mulRight`, `Algebra.norm_quaternion_apply`: both
  determinants, and the algebra norm `ℍ[R] → R`, are `normSq a ^ 2`.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.1, for the multiplication rules and the
  multiplicativity of the norm.
-/

public section

open Quaternion

variable {R : Type*} [CommRing R]

/-- The matrix of left multiplication by a quaternion `a` in the basis `1, i, j, k`. -/
theorem Algebra.leftMulMatrix_quaternion (a : ℍ[R]) :
    Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1)) a =
      !![a.re, -a.imI, -a.imJ, -a.imK;
         a.imI, a.re, -a.imK, a.imJ;
         a.imJ, a.imK, a.re, -a.imI;
         a.imK, -a.imJ, a.imI, a.re] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, QuaternionAlgebra.coe_basisOneIJK_repr]
  fin_cases i <;> fin_cases j <;> simp [QuaternionAlgebra.basisOneIJK]

namespace Quaternion

/-- The matrix of right multiplication by a quaternion `a` in the basis `1, i, j, k`. It differs
from `Algebra.leftMulMatrix_quaternion` by the signs of the six entries of the lower right
`3 × 3` block off its diagonal. -/
theorem toMatrix_mulRight (a : ℍ[R]) :
    LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1))
        (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1)) (LinearMap.mulRight R a) =
      !![a.re, -a.imI, -a.imJ, -a.imK;
         a.imI, a.re, a.imK, -a.imJ;
         a.imJ, -a.imK, a.re, a.imI;
         a.imK, a.imJ, -a.imI, a.re] := by
  ext i j
  rw [LinearMap.toMatrix_apply, QuaternionAlgebra.coe_basisOneIJK_repr]
  fin_cases i <;> fin_cases j <;> simp [QuaternionAlgebra.basisOneIJK]

/-- When `2` is a regular element of `R`, the matrices of right and left multiplication by a
quaternion `a` agree exactly when `a` is real. Without the hypothesis this fails: in
characteristic two `ℍ[R]` is commutative, so the two matrices always agree. -/
theorem toMatrix_mulRight_eq_leftMulMatrix_iff (h2 : IsLeftRegular (2 : R)) (a : ℍ[R]) :
    LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1))
        (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1)) (LinearMap.mulRight R a) =
      Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1)) a ↔
      a = a.re := by
  rw [← Algebra.toMatrix_lmul_eq, (LinearMap.toMatrix _ _).injective.eq_iff, LinearMap.ext_iff]
  simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
  rw [← Subalgebra.mem_center_iff (R := R) (A := ℍ[R]), TauCeti.Quaternion.center_eq_bot h2,
    Algebra.mem_bot]
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · intro h
    exact ⟨a.re, h.symm⟩

/-- The determinant of left multiplication by a quaternion `a` is `normSq a ^ 2`; over `ℝ` this
is `‖a‖ ^ 4`. -/
@[simp]
theorem det_mulLeft (a : ℍ[R]) : LinearMap.det (LinearMap.mulLeft R a) = normSq a ^ 2 := by
  rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1)),
    Algebra.toMatrix_lmul_eq, Algebra.leftMulMatrix_quaternion]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, normSq_def']
  ring

/-- The determinant of right multiplication by a quaternion `a` is `normSq a ^ 2`; over `ℝ` this
is `‖a‖ ^ 4`. -/
@[simp]
theorem det_mulRight (a : ℍ[R]) : LinearMap.det (LinearMap.mulRight R a) = normSq a ^ 2 := by
  rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1)),
    toMatrix_mulRight]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, normSq_def']
  ring

end Quaternion

/-- The algebra norm `ℍ[R] → R`, the determinant of left multiplication, is the square of the
quaternion norm `normSq`. -/
@[simp]
theorem Algebra.norm_quaternion_apply (a : ℍ[R]) : Algebra.norm R a = normSq a ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1)),
    ← Algebra.toMatrix_lmul_eq, LinearMap.det_toMatrix, Quaternion.det_mulLeft]
