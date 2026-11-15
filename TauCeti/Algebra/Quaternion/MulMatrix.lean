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

Since `1, i, j, k` is a basis, an `R`-linear endomorphism `D` of any quaternion algebra
`ℍ[R,c₁,c₂,c₃]` is a left multiplication exactly when `D i = D 1 * i`, `D j = D 1 * j` and
`D k = D 1 * k`, the multiplier then being `D 1`, and a right multiplication exactly when
`D i = i * D 1`, `D j = j * D 1` and `D k = k * D 1`. For `ℍ[R]`, write `D q = K + iL + jM + kN`
and `K_t, K_x, K_y, K_z` for the coordinates `re` of `D 1, D i, D j, D k`, and likewise for
`L, M, N` with `imI, imJ, imK`. Expanding the products with the matrices above turns these
conditions into twelve component equations for each side

```text
Lₐ:  K_t = L_x = M_y = N_z,  K_x = -L_t = M_z = -N_y,
     K_y = -L_z = -M_t = N_x,  K_z = L_y = -M_x = -N_t;
Rₐ:  K_t = L_x = M_y = N_z,  K_x = -L_t = -M_z = N_y,
     K_y = L_z = -M_t = -N_x,  K_z = -L_y = M_x = -N_t.
```

For a real Fréchet derivative these entries are the partial derivatives of the four real
component functions of a function `ℍ → ℍ`; see `TauCeti.Analysis.Quaternion.PartialDeriv`.

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
* `QuaternionAlgebra.exists_eq_mulLeft_iff`, `QuaternionAlgebra.exists_eq_mulRight_iff`: a linear
  endomorphism of any quaternion algebra `ℍ[R,c₁,c₂,c₃]` is a left (right) multiplication exactly
  when it is left (right) multiplication by its value at `1` on `i`, `j` and `k`.
* `Quaternion.exists_eq_mulLeft_iff_components`, `Quaternion.exists_eq_mulRight_iff_components`:
  the component equations cutting out the two multiplication subspaces.

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

namespace QuaternionAlgebra

variable {c₁ c₂ c₃ : R}

/-- An `R`-linear endomorphism `D` of the quaternion algebra `ℍ[R,c₁,c₂,c₃]` is a left
multiplication `q ↦ a * q` exactly when it agrees with left multiplication by `D 1` on the basis
elements `i`, `j` and `k` of `basisOneIJK`; the multiplier is then `a = D 1`. -/
theorem exists_eq_mulLeft_iff {D : ℍ[R,c₁,c₂,c₃] →ₗ[R] ℍ[R,c₁,c₂,c₃]} :
    (∃ a, D = LinearMap.mulLeft R a) ↔
      D ⟨0, 1, 0, 0⟩ = D 1 * ⟨0, 1, 0, 0⟩ ∧ D ⟨0, 0, 1, 0⟩ = D 1 * ⟨0, 0, 1, 0⟩ ∧
        D ⟨0, 0, 0, 1⟩ = D 1 * ⟨0, 0, 0, 1⟩ := by
  refine ⟨fun ⟨a, ha⟩ ↦ by simp [ha], fun ⟨hi, hj, hk⟩ ↦ ⟨D 1, ?_⟩⟩
  have h1 : (⟨1, 0, 0, 0⟩ : ℍ[R,c₁,c₂,c₃]) = 1 := (rfl)
  refine (basisOneIJK c₁ c₂ c₃).ext fun n ↦ ?_
  fin_cases n <;> simp [basisOneIJK, h1, hi, hj, hk]

/-- An `R`-linear endomorphism `D` of the quaternion algebra `ℍ[R,c₁,c₂,c₃]` is a right
multiplication `q ↦ q * a` exactly when it agrees with right multiplication by `D 1` on the basis
elements `i`, `j` and `k` of `basisOneIJK`; the multiplier is then `a = D 1`. -/
theorem exists_eq_mulRight_iff {D : ℍ[R,c₁,c₂,c₃] →ₗ[R] ℍ[R,c₁,c₂,c₃]} :
    (∃ a, D = LinearMap.mulRight R a) ↔
      D ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * D 1 ∧ D ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * D 1 ∧
        D ⟨0, 0, 0, 1⟩ = ⟨0, 0, 0, 1⟩ * D 1 := by
  refine ⟨fun ⟨a, ha⟩ ↦ by simp [ha], fun ⟨hi, hj, hk⟩ ↦ ⟨D 1, ?_⟩⟩
  have h1 : (⟨1, 0, 0, 0⟩ : ℍ[R,c₁,c₂,c₃]) = 1 := (rfl)
  refine (basisOneIJK c₁ c₂ c₃).ext fun n ↦ ?_
  fin_cases n <;> simp [basisOneIJK, h1, hi, hj, hk]

end QuaternionAlgebra

namespace Quaternion

/-- The component equations of the left multiplication subspace. Write `D q = K + iL + jM + kN`
and let the subscripts `t, x, y, z` denote evaluation at `1, i, j, k`. Then `D` is a left
multiplication exactly when `K_t = L_x = M_y = N_z`, `K_x = -L_t = M_z = -N_y`,
`K_y = -L_z = -M_t = N_x` and `K_z = L_y = -M_x = -N_t`. -/
theorem exists_eq_mulLeft_iff_components {D : ℍ[R] →ₗ[R] ℍ[R]} :
    (∃ a, D = LinearMap.mulLeft R a) ↔
      ((D 1).re = (D ⟨0, 1, 0, 0⟩).imI ∧ (D ⟨0, 1, 0, 0⟩).imI = (D ⟨0, 0, 1, 0⟩).imJ ∧
        (D ⟨0, 0, 1, 0⟩).imJ = (D ⟨0, 0, 0, 1⟩).imK) ∧
      ((D ⟨0, 1, 0, 0⟩).re = -(D 1).imI ∧ -(D 1).imI = (D ⟨0, 0, 0, 1⟩).imJ ∧
        (D ⟨0, 0, 0, 1⟩).imJ = -(D ⟨0, 0, 1, 0⟩).imK) ∧
      ((D ⟨0, 0, 1, 0⟩).re = -(D ⟨0, 0, 0, 1⟩).imI ∧ -(D ⟨0, 0, 0, 1⟩).imI = -(D 1).imJ ∧
        -(D 1).imJ = (D ⟨0, 1, 0, 0⟩).imK) ∧
      ((D ⟨0, 0, 0, 1⟩).re = (D ⟨0, 0, 1, 0⟩).imI ∧
        (D ⟨0, 0, 1, 0⟩).imI = -(D ⟨0, 1, 0, 0⟩).imJ ∧
        -(D ⟨0, 1, 0, 0⟩).imJ = -(D 1).imK) := by
  rw [QuaternionAlgebra.exists_eq_mulLeft_iff]
  simp only [QuaternionAlgebra.ext_iff, re_mul, imI_mul, imJ_mul, imK_mul]
  grind

/-- The component equations of the right multiplication subspace. Write `D q = K + iL + jM + kN`
and let the subscripts `t, x, y, z` denote evaluation at `1, i, j, k`. Then `D` is a right
multiplication exactly when `K_t = L_x = M_y = N_z`, `K_x = -L_t = -M_z = N_y`,
`K_y = L_z = -M_t = -N_x` and `K_z = -L_y = M_x = -N_t`. -/
theorem exists_eq_mulRight_iff_components {D : ℍ[R] →ₗ[R] ℍ[R]} :
    (∃ a, D = LinearMap.mulRight R a) ↔
      ((D 1).re = (D ⟨0, 1, 0, 0⟩).imI ∧ (D ⟨0, 1, 0, 0⟩).imI = (D ⟨0, 0, 1, 0⟩).imJ ∧
        (D ⟨0, 0, 1, 0⟩).imJ = (D ⟨0, 0, 0, 1⟩).imK) ∧
      ((D ⟨0, 1, 0, 0⟩).re = -(D 1).imI ∧ -(D 1).imI = -(D ⟨0, 0, 0, 1⟩).imJ ∧
        -(D ⟨0, 0, 0, 1⟩).imJ = (D ⟨0, 0, 1, 0⟩).imK) ∧
      ((D ⟨0, 0, 1, 0⟩).re = (D ⟨0, 0, 0, 1⟩).imI ∧ (D ⟨0, 0, 0, 1⟩).imI = -(D 1).imJ ∧
        -(D 1).imJ = -(D ⟨0, 1, 0, 0⟩).imK) ∧
      ((D ⟨0, 0, 0, 1⟩).re = -(D ⟨0, 0, 1, 0⟩).imI ∧
        -(D ⟨0, 0, 1, 0⟩).imI = (D ⟨0, 1, 0, 0⟩).imJ ∧
        (D ⟨0, 1, 0, 0⟩).imJ = -(D 1).imK) := by
  rw [QuaternionAlgebra.exists_eq_mulRight_iff]
  simp only [QuaternionAlgebra.ext_iff, re_mul, imI_mul, imJ_mul, imK_mul]
  grind

end Quaternion
