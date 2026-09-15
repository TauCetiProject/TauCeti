/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Module

/-!
# The congruence of a matrix by a quadratic exponential

A divided-power exponential of a nilpotent matrix truncated after the quadratic term is
`1 + t N + t² P`. The congruence of a fixed matrix `C` by it,

```text
(1 + t N + t² P) C (1 + t N + t² P)ᵀ,
```

expands into a polynomial of degree four in `t` whose coefficients are matrix expressions in `N`,
`P` and `C` alone. The congruence therefore fixes `C` for every value of `t` as soon as those four
coefficients vanish, and the vanishing is a statement about `N`, `P` and `C` with no `t` in it.

The two factors are allowed to be different exponentials, so that the expansion also covers a
two-sided product `M C M'` by unrelated matrices; the criterion below is the case `N' = Nᵀ` and
`P' = Pᵀ`, where the right factor is the transpose of the left one and the product is a
congruence.

## Main results

* `Matrix.one_add_smul_add_smul_mul_mul`: the degree-four expansion.
* `Matrix.one_add_smul_add_smul_mul_mul_transpose`: the congruence fixes `C` when the four
  coefficients of that expansion vanish.
* `Matrix.mul_mul_transpose_mul` and `Matrix.transpose_mul_mul_mul`: congruence in either
  orientation composes, congruence by a product being congruence twice.
-/

public section

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommSemiring A]

/-- **The degree-four expansion of a quadratic exponential acting on both sides of a matrix.** -/
theorem one_add_smul_add_smul_mul_mul (t : A) (N P C N' P' : Matrix ι ι A) :
    (1 + t • N + t ^ 2 • P) * C * (1 + t • N' + t ^ 2 • P') =
      C + t • (N * C + C * N') + t ^ 2 • (P * C + N * C * N' + C * P') +
        t ^ 3 • (P * C * N' + N * C * P') + t ^ 4 • (P * C * P') := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul,
    smul_smul, smul_add]
  module

/-- **A quadratic exponential fixes a matrix by congruence** when the four coefficients of the
expansion above vanish. The four hypotheses are the coefficients of `t`, `t²`, `t³` and `t⁴`; they
mention no parameter, so a consumer checks them once for all values of `t`. -/
theorem one_add_smul_add_smul_mul_mul_transpose {N P C : Matrix ι ι A}
    (h1 : N * C + C * Nᵀ = 0)
    (h2 : P * C + N * C * Nᵀ + C * Pᵀ = 0)
    (h3 : P * C * Nᵀ + N * C * Pᵀ = 0)
    (h4 : P * C * Pᵀ = 0) (t : A) :
    (1 + t • N + t ^ 2 • P) * C * (1 + t • N + t ^ 2 • P)ᵀ = C := by
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_smul, one_add_smul_add_smul_mul_mul, h1, h2, h3, h4, smul_zero, smul_zero,
    smul_zero, smul_zero, add_zero, add_zero, add_zero, add_zero]

omit [DecidableEq ι] in
/-- **Congruence by a product is congruence twice**, in the orientation `g C gᵀ`. -/
theorem mul_mul_transpose_mul (g h C : Matrix ι ι A) :
    g * h * C * (g * h)ᵀ = g * (h * C * hᵀ) * gᵀ := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- **Congruence by a product is congruence twice**, in the orientation `gᵀ C g`. -/
theorem transpose_mul_mul_mul (g h C : Matrix ι ι A) :
    (g * h)ᵀ * C * (g * h) = hᵀ * (gᵀ * C * g) * h := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end Matrix
