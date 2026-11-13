/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The bilinear form of a matrix on finitely supported vectors

Mathlib's `Matrix.toBilin'` reads a square matrix over a finite index type as a bilinear form on
`n → R`. For an arbitrary index set `I`, a matrix `A : Matrix I I R` over a commutative semiring
still defines the bilinear form `∑ᵢⱼ xᵢ A i j yⱼ` on the free module `I →₀ R`, whose Gram matrix in
the standard basis is `A`. This is the form used, for example, to pair the simple roots of a
Coxeter system with infinite rank.

## Main definitions

* `Matrix.finsuppBilinForm`: the bilinear form `∑ᵢⱼ xᵢ A i j yⱼ` on `I →₀ R`.

## Main results

* `Matrix.finsuppBilinForm_apply`: the form is `∑ᵢⱼ xᵢ A i j yⱼ`, as a double `Finsupp.sum`.
* `Matrix.finsuppBilinForm_single_single`: the Gram matrix of `Matrix.finsuppBilinForm A` is `A`.
* `Matrix.finsuppBilinForm_apply_eq_dotProduct`: for finite `I` the form is `x ⬝ᵥ (A *ᵥ y)`.
-/

public section

namespace Matrix

variable {I R : Type*} [CommSemiring R] (A : Matrix I I R)

/-- **The bilinear form of a matrix** on the free module `I →₀ R`, the form `∑ᵢⱼ xᵢ A i j yⱼ`
whose Gram matrix in the standard basis is `A`. -/
noncomputable def finsuppBilinForm : LinearMap.BilinForm R (I →₀ R) :=
  Finsupp.linearCombination R fun i ↦ Finsupp.linearCombination R (A i)

/-- `Matrix.finsuppBilinForm A` pairs `eᵢ` with `y` by the functional `y ↦ ∑ⱼ A i j yⱼ`. -/
theorem finsuppBilinForm_def :
    A.finsuppBilinForm = Finsupp.linearCombination R fun i ↦ Finsupp.linearCombination R (A i) :=
  (rfl)

/-- **Evaluation of the bilinear form of a matrix**: `A.finsuppBilinForm x y = ∑ᵢⱼ xᵢ A i j yⱼ`,
for an arbitrary index set. -/
theorem finsuppBilinForm_apply (x y : I →₀ R) :
    A.finsuppBilinForm x y = x.sum fun i a ↦ y.sum fun j b ↦ a * A i j * b := by
  simp [finsuppBilinForm, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply,
    Finsupp.mul_sum, mul_comm, mul_left_comm]

/-- Pairing with a basis vector `a • eᵢ` on the left is the functional `y ↦ a * ∑ⱼ A i j yⱼ`. -/
@[simp]
theorem finsuppBilinForm_single_left (i : I) (a : R) :
    A.finsuppBilinForm (Finsupp.single i a) = a • Finsupp.linearCombination R (A i) :=
  Finsupp.linearCombination_single R a i

/-- The Gram matrix of `Matrix.finsuppBilinForm` is the matrix itself. -/
theorem finsuppBilinForm_single_single (i j : I) (a b : R) :
    A.finsuppBilinForm (Finsupp.single i a) (Finsupp.single j b) = a * b * A i j := by
  simp only [finsuppBilinForm_single_left, LinearMap.smul_apply, Finsupp.linearCombination_single,
    smul_eq_mul]
  ring

/-- For a finite index set, `Matrix.finsuppBilinForm` is the usual form `x ⬝ᵥ (A *ᵥ y)` of the
matrix `A`. -/
theorem finsuppBilinForm_apply_eq_dotProduct [Fintype I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = ⇑x ⬝ᵥ (A *ᵥ ⇑y) := by
  simp [finsuppBilinForm, Finsupp.linearCombination_apply, Finsupp.sum_fintype, dotProduct,
    mulVec, Finset.mul_sum, mul_comm]

end Matrix
