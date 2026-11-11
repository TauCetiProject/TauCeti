/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.RingTheory.Norm.Defs

/-!
# Norms of non-zero-divisors and units in finite free algebras

Let `S` be a commutative `R`-algebra that is free of finite rank as an `R`-module. The norm
`Algebra.norm R x` is the determinant of multiplication by `x` in a basis. By the theorem of
McCoy, as proved in Mathlib (`Matrix.isLeftRegular_iff_nonsingular`,
`Matrix.nonsingular_iff_det_mem_nonZeroDivisors`), a square matrix over a commutative ring is
injective exactly when its determinant is a non-zero-divisor. Hence `x` is a non-zero-divisor of
`S` exactly when its norm is a non-zero-divisor of `R` (`Algebra.norm_mem_nonZeroDivisors_iff`),
with no domain hypothesis on `R` or `S`.

By the Cayley–Hamilton theorem `x` divides the image of its norm in `S`
(`Algebra.dvd_algebraMap_norm`). Hence `x` is a unit of `S` exactly when its norm is a unit of `R`
(`Algebra.isUnit_norm_iff`). The first two results together say that every non-zero-divisor of
`S` divides the image of a non-zero-divisor of `R`, which identifies the total ring of fractions
of `S` with a localization of `S` at non-zero-divisors of `R`
(`TauCeti.RingTheory.Localization.FiniteFree`).

## Main results

* `Algebra.isLeftRegular_leftMulMatrix_iff`: the matrix of left multiplication by `x` in a basis
  is left regular exactly when `x` is.
* `Algebra.norm_mem_nonZeroDivisors_iff`: `x` is a non-zero-divisor exactly when its norm is.
* `Algebra.dvd_algebraMap_norm`: `x` divides the image of its norm.
* `Algebra.isUnit_norm_iff`: `x` is a unit exactly when its norm is.
-/

public section

open scoped nonZeroDivisors

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Left multiplication by `x` is injective exactly when its matrix in a basis is left regular,
since the coordinates of `x * y` are that matrix applied to the coordinates of `y`. -/
theorem isLeftRegular_leftMulMatrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (x : S) : IsLeftRegular (leftMulMatrix b x) ↔ IsLeftRegular x := by
  have hcomp : (leftMulMatrix b x).mulVec ∘ b.equivFun = b.equivFun ∘ (x * ·) := by
    ext y : 1
    simp [b.equivFun_apply, ← leftMulMatrix_mulVec_repr b x y]
  rw [Matrix.isLeftRegular_iff_mulVec_injective, ← EquivLike.injective_comp b.equivFun, hcomp,
    EquivLike.comp_injective]
  -- `IsLeftRegular x` is defined as the injectivity of `(x * ·)`.
  rfl

variable [Module.Free R S] [Module.Finite R S]

/-- In a commutative algebra that is free of finite rank, an element is a non-zero-divisor exactly
when its norm is a non-zero-divisor of the base ring. -/
@[simp]
theorem norm_mem_nonZeroDivisors_iff {x : S} : norm R x ∈ R⁰ ↔ x ∈ S⁰ := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [norm_eq_matrix_det b, ← Matrix.nonsingular_iff_det_mem_nonZeroDivisors,
    ← Matrix.isLeftRegular_iff_nonsingular, isLeftRegular_leftMulMatrix_iff,
    isLeftRegular_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]

/-- In a commutative algebra that is free of finite rank, an element divides the image of its
norm. -/
theorem dvd_algebraMap_norm (x : S) : x ∣ algebraMap R S (norm R x) := by
  classical
  let b := Module.Free.chooseBasis R S
  let p := (leftMulMatrix b x).charpoly
  -- By Cayley–Hamilton `x` is a root of `p`, so it divides `p.coeff 0 = ± norm R x`.
  have hp : (p.map (algebraMap R S)).IsRoot x := by
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, aeval_charpoly_leftMulMatrix]
  have hdvd : x ∣ algebraMap R S (p.coeff 0) := by
    simpa only [Polynomial.coeff_map] using hp.dvd_coeff_zero
  rw [norm_eq_matrix_det b, Matrix.det_eq_sign_charpoly_coeff, map_mul]
  exact Dvd.dvd.mul_left hdvd _

/-- In a commutative algebra that is free of finite rank, an element is a unit exactly when its
norm is a unit of the base ring. -/
@[simp]
theorem isUnit_norm_iff {x : S} : IsUnit (norm R x) ↔ IsUnit x :=
  ⟨fun h ↦ isUnit_of_dvd_unit (dvd_algebraMap_norm x) (h.map _), fun h ↦ h.map _⟩

end Algebra
