/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Matrix entries lying in an ideal

A two-sided ideal containing every entry of a matrix contains every entry of any two-sided
product formed from it, and an ideal contains every entry of any linear combination of matrices
whose entries it contains: each such entry is an `S`-combination of entries of the original
matrices.

Nothing here needs invertibility, a square shape, or a diagonal target — only that the products
are conformable — so the statements are rectangular. Both hold over any `Semiring`; the
two-sided product statement asks the ideal to be two-sided (`Ideal.IsTwoSided`), which is
automatic over a commutative semiring. They are the membership computations a defining-ideal
closure proof performs when it propagates a relation through a matrix identity.

## Main results

* `Matrix.mul_mul_apply_mem`: every entry of `P * A * Q` lies in a two-sided ideal containing
  every entry of `A`.
* `Matrix.sum_smul_apply_mem`: every entry of `∑ a, c a • F a` lies in an ideal containing every
  entry of every `F a`.
* `Matrix.mul_eq_zero_of_sq_eq_bot`: the product of two matrices with entries in a square-zero
  ideal vanishes.
* `Matrix.forall_mem_ker_iff_map_eq_zero`: the entries of a matrix lie in the kernel of a ring
  homomorphism exactly when its image under that homomorphism is zero.
-/

public section

namespace Matrix

variable {l m n o ι S : Type*}

/-- **A two-sided ideal containing the entries of a matrix contains the entries of any two-sided
product formed from it.** Each entry of `P * A * Q` is an `S`-combination of entries of `A`. -/
theorem mul_mul_apply_mem [Semiring S] [Fintype m] [Fintype n] {A : Matrix m n S} {I : Ideal S}
    [I.IsTwoSided] (hA : ∀ i j, A i j ∈ I) (P : Matrix l m S) (Q : Matrix n o S) (i : l) (j : o) :
    (P * A * Q) i j ∈ I := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Ideal.sum_mem _ fun t _ =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hA t k))

/-- **An ideal containing the entries of a family of matrices contains the entries of every
linear combination of them.** -/
theorem sum_smul_apply_mem [Semiring S] [Fintype ι] {F : ι → Matrix m n S} {I : Ideal S}
    (hF : ∀ a i j, F a i j ∈ I) (c : ι → S) (i : m) (j : n) :
    (∑ a, c a • F a) i j ∈ I := by
  rw [Matrix.sum_apply]
  refine Ideal.sum_mem _ fun a _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hF a i j)

/-- **The product of two matrices with entries in a square-zero ideal vanishes**: each entry of
`A * B` is a sum of products of two elements of the ideal. -/
theorem mul_eq_zero_of_sq_eq_bot [Semiring S] [Fintype m] {I : Ideal S} (hI : I ^ 2 = ⊥)
    {A : Matrix l m S} {B : Matrix m o S} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    A * B = 0 := by
  rw [Submodule.pow_succ, Submodule.pow_one] at hI
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h := Ideal.mul_mem_mul (hA i k) (hB k j)
  rw [hI] at h
  exact Ideal.mem_bot.mp h

/-- The entries of a matrix lie in the kernel of `f` exactly when its image under `f` is zero. -/
theorem forall_mem_ker_iff_map_eq_zero {R : Type*} [Semiring R] [Semiring S] {F : Type*}
    [FunLike F R S] [RingHomClass F R S] {f : F} {D : Matrix m n R} :
    (∀ i j, D i j ∈ RingHom.ker f) ↔ D.map f = 0 := by
  simp only [RingHom.mem_ker, ← Matrix.ext_iff, map_apply, zero_apply]

end Matrix
