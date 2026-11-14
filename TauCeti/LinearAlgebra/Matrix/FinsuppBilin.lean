/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Reflection
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Matrix bilinear forms and reflections on finitely supported functions

Mathlib's `Matrix.toBilin'` attaches the bilinear form `(x, y) ↦ ∑ i, ∑ j, x i * A i j * y j` on
`I → R` to a square matrix `A : Matrix I I R` over a finite index type `I` with decidable equality.
Root lattices and reflection representations of infinite-rank Coxeter groups live instead on the
free module `I →₀ R` of finitely supported functions, without finiteness or decidability
assumptions on `I`.

This file defines the bilinear form `Matrix.finsuppBilin` on `I →₀ R` with Gram matrix `A` in the
basis of single-coordinate vectors `Finsupp.single i 1`, together with the associated reflection
endomorphisms `Matrix.finsuppPreReflection` and linear automorphisms `Matrix.finsuppReflection`
when `A i i = 2`. Both constructions commute with coefficientwise scalar maps `Finsupp.mapRange`
along ring homomorphisms, and agree with `Matrix.toBilin'` and `Matrix.toBilin` when `I` is finite.

## Main definitions

* `Matrix.finsuppBilin`: the bilinear form `(x, y) ↦ ∑_{i, j} x i * A i j * y j` on `I →₀ R`.
* `Matrix.finsuppPreReflection`: the endomorphism
  `x ↦ x - (x.sum fun j a ↦ a * A i j) • Finsupp.single i 1` of `I →₀ R`.
* `Matrix.finsuppReflection`: `Matrix.finsuppPreReflection` bundled as a linear equivalence via
  `Module.reflection` when `A i i = 2`.

## Main results

* `Matrix.IsSymm.finsuppBilin_comm`: a symmetric matrix defines a symmetric bilinear form on
  `I →₀ R`.
* `Matrix.finsuppBilin_eq_toBilin'` and `Matrix.finsuppBilin_repr_eq_toBilin`: for finite `I`,
  `Matrix.finsuppBilin` agrees with `Matrix.toBilin'` and, in coordinates of a basis, with
  `Matrix.toBilin`.
* `Matrix.finsuppBilin_finsuppPreReflection`: when `A` is symmetric and `A i i = 2`, the `i`-th
  reflection preserves `A.finsuppBilin`.
* `Matrix.map_finsuppBilin` and `Matrix.mapRange_finsuppPreReflection`: compatibility of the form
  and reflections with ring homomorphisms on scalars.
-/

public section

namespace Matrix

section CommSemiring

variable {I R S : Type*} [CommSemiring R] [CommSemiring S] (A : Matrix I I R)

/-- **The bilinear form of a matrix on finitely supported functions**: the `R`-bilinear form on
`I →₀ R` whose Gram matrix in the standard basis `i ↦ Finsupp.single i 1` is `A`. Neither
finiteness nor decidable equality on `I` is required. -/
noncomputable def finsuppBilin : LinearMap.BilinForm R (I →₀ R) :=
  Finsupp.linearCombination R fun i ↦
    Finsupp.linearCombination R fun j ↦ A i j

/-- Evaluating `A.finsuppBilin` expands as the double finitely supported sum
`∑_{i, j} x i * A i j * y j`. -/
theorem finsuppBilin_apply (x y : I →₀ R) :
    A.finsuppBilin x y = x.sum fun i a ↦ y.sum fun j b ↦ a * A i j * b := by
  simp only [finsuppBilin, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun i _ ↦ Finsupp.sum_congr fun j _ ↦ ?_
  ring

/-- **The Gram matrix of `A.finsuppBilin`** on single-coordinate vectors. -/
@[simp]
theorem finsuppBilin_single_single (i j : I) (a b : R) :
    A.finsuppBilin (Finsupp.single i a) (Finsupp.single j b) = a * A i j * b := by
  simp only [finsuppBilin, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Pairing the `i`-th standard basis vector on the left extracts the `i`-th row functional
`y ↦ ∑ j, y j * A i j`. -/
theorem finsuppBilin_single_one_left (i : I) (y : I →₀ R) :
    A.finsuppBilin (Finsupp.single i 1) y = y.sum fun j b ↦ b * A i j := by
  simp [finsuppBilin, Finsupp.linearCombination_apply]

/-- Pairing the `j`-th standard basis vector on the right extracts the `j`-th column functional
`x ↦ ∑ i, x i * A i j`. -/
theorem finsuppBilin_single_one_right (x : I →₀ R) (j : I) :
    A.finsuppBilin x (Finsupp.single j 1) = x.sum fun i a ↦ a * A i j := by
  rw [finsuppBilin_apply]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  simp

/-- **A symmetric matrix defines a symmetric bilinear form on `I →₀ R`.** -/
theorem IsSymm.finsuppBilin_comm {A : Matrix I I R} (hA : A.IsSymm) (x y : I →₀ R) :
    A.finsuppBilin x y = A.finsuppBilin y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  | single i a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]
    | single j b =>
      rw [finsuppBilin_single_single, finsuppBilin_single_single, hA.apply i j]
      ring

/-- **Compatibility of `Matrix.finsuppBilin` with ring homomorphisms**: mapping entries by `f`
matches applying `f` after pairing and pushing vectors forward by `Finsupp.mapRange`. -/
theorem map_finsuppBilin (f : R →+* S) (x y : I →₀ R) :
    f (A.finsuppBilin x y) =
      (A.map f).finsuppBilin (x.mapRange f f.map_zero) (y.mapRange f f.map_zero) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    rw [map_add, LinearMap.add_apply, map_add, hx₁, hx₂, Finsupp.mapRange_add f.map_add, map_add,
      LinearMap.add_apply]
  | single i a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      rw [map_add, map_add, hy₁, hy₂, Finsupp.mapRange_add f.map_add, map_add]
    | single j b =>
      simp [Finsupp.mapRange_single]

/-- **Evaluation of `Matrix.finsuppBilin` over a finite index type** as a double `Finset.univ` sum,
without requiring decidable equality on `I`. -/
theorem finsuppBilin_eq_sum [Fintype I] (x y : I →₀ R) :
    A.finsuppBilin x y = ∑ i, ∑ j, x i * A i j * y j := by
  rw [finsuppBilin_apply]
  refine (Finsupp.sum_fintype x _ (fun i ↦ ?_)).trans ?_
  · simp
  · refine Finset.sum_congr rfl fun i _ ↦ Finsupp.sum_fintype y _ fun j ↦ ?_
    simp

/-- **Agreement with `Matrix.toBilin'` for a finite index type.** -/
theorem finsuppBilin_eq_toBilin' [Fintype I] [DecidableEq I] (x y : I →₀ R) :
    A.finsuppBilin x y = Matrix.toBilin' A x y :=
  (A.finsuppBilin_eq_sum x y).trans (Matrix.toBilin'_apply A x y).symm

/-- **Agreement with `Matrix.toBilin` in the coordinates of a finite basis.** -/
theorem finsuppBilin_repr_eq_toBilin {M : Type*} [AddCommMonoid M] [Module R M]
    [Fintype I] [DecidableEq I] (b : Module.Basis I R M) (x y : M) :
    A.finsuppBilin (b.repr x) (b.repr y) = Matrix.toBilin b A x y := by
  rw [finsuppBilin_eq_toBilin', Matrix.toBilin'_apply, Matrix.toBilin_apply]

end CommSemiring

section CommRing

variable {I R S : Type*} [CommRing R] [CommRing S] (A : Matrix I I R)

/-- **The pre-reflection endomorphism attached to the `i`-th row of `A`** on `I →₀ R`, sending
`x` to `x - (∑ j, x j * A i j) • Finsupp.single i 1`. It requires no assumption on the diagonal
entry `A i i`; when `A i i = 2`, `Matrix.finsuppReflection` upgrades it to a linear automorphism. -/
noncomputable def finsuppPreReflection (i : I) : Module.End R (I →₀ R) :=
  Module.preReflection (Finsupp.single i 1) (A.finsuppBilin (Finsupp.single i 1))

/-- `Matrix.finsuppPreReflection` in terms of `Matrix.finsuppBilin`. -/
theorem finsuppPreReflection_eq_sub_finsuppBilin (i : I) (x : I →₀ R) :
    A.finsuppPreReflection i x = x - A.finsuppBilin (Finsupp.single i 1) x • Finsupp.single i 1 :=
  Module.preReflection_apply _ _ x

/-- **The explicit coordinate formula** for `Matrix.finsuppPreReflection`. -/
@[simp]
theorem finsuppPreReflection_apply (i : I) (x : I →₀ R) :
    A.finsuppPreReflection i x = x - (x.sum fun j a ↦ a * A i j) • Finsupp.single i 1 := by
  rw [finsuppPreReflection_eq_sub_finsuppBilin, finsuppBilin_single_one_left]

/-- Over a finite index type `I`, `Matrix.finsuppPreReflection` subtracts the finite sum
`∑ j, x j * A i j` along the `i`-th standard basis vector. -/
theorem finsuppPreReflection_apply_fintype [Fintype I] (i : I) (x : I →₀ R) :
    A.finsuppPreReflection i x = x - (∑ j, x j * A i j) • Finsupp.single i 1 := by
  rw [finsuppPreReflection_apply]
  congr 2
  exact Finsupp.sum_fintype x _ fun j ↦ by simp

/-- Action of the `i`-th pre-reflection on the `j`-th standard basis vector. -/
theorem finsuppPreReflection_apply_single (i j : I) :
    A.finsuppPreReflection i (Finsupp.single j 1) =
      Finsupp.single j 1 - A i j • Finsupp.single i 1 := by
  rw [finsuppPreReflection_eq_sub_finsuppBilin, finsuppBilin_single_single, one_mul, mul_one]

/-- When `A i i = 2`, the `i`-th pre-reflection negates the `i`-th standard basis vector. -/
theorem finsuppPreReflection_apply_single_self {i : I} (hii : A i i = 2) :
    A.finsuppPreReflection i (Finsupp.single i 1) = -Finsupp.single i 1 :=
  Module.preReflection_apply_self (by simp [hii])

/-- A pre-reflection at `i` leaves every coordinate `j ≠ i` unchanged. -/
theorem finsuppPreReflection_apply_apply_of_ne {i j : I} (h : j ≠ i) (x : I →₀ R) :
    A.finsuppPreReflection i x j = x j := by
  simp [h.symm]

/-- When `A i i = 2`, the `i`-th pre-reflection is an involution. -/
theorem finsuppPreReflection_mul_self {i : I} (hii : A i i = 2) :
    A.finsuppPreReflection i * A.finsuppPreReflection i = 1 :=
  LinearMap.ext <| Module.involutive_preReflection (by simp [hii])

/-- **When `A` is symmetric and `A i i = 2`, the `i`-th reflection preserves `A.finsuppBilin`.** -/
theorem finsuppBilin_finsuppPreReflection {i : I} (hsym : A.IsSymm) (hii : A i i = 2)
    (x y : I →₀ R) :
    A.finsuppBilin (A.finsuppPreReflection i x) (A.finsuppPreReflection i y) =
      A.finsuppBilin x y := by
  simp only [finsuppPreReflection_eq_sub_finsuppBilin, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, finsuppBilin_single_single, one_mul, mul_one, hii,
    hsym.finsuppBilin_comm (Finsupp.single i 1) x]
  ring

/-- **The simple reflection linear equivalence attached to the `i`-th row of `A`** when
`A i i = 2`, built from Mathlib's `Module.reflection`. -/
noncomputable def finsuppReflection {i : I} (hii : A i i = 2) : (I →₀ R) ≃ₗ[R] (I →₀ R) :=
  Module.reflection (x := Finsupp.single i 1) (f := A.finsuppBilin (Finsupp.single i 1))
    (by simp [hii])

/-- The underlying linear map of `Matrix.finsuppReflection` is `Matrix.finsuppPreReflection`. -/
@[simp]
theorem toLinearMap_finsuppReflection {i : I} (hii : A i i = 2) :
    (A.finsuppReflection hii).toLinearMap = A.finsuppPreReflection i :=
  (rfl)

/-- Coordinate formula for `Matrix.finsuppReflection`. -/
theorem finsuppReflection_apply {i : I} (hii : A i i = 2) (x : I →₀ R) :
    A.finsuppReflection hii x = x - (x.sum fun j a ↦ a * A i j) • Finsupp.single i 1 :=
  A.finsuppPreReflection_apply i x

/-- `Matrix.finsuppReflection` is equal to its own inverse linear equivalence. -/
@[simp]
theorem finsuppReflection_symm {i : I} (hii : A i i = 2) :
    (A.finsuppReflection hii).symm = A.finsuppReflection hii :=
  (rfl)

/-- `Matrix.finsuppReflection` is self-inverse in `(I →₀ R) ≃ₗ[R] (I →₀ R)`. -/
@[simp]
theorem finsuppReflection_inv {i : I} (hii : A i i = 2) :
    (A.finsuppReflection hii)⁻¹ = A.finsuppReflection hii :=
  (rfl)

/-- `Matrix.finsuppReflection` squares to `1` in `(I →₀ R) ≃ₗ[R] (I →₀ R)`. -/
@[simp]
theorem finsuppReflection_mul_self {i : I} (hii : A i i = 2) :
    A.finsuppReflection hii * A.finsuppReflection hii = 1 :=
  LinearEquiv.toLinearMap_injective (A.finsuppPreReflection_mul_self hii)

/-- When `A` is symmetric and `A i i = 2`, `A.finsuppReflection hii` preserves `A.finsuppBilin`. -/
theorem finsuppBilin_finsuppReflection {i : I} (hsym : A.IsSymm) (hii : A i i = 2)
    (x y : I →₀ R) :
    A.finsuppBilin (A.finsuppReflection hii x) (A.finsuppReflection hii y) =
      A.finsuppBilin x y :=
  A.finsuppBilin_finsuppPreReflection hsym hii x y

/-- **Ring homomorphisms intertwine `Matrix.finsuppPreReflection` with entrywise matrix maps.** -/
theorem mapRange_finsuppPreReflection (f : R →+* S) (i : I) (x : I →₀ R) :
    (A.finsuppPreReflection i x).mapRange f f.map_zero =
      (A.map f).finsuppPreReflection i (x.mapRange f f.map_zero) := by
  have hpair :
      f (A.finsuppBilin (Finsupp.single i 1) x) =
        (A.map f).finsuppBilin (Finsupp.single i 1) (x.mapRange f f.map_zero) := by
    simpa [Finsupp.mapRange_single] using A.map_finsuppBilin f (Finsupp.single i 1) x
  have hsub :
      ∀ u v : I →₀ R,
        (u - v).mapRange f f.map_zero = u.mapRange f f.map_zero - v.mapRange f f.map_zero :=
    fun u v ↦ map_sub (Finsupp.mapRange.addMonoidHom f.toAddMonoidHom) u v
  rw [finsuppPreReflection_eq_sub_finsuppBilin, finsuppPreReflection_eq_sub_finsuppBilin, hsub,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapRange_single, hpair,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Iterates of the product of two pre-reflections commute with `Finsupp.mapRange` along a ring
homomorphism. -/
theorem mapRange_pow_finsuppPreReflection_mul (f : R →+* S) (i j : I) (n : ℕ) (x : I →₀ R) :
    (((A.finsuppPreReflection i * A.finsuppPreReflection j) ^ n) x).mapRange f f.map_zero =
      (((A.map f).finsuppPreReflection i * (A.map f).finsuppPreReflection j) ^ n)
        (x.mapRange f f.map_zero) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, A.mapRange_finsuppPreReflection f i,
      A.mapRange_finsuppPreReflection f j, ih, pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]

end CommRing

end Matrix
