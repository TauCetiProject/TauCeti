/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Algebra.Star.SelfAdjoint
import TauCeti.Analysis.SpecificLimits.SqLeMulDoubling

/-!
# Cauchy–Schwarz inequalities for positive functionals on star algebras

Let `A` be a (possibly non-unital) star algebra over `ℂ` and `φ : A →ₗ[ℂ] ℂ` a linear functional
which is *positive* in the algebraic sense, `0 ≤ φ (star x * x)` for every `x`. No order on `A`,
norm on `A` or completeness is assumed, so this covers functionals on algebras of noncommutative
star polynomials, where Mathlib's `PositiveLinearMap` API for star-ordered rings does not apply.
The sesquilinear form `(x, y) ↦ φ (star x * y)` is then positive semidefinite, so `φ` is hermitian
on products, `star (φ (star x * y)) = φ (star y * x)`, and satisfies the Cauchy–Schwarz inequality
`‖φ (star x * y)‖ ^ 2 ≤ ‖φ (star x * x)‖ * ‖φ (star y * y)‖`. The form `LinearMap.starMulCore`
and the inequality `LinearMap.norm_map_star_mul_sq_le` adapt Mathlib's
`PositiveLinearMap.preGNSpreInnerProdSpace` and `PositiveLinearMap.norm_map_star_mul_sq_le`
(in `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`) from positive maps on star-ordered rings
to algebraically positive functionals without a star order.

Iterating Cauchy–Schwarz turns growth bounds on moments into operator-type bounds. If `y` is
selfadjoint and `‖φ (star p * y ^ m * p)‖ ≤ C * r ^ m` for all `m`, then
`‖φ (star p * y * p)‖ ≤ r * ‖φ (star p * p)‖`: Cauchy–Schwarz gives
`‖φ (star p * y ^ n * p)‖ ^ 2 ≤ ‖φ (star p * p)‖ * ‖φ (star p * y ^ (2 * n) * p)‖`, so the bounded
sequence `‖φ (star p * y ^ n * p)‖ / r ^ n` satisfies the doubling inequality of
`TauCeti.apply_one_le_apply_zero_of_sq_le_mul`. For `y = star x * x` this is the inequality
`φ (star p * star x * x * p) ≤ r * φ (star p * p)`. When it holds for every `p`, left
multiplication by `x` is bounded, of norm at most `√r`, on the GNS space of `φ`. Positivity of `φ`
alone gives no such bound; the growth hypothesis is essential.

## Main results

* `LinearMap.star_map_star_mul` — a positive functional is hermitian on products.
* `LinearMap.starMulCore` — the positive semidefinite form `(x, y) ↦ φ (star x * y)` as a
  `PreInnerProductSpace.Core`.
* `LinearMap.norm_map_star_mul_sq_le` — the Cauchy–Schwarz inequality.
* `LinearMap.norm_map_star_mul_mul_le_of_forall_pow` — exponential growth of the moments
  `φ (star p * y ^ m * p)` of a selfadjoint `y` bounds `φ (star p * y * p)`.
* `LinearMap.map_star_mul_star_mul_mul_le_of_forall_pow` — the special case `y = star x * x`,
  as an inequality in `ℂ`.

## References

* K. Schmüdgen, *An Invitation to Unbounded Representations of ∗-Algebras on Hilbert Space*,
  Graduate Texts in Mathematics 285, Springer, 2020, Chapter 4.
-/

public section

open ComplexOrder

namespace LinearMap

section NonUnital

variable {A : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (φ : A →ₗ[ℂ] ℂ)

/-- A positive functional is hermitian on products: `star (φ (star x * y)) = φ (star y * x)`. -/
theorem star_map_star_mul (hφ : ∀ x, 0 ≤ φ (star x * x)) (x y : A) :
    star (φ (star x * y)) = φ (star y * x) := by
  -- The values on `star z * z` are real for `z = x + y` and `z = x + I • y`.
  have h₁ : φ (star (x + y) * (x + y)) =
      φ (star x * x) + φ (star x * y) + φ (star y * x) + φ (star y * y) := by
    simp only [star_add, add_mul, mul_add, map_add]
    ring
  have h₂ : φ (star (x + Complex.I • y) * (x + Complex.I • y)) =
      φ (star x * x) + Complex.I * φ (star x * y) - Complex.I * φ (star y * x) +
        φ (star y * y) := by
    simp only [star_add, star_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add,
      map_smul, smul_eq_mul, Complex.star_def, Complex.conj_I]
    linear_combination (-φ (star y * y)) * Complex.I_sq
  have i₁ := (Complex.nonneg_iff.1 (hφ (x + y))).2
  have i₂ := (Complex.nonneg_iff.1 (hφ (x + Complex.I • y))).2
  have ix := (Complex.nonneg_iff.1 (hφ x)).2
  have iy := (Complex.nonneg_iff.1 (hφ y)).2
  rw [h₁] at i₁
  rw [h₂] at i₂
  generalize φ (star x * y) = a at i₁ i₂ ⊢
  generalize φ (star y * x) = b at i₁ i₂ ⊢
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im] at i₁ i₂
  apply Complex.ext <;> simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> linarith

/-- The positive semidefinite sesquilinear form `(x, y) ↦ φ (star x * y)` of a positive
functional, as a `PreInnerProductSpace.Core`. Its quotient by the null space is the pre-Hilbert
space of the GNS construction of `φ`. -/
@[instance_reducible]
def starMulCore (hφ : ∀ x, 0 ≤ φ (star x * x)) : PreInnerProductSpace.Core ℂ A where
  inner x y := φ (star x * y)
  conj_inner_symm x y := φ.star_map_star_mul hφ y x
  re_inner_nonneg x := (Complex.nonneg_iff.1 (hφ x)).1
  add_left x y z := by simp only [star_add, add_mul, map_add]
  smul_left x y r := by
    simp only [star_smul, smul_mul_assoc, map_smul, smul_eq_mul, Complex.star_def]

/-- The inner product of `φ.starMulCore hφ` is `(x, y) ↦ φ (star x * y)`. -/
@[simp]
theorem starMulCore_inner (hφ : ∀ x, 0 ≤ φ (star x * x)) (x y : A) :
    (φ.starMulCore hφ).inner x y = φ (star x * y) :=
  (rfl)

/-- The **Cauchy–Schwarz inequality** for a positive functional on a star algebra over `ℂ`. -/
theorem norm_map_star_mul_sq_le (hφ : ∀ x, 0 ≤ φ (star x * x)) (x y : A) :
    ‖φ (star x * y)‖ ^ 2 ≤ ‖φ (star x * x)‖ * ‖φ (star y * y)‖ := by
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ A _ _ _ (φ.starMulCore hφ) x y
  simp only [starMulCore_inner, RCLike.re_to_complex] at h
  rwa [← φ.star_map_star_mul hφ x y, norm_star, ← sq, Complex.re_eq_norm.2 (hφ x),
    Complex.re_eq_norm.2 (hφ y)] at h

end NonUnital

section Unital

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (φ : A →ₗ[ℂ] ℂ)

/-- One step of the iterated Cauchy–Schwarz inequality: for selfadjoint `y`,
`‖φ (star p * y ^ n * p)‖ ^ 2 ≤ ‖φ (star p * p)‖ * ‖φ (star p * y ^ (2 * n) * p)‖`. -/
private theorem norm_map_star_mul_pow_mul_sq_le (hφ : ∀ x, 0 ≤ φ (star x * x)) {y : A}
    (hy : IsSelfAdjoint y) (p : A) (n : ℕ) :
    ‖φ (star p * y ^ n * p)‖ ^ 2 ≤
      ‖φ (star p * p)‖ * ‖φ (star p * y ^ (2 * n) * p)‖ := by
  have h := φ.norm_map_star_mul_sq_le hφ p (y ^ n * p)
  rw [star_mul, (hy.pow n).star_eq] at h
  simpa only [two_mul, pow_add, mul_assoc] using h

/-- If the moments `φ (star p * y ^ m * p)` of a selfadjoint `y` grow at most like `C * r ^ m`,
then `‖φ (star p * y * p)‖ ≤ r * ‖φ (star p * p)‖`. -/
theorem norm_map_star_mul_mul_le_of_forall_pow (hφ : ∀ x, 0 ≤ φ (star x * x)) {y : A}
    (hy : IsSelfAdjoint y) (p : A) {C r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ m, ‖φ (star p * y ^ m * p)‖ ≤ C * r ^ m) :
    ‖φ (star p * y * p)‖ ≤ r * ‖φ (star p * p)‖ := by
  obtain rfl | hr := hr.eq_or_lt
  · simpa using hC 1
  -- The normalized moments `‖φ (star p * y ^ n * p)‖ / r ^ n` are bounded by `C` and satisfy the
  -- doubling form of the Cauchy–Schwarz inequality, so they cannot increase at the first step.
  have h := TauCeti.apply_one_le_apply_zero_of_sq_le_mul
    (b := fun n ↦ ‖φ (star p * y ^ n * p)‖ / r ^ n) (D := C) (by positivity) (fun n ↦ ?_)
    (fun n ↦ (div_le_iff₀ (pow_pos hr n)).2 (hC n))
  · simpa [div_le_iff₀ hr, mul_comm r] using h
  · have hrn : r ^ (n + n) = (r ^ n) ^ 2 := by ring
    simp only [pow_zero, mul_one, div_one, div_pow]
    rw [hrn, ← two_mul, mul_div_assoc']
    exact div_le_div_of_nonneg_right (φ.norm_map_star_mul_pow_mul_sq_le hφ hy p n) (by positivity)

/-- If the moments `φ (star p * (star x * x) ^ m * p)` grow at most like `C * r ^ m`, then
`φ (star p * star x * x * p) ≤ r * φ (star p * p)`. On the GNS space of `φ`, this says that left
multiplication by `x` multiplies the norm of the class of `p` by at most `√r`. -/
theorem map_star_mul_star_mul_mul_le_of_forall_pow (hφ : ∀ x, 0 ≤ φ (star x * x)) (x p : A)
    {C r : ℝ} (hr : 0 ≤ r) (hC : ∀ m, ‖φ (star p * (star x * x) ^ m * p)‖ ≤ C * r ^ m) :
    φ (star p * star x * x * p) ≤ r * φ (star p * p) := by
  have h := φ.norm_map_star_mul_mul_le_of_forall_pow hφ (IsSelfAdjoint.star_mul_self x) p hr hC
  have hxp : φ (star p * star x * x * p) = φ (star (x * p) * (x * p)) := by
    simp only [star_mul, mul_assoc]
  rw [← mul_assoc (star p)] at h
  have hnonneg : 0 ≤ φ (star p * star x * x * p) := hxp ▸ hφ (x * p)
  rw [Complex.eq_coe_norm_of_nonneg hnonneg,
    Complex.eq_coe_norm_of_nonneg (hφ p), ← Complex.ofReal_mul, Complex.real_le_real]
  exact h

end Unital

end LinearMap
