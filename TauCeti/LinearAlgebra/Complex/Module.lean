/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Real-linear evaluation and scalar multiplication on the complex plane

A real-linear map out of the complex plane is determined by its values at `1` and `I`.
In particular, a complex scalar action decomposes into its real and imaginary parts.
This decomposition applies to any real module structure compatible with the complex action.

For a real-linear map `L` into a complex module, its defect from complex linearity
`e ↦ L e + I • L (I * e)` is conjugate-linear and is therefore determined by its value at `1`.
Multiplication by `I` and by `-I` are mutually inverse on any complex multiplication action.
-/

public section

namespace LinearMap

/-- A real-linear map out of the complex plane is evaluated in the real basis `(1,I)`. -/
theorem apply_eq_re_smul_one_add_im_smul_I {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (L : ℂ →ₗ[ℝ] F) (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I := by
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) :=
      congrArg L (by simp [Complex.real_smul])
    _ = _ := by simp only [map_add, map_smul]

open Complex ComplexConjugate

/-- Rotating `L 1 + I • L I` by the conjugate of `e` gives the derivative of `L` along `e` plus
`I` times its derivative along `I * e`: the map `e ↦ L e + I • L (I * e)` is conjugate-linear. For
`L` the derivative of a map `u` at `w + r e^{iθ}` and `e = e^{iθ}`, these are the radial derivative
and `r⁻¹` times the angular derivative of `(r, θ) ↦ u (w + r e^{iθ})`. -/
theorem conj_smul_apply_one_add_I_smul_apply_I {F : Type*} [AddCommGroup F] [Module ℂ F]
    (L : ℂ →ₗ[ℝ] F) (e : ℂ) :
    conj e • (L 1 + I • L I) = L e + I • L (I * e) := by
  have hL (z : ℂ) : L z = (z.re : ℂ) • L 1 + (z.im : ℂ) • L I := by
    simpa only [Complex.coe_smul] using L.apply_eq_re_smul_one_add_im_smul_I z
  have he : conj e = (e.re : ℂ) - e.im * I := by
    apply Complex.ext <;> simp
  rw [hL e, hL (I * e), he]
  simp only [mul_re, I_re, I_im, mul_im, zero_mul, one_mul, zero_sub, zero_add, ofReal_neg]
  match_scalars
  · ring
  · linear_combination -(e.im : ℂ) * I_sq

end LinearMap

namespace Complex

theorem I_smul_neg_I_smul {X : Type*} [MulAction ℂ X] (x : X) : I • (-I • x) = x := by
  rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

theorem neg_I_smul_I_smul {X : Type*} [MulAction ℂ X] (x : X) : -I • (I • x) = x := by
  rw [smul_smul, neg_mul, I_mul_I, neg_neg, one_smul]

/-- Decompose a complex scalar action into its real and imaginary parts. -/
@[simp]
lemma re_smul_add_im_smul {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
    [IsScalarTower ℝ ℂ V] (z : ℂ) (v : V) :
    z.re • v + z.im • (I • v) = z • v := by
  simpa only [LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, one_smul]
    using (LinearMap.apply_eq_re_smul_one_add_im_smul_I
      ((LinearMap.toSpanSingleton ℂ V v).restrictScalars ℝ) z).symm

end Complex
