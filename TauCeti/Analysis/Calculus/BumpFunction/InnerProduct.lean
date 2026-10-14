/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Derivatives of bump test functions on inner product spaces

For a smooth bump `θ` on a real inner product space, a smooth bump `ψ` on `ℝ`, a vector `w` and a
function `f`, the test function `x ↦ θ x * (ψ (f x) * ⟪w, x⟫)` is the product of a localisation in
space, a localisation in the values of `f` and a linear function. Its derivative in a direction
along which `f` is stationary does not see `ψ'`.

## Main results

* `ContDiffBump.fderiv_mul_comp_mul_inner_apply`.
-/

public section

open scoped RealInnerProductSpace

/-- **The derivative of a bump test function.** For a bump `θ` on an inner product space `E`, a
bump `ψ` on `ℝ`, a vector `w` and a function `f` differentiable at `p`, the derivative at `p` of
`x ↦ θ x * (ψ (f x) * ⟪w, x⟫)` in a direction `v` with `Df(p) v = 0` is
`(θ p ⟪w, v⟫ + ⟪w, p⟫ Dθ(p) v) ψ (f p)`. -/
theorem ContDiffBump.fderiv_mul_comp_mul_inner_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [HasContDiffBump E] {z : E} (θ : ContDiffBump z) {c : ℝ}
    (ψ : ContDiffBump c) (w : E) {f : E → ℝ} {p v : E} (hf : DifferentiableAt ℝ f p)
    (hv : fderiv ℝ f p v = 0) :
    fderiv ℝ (fun x ↦ θ x * (ψ (f x) * ⟪w, x⟫)) p v =
      (θ p * ⟪w, v⟫ + ⟪w, p⟫ * fderiv ℝ θ p v) * ψ (f p) := by
  have hgder : HasFDerivAt (fun x ↦ θ x * (ψ (f x) * ⟪w, x⟫))
      (θ p • ((ψ (f p)) • innerSL ℝ w + ⟪w, p⟫ • (fderiv ℝ ψ (f p)).comp (fderiv ℝ f p)) +
        (ψ (f p) * ⟪w, p⟫) • fderiv ℝ θ p) p :=
    ((θ.contDiff (n := 1)).differentiable one_ne_zero p).hasFDerivAt.mul
      ((((ψ.contDiff (n := 1)).differentiable one_ne_zero (f p)).hasFDerivAt.comp p
        hf.hasFDerivAt).mul (innerSL ℝ w).hasFDerivAt)
  rw [hgder.fderiv]
  simp only [smul_add, add_apply, smul_apply, coe_innerSL_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, hv, fderiv_eq_smul_deriv, zero_mul, mul_zero, add_zero]
  ring
