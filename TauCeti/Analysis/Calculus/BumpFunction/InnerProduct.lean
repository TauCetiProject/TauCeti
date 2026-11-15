/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Derivatives of bump test functions on inner product spaces

For functions `θ` on an inner product space over `𝕜` (`ℝ` or `ℂ`) and `ψ` on `𝕜` (typically
smooth bumps on real spaces), a vector `w` and a function `f`, the test function
`x ↦ θ x * (ψ (f x) * ⟪w, x⟫)` is the product of a localisation in space, a localisation in the
values of `f` and a linear function. Its derivative in a direction along which `f` is stationary
does not see `ψ'`.

## Main results

* `TauCeti.fderiv_mul_comp_mul_inner_apply`: for any functions differentiable at the point, over
  any `RCLike` field `𝕜`.
* `ContDiffBump.fderiv_mul_comp_mul_inner_apply`: its form for bumps on a real inner product space.
-/

public section

open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

/-- **The derivative of a localized linear test function.** For functions `θ : E → 𝕜` and
`ψ : 𝕜 → 𝕜`, a vector `w` and a function `f`, with `θ` differentiable at `p`, `f` differentiable at
`p` and `ψ` differentiable at `f p`, the derivative at `p` of `x ↦ θ x * (ψ (f x) * ⟪w, x⟫_𝕜)` in a
direction `v` with `Df(p) v = 0` is `(θ p ⟪w, v⟫_𝕜 + ⟪w, p⟫_𝕜 Dθ(p) v) ψ (f p)`. -/
theorem fderiv_mul_comp_mul_inner_apply {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {θ : E → 𝕜} {ψ : 𝕜 → 𝕜} (w : E) {f : E → 𝕜} {p v : E}
    (hθ : DifferentiableAt 𝕜 θ p) (hψ : DifferentiableAt 𝕜 ψ (f p))
    (hf : DifferentiableAt 𝕜 f p) (hv : fderiv 𝕜 f p v = 0) :
    fderiv 𝕜 (fun x ↦ θ x * (ψ (f x) * ⟪w, x⟫_𝕜)) p v =
      (θ p * ⟪w, v⟫_𝕜 + ⟪w, p⟫_𝕜 * fderiv 𝕜 θ p v) * ψ (f p) := by
  have hgder : HasFDerivAt (fun x ↦ θ x * (ψ (f x) * ⟪w, x⟫_𝕜))
      (θ p • ((ψ (f p)) • innerSL 𝕜 w + ⟪w, p⟫_𝕜 • (fderiv 𝕜 ψ (f p)).comp (fderiv 𝕜 f p)) +
        (ψ (f p) * ⟪w, p⟫_𝕜) • fderiv 𝕜 θ p) p :=
    hθ.hasFDerivAt.mul ((hψ.hasFDerivAt.comp p hf.hasFDerivAt).mul (innerSL 𝕜 w).hasFDerivAt)
  rw [hgder.fderiv]
  simp only [smul_add, add_apply, smul_apply, coe_innerSL_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, hv, map_zero, mul_zero, add_zero]
  ring

end TauCeti

/-- **The derivative of a bump test function.** The case of
`TauCeti.fderiv_mul_comp_mul_inner_apply` in which `𝕜 = ℝ`, `θ` is a bump on `E` and `ψ` a bump
on `ℝ`. -/
theorem ContDiffBump.fderiv_mul_comp_mul_inner_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [HasContDiffBump E] {z : E} (θ : ContDiffBump z) {c : ℝ}
    (ψ : ContDiffBump c) (w : E) {f : E → ℝ} {p v : E} (hf : DifferentiableAt ℝ f p)
    (hv : fderiv ℝ f p v = 0) :
    fderiv ℝ (fun x ↦ θ x * (ψ (f x) * ⟪w, x⟫)) p v =
      (θ p * ⟪w, v⟫ + ⟪w, p⟫ * fderiv ℝ θ p v) * ψ (f p) :=
  TauCeti.fderiv_mul_comp_mul_inner_apply w
    ((θ.contDiff (n := 1)).differentiable one_ne_zero p)
    ((ψ.contDiff (n := 1)).differentiable one_ne_zero (f p)) hf hv
