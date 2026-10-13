/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Second derivatives of extended-real convex functions

Let `f : E → EReal` be convex (convex real epigraph, never `⊥`) on a real inner product space,
with real representative `F x = (f x).toReal` and `D` the interior of the effective domain
`{x | f x ≠ ⊤}`. At a point of `D` near which `F` is differentiable, the gradient `∇ F` is a
subgradient of `f`, so it is a monotone map. This file records what monotonicity says about the
derivative `H` of `∇ F` at a point where it exists, the Hessian of `F` represented as an
endomorphism of `E`.

`H` is a positive operator: it is symmetric by Schwarz's theorem, and `⟪H v, v⟫ ≥ 0` because
`t ↦ ⟪∇ F (x + t • v), v⟫` is nondecreasing. In particular `det H ≥ 0`.

## Main statements

* `TauCeti.isPositive_of_hasFDerivAt_gradient` — the Hessian of a convex function is a positive
  operator.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 4.5
  (second-order characterisation of convexity) and §24 (monotonicity of the subdifferential).
-/

public section

namespace TauCeti

open Filter Set InnerProductSpace
open scoped Topology Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → EReal} {H : E →L[ℝ] E}

/-- **The Hessian of a convex function is a positive operator.** Let `f : E → EReal` be convex
and never `⊥`, let `x` be an interior point of its effective domain near which the real
representative `F` is differentiable, and let `H` be the derivative of `∇ F` at `x`. Then `H` is
symmetric and `⟪H v, v⟫ ≥ 0` for every `v`. -/
theorem isPositive_of_hasFDerivAt_gradient (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {x : E} (hx : x ∈ interior {x | f x ≠ ⊤})
    (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun x' => (f x').toReal) y)
    (hH : HasFDerivAt (∇ fun x' => (f x').toReal) H x) : (H : E →ₗ[ℝ] E).IsPositive := by
  refine ⟨isSymmetric_of_hasFDerivAt_gradient hd hH, fun v => ?_⟩
  set F := fun x' => (f x').toReal
  -- `φ t = ⟪v, ∇ F (x + t • v)⟫` has derivative `⟪v, H v⟫` at `0` ...
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hφ : HasDerivAt (fun t : ℝ => ⟪v, ∇ F (x + t • v)⟫_ℝ) ⟪v, H v⟫_ℝ 0 := by
    have := HasFDerivAt.comp_hasDerivAt 0 (innerSL ℝ v).hasFDerivAt
      (HasFDerivAt.comp_hasDerivAt_of_eq 0 hH hline (by simp))
    simpa only [Function.comp_def, innerSL_apply_apply] using this
  -- ... and `φ t ≥ φ 0` for small `t > 0`, by monotonicity of the subdifferential.
  have hmem : ∀ᶠ y in 𝓝 x, ∇ F y ∈ subdifferential (innerₗ E) f y := by
    filter_upwards [hd, isOpen_interior.mem_nhds hx] with y hy hyD
    exact gradient_toReal_mem_subdifferential hf hbot (interior_subset hyD) hy
  have hcont : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) :=
    (Continuous.tendsto' (by fun_prop) 0 x (by simp)).mono_left nhdsWithin_le_nhds
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ t⁻¹ • (⟪v, ∇ F (x + (0 + t) • v)⟫_ℝ - ⟪v, ∇ F (x + (0 : ℝ) • v)⟫_ℝ) := by
    filter_upwards [hcont.eventually hmem, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
    have hmono := apply_le_apply_of_mem_subdifferential (innerₗ E)
      (hmem.self_of_nhds) ht
    simp only [add_sub_cancel_left, innerₗ_apply_apply, real_inner_smul_left] at hmono
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 htpos.le) (by nlinarith)
  simpa [real_inner_comm] using ge_of_tendsto hφ.tendsto_slope_zero_right hslope

end TauCeti
