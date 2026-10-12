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

* `H` is a positive operator: it is symmetric by Schwarz's theorem, and `⟪H v, v⟫ ≥ 0` because
  `t ↦ ⟪∇ F (x + t • v), v⟫` is nondecreasing. In particular `det H ≥ 0`.
* If `∇ F` takes the same value `y` at two points `x₁ ≠ x₂` of `D`, then `y` is a subgradient
  at every point of the segment joining them, so `∇ F` is constant on that segment and `H`
  kills `x₂ - x₁`. In particular `∇ F` is injective on the set where `det H ≠ 0`.

These are the two facts that identify the Aleksandrov Monge–Ampère measure of a twice
differentiable convex function with `det (D²F) dx`.

## Main statements

* `TauCeti.isPositive_of_hasFDerivAt_gradient` — the Hessian of a convex function is a positive
  operator;
* `TauCeti.apply_sub_eq_zero_of_gradient_eq` — if the gradient agrees at `x₁` and `x₂`, the
  Hessian at `x₁` vanishes on `x₂ - x₁`.

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

/-- **The Hessian kills the direction of a flat segment.** Let `f : E → EReal` be convex and
never `⊥`, and let `x₁, x₂` be interior points of its effective domain such that the real
representative `F` is differentiable along the segment `[x₁, x₂]` and `∇ F x₁ = ∇ F x₂`. If `H`
is the derivative of `∇ F` at `x₁`, then `H (x₂ - x₁) = 0`. So when `x₁ ≠ x₂` the Hessian at
`x₁` is degenerate: two points at which the Hessian is nondegenerate have distinct gradients. -/
theorem apply_sub_eq_zero_of_gradient_eq (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {x₁ x₂ : E} (hx₁ : x₁ ∈ interior {x | f x ≠ ⊤})
    (hx₂ : x₂ ∈ interior {x | f x ≠ ⊤})
    (hd : ∀ y ∈ segment ℝ x₁ x₂, DifferentiableAt ℝ (fun x' => (f x').toReal) y)
    (hg : ∇ (fun x' => (f x').toReal) x₁ = ∇ (fun x' => (f x').toReal) x₂)
    (hH : HasFDerivAt (∇ fun x' => (f x').toReal) H x₁) : H (x₂ - x₁) = 0 := by
  set F := fun x' => (f x').toReal
  -- The common gradient `y` is a subgradient at each point of the segment, hence the gradient.
  have hy : ∀ z ∈ segment ℝ x₁ x₂, ∇ F z = ∇ F x₁ := by
    have h₁ := gradient_toReal_mem_subdifferential hf hbot (interior_subset hx₁)
      (hd x₁ (left_mem_segment ℝ x₁ x₂))
    have h₂ := gradient_toReal_mem_subdifferential hf hbot (interior_subset hx₂)
      (hd x₂ (right_mem_segment ℝ x₁ x₂))
    rw [← hg] at h₂
    intro z hz
    have hzD := (convex_setOf_ne_top hf).interior.segment_subset hx₁ hx₂ hz
    exact gradient_toReal_eq_of_mem_subdifferential
      ((convex_setOf_mem_subdifferential (innerₗ E) hf _).segment_subset h₁ h₂ hz)
      (mem_interior_iff_mem_nhds.1 hzD) (hd z hz)
  -- So `t ↦ ∇ F (x₁ + t • (x₂ - x₁))` is constant on `[0, 1]`, with derivative `H (x₂ - x₁)`.
  have hline : HasDerivAt (fun t : ℝ => x₁ + t • (x₂ - x₁)) (x₂ - x₁) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x₂ - x₁)).const_add x₁
  have hder : HasDerivAt (fun t : ℝ => ∇ F (x₁ + t • (x₂ - x₁))) (H (x₂ - x₁)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq 0 hH hline (by simp)
  have hconst : HasDerivWithinAt (fun t : ℝ => ∇ F (x₁ + t • (x₂ - x₁))) 0 (Icc 0 1) 0 :=
    (hasDerivWithinAt_const 0 (Icc 0 1) (∇ F x₁)).congr
      (fun t ht => hy _ (segment_eq_image' ℝ x₁ x₂ ▸ mem_image_of_mem _ ht)) (by simp)
  exact (uniqueDiffOn_Icc zero_lt_one 0 (left_mem_Icc.2 zero_le_one)).eq_deriv _
    hder.hasDerivWithinAt hconst

end TauCeti
