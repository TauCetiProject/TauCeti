/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv

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

Conversely, a real function on an open convex set whose gradient has a derivative `H x` with
`⟪H x v, v⟫ ≥ 0` at every point is convex: along each segment it has a nonnegative second
derivative.

## Main statements

* `TauCeti.isPositive_of_hasFDerivAt_gradient` and
  `ConvexOn.isPositive_of_hasFDerivAt_gradient` — the Hessian of a convex function, extended-real
  or real-valued, is a positive operator;
* `TauCeti.convexOn_of_hasFDerivAt_gradient` — a function with positive Hessian on an open convex
  set is convex there.

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

/-- **The Hessian of a real convex function is a positive operator.** Let `F : E → ℝ` be convex on
a neighbourhood `s` of `x` and differentiable near `x`, and let `H` be the derivative of `∇ F` at
`x`. Then `H` is symmetric and `⟪H v, v⟫ ≥ 0` for every `v`. -/
theorem _root_.ConvexOn.isPositive_of_hasFDerivAt_gradient {s : Set E} {F : E → ℝ}
    (hF : ConvexOn ℝ s F) {x : E} (hx : s ∈ 𝓝 x) (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y)
    (hH : HasFDerivAt (∇ F) H x) : (H : E →ₗ[ℝ] E).IsPositive := by
  classical
  -- Extend `F` by `⊤` off the interior `U` of `s`; near `x` its real representative is `F`.
  set U := interior s
  have hU : ConvexOn ℝ U F := hF.subset interior_subset hF.1.interior
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.2 hx
  have hF' : (fun x' => (if x' ∈ U then (F x' : EReal) else ⊤).toReal) =ᶠ[𝓝 x] F :=
    eventually_of_mem (isOpen_interior.mem_nhds hxU) fun x' (hx' : x' ∈ U) => by
      simp only [hx', ite_true, EReal.toReal_coe]
  refine TauCeti.isPositive_of_hasFDerivAt_gradient (convex_epigraph_ite hU)
    ite_ne_bot ?_ ?_ (hH.congr_of_eventuallyEq hF'.gradient)
  · rwa [setOf_ite_ne_top, isOpen_interior.interior_eq]
  · filter_upwards [hd, hF'.eventuallyEq_nhds] with y hy hFy
    exact hy.congr_of_eventuallyEq hFy

/-- **A function with positive Hessian is convex.** Let `s` be an open convex set and let
`F : E → ℝ` be differentiable on `s`, with the gradient `∇ F` having derivative `H x` at each
`x ∈ s`. If `⟪H x v, v⟫ ≥ 0` for every `x ∈ s` and every `v`, then `F` is convex on `s`. This is
the converse of `ConvexOn.isPositive_of_hasFDerivAt_gradient`. -/
theorem convexOn_of_hasFDerivAt_gradient {s : Set E} (hs : Convex ℝ s) (hso : IsOpen s)
    {F : E → ℝ} {H : E → E →L[ℝ] E} (hF : ∀ x ∈ s, DifferentiableAt ℝ F x)
    (hH : ∀ x ∈ s, HasFDerivAt (∇ F) (H x) x) (hpos : ∀ x ∈ s, ∀ v, 0 ≤ ⟪H x v, v⟫_ℝ) :
    ConvexOn ℝ s F := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  -- Restrict `F` to the line through `x` and `y`, on the open convex set `D` of parameters `t`
  -- with `lineMap x y t ∈ s`; there it has the nonnegative second derivative
  -- `⟪y - x, H (lineMap x y t) (y - x)⟫`.
  set ℓ : ℝ → E := ⇑(AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
  set D := ℓ ⁻¹' s
  have hD : Convex ℝ D := hs.affine_preimage (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
  have hDo : IsOpen D := hso.preimage (AffineMap.lineMap_continuous (R := ℝ))
  have hℓ : ∀ t, HasDerivAt ℓ (y - x) t := fun t => AffineMap.hasDerivAt_lineMap
  have h₁ : ∀ t ∈ D, HasDerivAt (F ∘ ℓ) ⟪y - x, ∇ F (ℓ t)⟫_ℝ t := fun t ht => by
    have := ((hF _ ht).hasGradientAt.hasFDerivAt).comp_hasDerivAt t (hℓ t)
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using this
  have h₂ : ∀ t ∈ D, HasDerivAt (fun t => ⟪y - x, ∇ F (ℓ t)⟫_ℝ) ⟪y - x, H (ℓ t) (y - x)⟫_ℝ t :=
    fun t ht => by
      have := HasFDerivAt.comp_hasDerivAt t (innerSL ℝ (y - x)).hasFDerivAt
        ((hH _ ht).comp_hasDerivAt t (hℓ t))
      simpa only [Function.comp_def, innerSL_apply_apply] using this
  have hconv : ConvexOn ℝ D (F ∘ ℓ) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := fun t => ⟪y - x, ∇ F (ℓ t)⟫_ℝ)
      (f'' := fun t => ⟪y - x, H (ℓ t) (y - x)⟫_ℝ) hD
      (fun t ht => (h₁ t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
      (fun t ht => ?_) <;> rw [hDo.interior_eq] at ht
    · exact (h₁ t ht).hasDerivWithinAt
    · exact (h₂ t ht).hasDerivWithinAt
    · rw [real_inner_comm]
      exact hpos _ ht _
  have h0 : (0 : ℝ) ∈ D := by simpa [D, ℓ] using hx
  have h1 : (1 : ℝ) ∈ D := by simpa [D, ℓ] using hy
  have := hconv.2 h0 h1 ha hb hab
  simp only [Function.comp_apply, smul_eq_mul, mul_zero, zero_add, ℓ,
    AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at this
  rwa [AffineMap.lineMap_apply_module, mul_one, show 1 - b = a by linarith] at this

end TauCeti
