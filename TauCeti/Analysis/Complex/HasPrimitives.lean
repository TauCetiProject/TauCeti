/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Primitives of holomorphic functions

Mathlib's `DifferentiableOn.isExactOn_ball` gives every holomorphic function on a disc a
primitive there.  This file records the gluing consequence: a primitive of the same integrand on
a convex part of the disc extends to a primitive on the whole disc, because two primitives of one
function differ by a constant on a convex set.

## Main results

* `DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter` -- a primitive of a holomorphic integrand
  on `ball c r ∩ U`, for convex `U`, is the restriction of a primitive on `ball c r`.
* `Complex.smul_integral_comp_mul_eq_sub` -- the integral `z ∫₀¹ f(tz) dt` of a derivative `f`
  along the segment from `0` to `z` is the endpoint difference of a primitive.
* `Differentiable.hasDerivAt_smul_integral_comp_mul` -- for an entire `f`, the segment integral
  `w ↦ w ∫₀¹ f(tw) dt` is a primitive of `f`.

The segment-integral lemmas are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMFMathlib/Analysis/Complex/SegmentPrimitive.lean`.
-/

public section

open Complex Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A holomorphic integrand `g` on a disc has a primitive on the disc agreeing with any given
primitive `f` of `g` on the intersection of the disc with a convex set `U`. -/
theorem DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter {f g : ℂ → E} {c : ℂ} {r : ℝ}
    {U : Set ℂ} (hg : DifferentiableOn ℂ g (ball c r)) (hU : Convex ℝ U)
    (hf : ∀ z ∈ ball c r ∩ U, HasDerivWithinAt f (g z) (ball c r ∩ U) z) :
    ∃ G : ℂ → E, (∀ z ∈ ball c r, HasDerivAt G (g z) z) ∧ EqOn G f (ball c r ∩ U) := by
  obtain ⟨P, hP⟩ := hg.isExactOn_ball
  rcases (ball c r ∩ U).eq_empty_or_nonempty with hV | ⟨z₀, hz₀⟩
  · exact ⟨P, hP, by simp [hV]⟩
  refine ⟨fun z ↦ P z + (f z₀ - P z₀), fun z hz ↦ (hP z hz).add_const _, fun z hz ↦ ?_⟩
  have hderiv (w) (hw : w ∈ ball c r ∩ U) :
      HasDerivWithinAt (f - P) 0 (ball c r ∩ U) w := by
    simpa using (hf w hw).sub (hP w hw.1).hasDerivWithinAt
  have := ((convex_ball c r).inter hU).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ ↦ norm_zero.le) hz₀ hz
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, Pi.sub_apply, Pi.sub_apply] at this
  simp [← this]

/-- Integrating a complex derivative along the straight segment from `0` to `z` recovers the
endpoint difference: if `g′ = f` everywhere, then `z ∫₀¹ f(tz) dt = g(z) − g(0)`. -/
theorem Complex.smul_integral_comp_mul_eq_sub {f g : ℂ → E} (hg : ∀ z, HasDerivAt g (f z) z)
    (z : ℂ) : z • (∫ t : ℝ in 0..1, f (t * z)) = g z - g 0 := by
  have hgd : Differentiable ℂ g := fun w => (hg w).differentiableAt
  have hf : Continuous f := by
    rw [← funext fun w => (hg w).deriv]
    exact (Differentiable.deriv hgd).continuous
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => g (u * z)) (z • f (t * z)) t := by
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z t := by
      simpa using (hasDerivAt_id (t : ℂ)).comp_ofReal.mul_const z
    have := ((hg (t * z)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hu
    simpa [Function.comp_def] using this
  have hi : IntervalIntegrable (fun t : ℝ => z • f (t * z)) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => z • f (t * z))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [intervalIntegral.integral_smul] using h

/-- For an entire function `f`, the straight-segment integral `w ↦ w ∫₀¹ f(tw) dt` is a primitive
of `f`. -/
theorem Differentiable.hasDerivAt_smul_integral_comp_mul {f : ℂ → E}
    (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w • (∫ t : ℝ in 0..1, f (t * w))) (f z) z := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hg' (w : ℂ) := hg w (mem_univ w)
  have he : (fun w : ℂ => w • (∫ t : ℝ in 0..1, f (t * w))) = fun w => g w - g 0 :=
    funext (Complex.smul_integral_comp_mul_eq_sub hg')
  rw [he]
  exact (hg' z).sub_const _
