/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.TestFunction
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.MeasureTheory.Measure.FiniteMeasure

/-!
# The continuity equation with boundary-time terms

The definition `TauCeti.IsContinuityEquation` tests the continuity equation
`∂ₜ μₜ + div (vₜ μₜ) = 0` on `(a, b)` only against test functions supported in `(a, b) × E`, and
says nothing about the measures at the times `a` and `b`. This file removes the support condition
in time, at the cost of boundary terms. For a bounded `C¹` function `u : ℝ × E → ℝ` with bounded
derivative, the function `t ↦ ∫ u (t, x) dμₜ(x)` has weak derivative

`t ↦ ∫ (∂ₜ u (t, x) + ⟨∇ₓ u (t, x), vₜ x⟩) dμₜ(x)`

on `(a, b)`, integrable there (`TauCeti.IsContinuityEquation.hasWeakLineDerivOn_integral`). So
`t ↦ ∫ u (t, ·) dμₜ` agrees almost everywhere with a constant plus a primitive of its weak
derivative. If `t ↦ μₜ` is a curve of finite measures that is narrowly continuous on `[a, b]`, then
`t ↦ ∫ u (t, ·) dμₜ` is continuous on `[a, b]` and agrees with that function everywhere there: for
all `s, t ∈ [a, b]`,

`∫ u (t, x) dμₜ(x) - ∫ u (s, x) dμₛ(x) = ∫_s^t ∫ (∂ₜ u (r, x) + ⟨∇ₓ u (r, x), vᵣ x⟩) dμᵣ(x) dr`

(`TauCeti.IsContinuityEquation.intervalIntegral_integral_fderiv_eq_sub`). The integrand is written,
as in `TauCeti.IsContinuityEquation`, as the space-time derivative `fderiv ℝ u (r, x)` applied to
`(1, v r x)`.

This is the form in which a solution of the continuity equation joins its endpoint laws `μ a` and
`μ b`. In particular, if `u` is a subsolution of a Hamilton–Jacobi equation, in the sense that
`∂ₜ u (t, x) + ⟨∇ₓ u (t, x), w⟩ ≤ L w` for every velocity `w`, the identity bounds
`∫ u (b, ·) d(μ b) - ∫ u (a, ·) d(μ a)` by the action `∫_a^b ∫ L (vₜ x) dμₜ(x) dt`; this is how dual
formulations of transport costs are compared with the action of a velocity field.

## Main results

* `TauCeti.IsContinuityEquation.hasWeakLineDerivOn_integral`: for a bounded `C¹` function `u` with
  bounded derivative, `t ↦ ∫ u (t, ·) dμₜ` has weak derivative
  `t ↦ ∫ (∂ₜ u + ⟨∇ₓ u, vₜ⟩) dμₜ` on `(a, b)`.
* `TauCeti.IsContinuityEquation.intervalIntegral_integral_fderiv_eq_sub`: along a narrowly
  continuous curve of finite measures, the continuity equation integrated from `s` to `t` against
  such a `u` equals the difference of the boundary terms `∫ u (t, ·) dμₜ - ∫ u (s, ·) dμₛ`.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1, Lemma 8.1.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §4.1.
-/

public section

open MeasureTheory Set Function Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {v : ℝ → E → E} {a b : ℝ} {u : ℝ × E → ℝ} {M M' : ℝ}

namespace IsContinuityEquation

/-- **The weak time derivative along a solution.** For a bounded `C¹` function `u` of time and
space with bounded derivative, the function `t ↦ ∫ u (t, x) dμₜ(x)` has weak derivative
`t ↦ ∫ (∂ₜ u (t, x) + ⟨∇ₓ u (t, x), vₜ x⟩) dμₜ(x)` on `(a, b)`, the integrand being written as the
space-time derivative `fderiv ℝ u (t, x)` applied to `(1, v t x)`. -/
theorem hasWeakLineDerivOn_integral {μ : ℝ → Measure E} (h : IsContinuityEquation μ v a b)
    (hu : ContDiff ℝ 1 u) (huM : ∀ q, ‖u q‖ ≤ M) (hDu : ∀ q, ‖fderiv ℝ u q‖ ≤ M') :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ∫ x, u (t, x) ∂μ t)
      (fun t ↦ ∫ x, fderiv ℝ u (t, x) (1, v t x) ∂μ t) 1 := by
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance,
    (h.integrableOn_integral_of_norm_le hu.continuous.stronglyMeasurable huM).locallyIntegrableOn,
    (h.integrableOn_integral_fderiv_of_norm_fderiv_le hDu).locallyIntegrableOn, fun φ ↦ ?_⟩
  have hφs : tsupport (φ : ℝ → ℝ) ⊆ Ioo a b := φ.tsupport_subset
  -- Both pairings vanish outside `(a, b)`, where the test function and its derivative vanish.
  have hφ0 (t : ℝ) (ht : t ∉ Ioo a b) : (φ : ℝ → ℝ) t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h' ↦ ht (hφs h')
  have hφ'0 (t : ℝ) (ht : t ∉ Ioo a b) : deriv (φ : ℝ → ℝ) t = 0 := by
    rw [← lineDeriv_one, lineDeriv_of_notMem_tsupport fun h' ↦ ht (hφs h')]
  have h₁ : ∫ t, deriv (φ : ℝ → ℝ) t * ∫ x, u (t, x) ∂μ t =
      ∫ t in Ioo a b, deriv (φ : ℝ → ℝ) t * ∫ x, u (t, x) ∂μ t :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by rw [hφ'0 t ht, zero_mul]).symm
  have h₂ : ∫ t, (φ : ℝ → ℝ) t * ∫ x, fderiv ℝ u (t, x) (1, v t x) ∂μ t =
      ∫ t in Ioo a b, (φ : ℝ → ℝ) t * ∫ x, fderiv ℝ u (t, x) (1, v t x) ∂μ t :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by rw [hφ0 t ht, zero_mul]).symm
  simp_rw [lineDeriv_one, smul_eq_mul]
  rw [h₁, h₂]
  exact h.integral_deriv_mul_integral_eq_neg (φ.contDiff.of_le (by simp)) hφs hu huM hDu

/-- **The continuity equation with boundary-time terms.** Let `t ↦ νₜ` be a curve of finite
measures, narrowly continuous on `[a, b]`, solving the continuity equation with velocity `v` on
`(a, b)`. For every bounded `C¹` function `u` of time and space with bounded derivative and all
`s, t ∈ [a, b]`,
`∫_s^t ∫ (∂ₜ u (r, x) + ⟨∇ₓ u (r, x), vᵣ x⟩) dνᵣ(x) dr = ∫ u (t, x) dνₜ(x) - ∫ u (s, x) dνₛ(x)`,
the integrand being written as the space-time derivative `fderiv ℝ u (r, x)` applied to
`(1, v r x)`. -/
theorem intervalIntegral_integral_fderiv_eq_sub {ν : ℝ → FiniteMeasure E}
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hu : ContDiff ℝ 1 u) (huM : ∀ q, ‖u q‖ ≤ M) (hDu : ∀ q, ‖fderiv ℝ u q‖ ≤ M') {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∫ r in s..t, ∫ x, fderiv ℝ u (r, x) (1, v r x) ∂(ν r : Measure E) =
      ∫ x, u (t, x) ∂(ν t : Measure E) - ∫ x, u (s, x) ∂(ν s : Measure E) := by
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hM' : 0 ≤ M' := (norm_nonneg _).trans (hDu 0)
  -- `u` is `M'`-Lipschitz in time, uniformly in space.
  have hlip (r r' : ℝ) (x : E) : ‖u (r, x) - u (r', x)‖ ≤ M' * |r - r'| := by
    simpa [Prod.norm_def] using convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun p _ ↦ hud p) (fun p _ ↦ hDu p) (mem_univ (r', x)) (mem_univ (r, x))
  -- Along the narrowly continuous curve, `r ↦ ∫ u (r, ·) dνᵣ` is continuous on `[a, b]`, so it is
  -- the continuous representative of a function with integrable weak derivative.
  have hcont : ContinuousOn (fun r ↦ ∫ x, u (r, x) ∂(ν r : Measure E)) (Icc a b) := by
    intro r₀ hr₀
    let f : E →ᵇ ℝ := .ofNormedAddCommGroup (fun x ↦ u (r₀, x))
      (hu.continuous.comp (Continuous.prodMk_right r₀)) M fun x ↦ huM _
    refine FiniteMeasure.tendsto_integral_of_tendstoUniformly (f := f) (hν r₀ hr₀) ?_
      (Eventually.of_forall fun r ↦
        (hu.continuous.comp (Continuous.prodMk_right r)).aestronglyMeasurable)
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hδ : 0 < ε / (M' + 1) := by positivity
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds r₀ hδ)] with r hr x
    rw [Metric.mem_ball, Real.dist_eq] at hr
    calc dist (f x) (u (r, x)) = ‖u (r₀, x) - u (r, x)‖ := by simp [f, dist_eq_norm]
      _ ≤ M' * |r₀ - r| := hlip _ _ _
      _ ≤ M' * (ε / (M' + 1)) := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hr.le hM'
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  exact (h.hasWeakLineDerivOn_integral hu huM hDu).integral_eq_sub
    (h.integrableOn_integral_fderiv_of_norm_fderiv_le hDu) hcont EventuallyEq.rfl hs ht

end IsContinuityEquation

end TauCeti
