/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Trajectory
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.Examples.ExponentialConvergence
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Gradient trajectories of the quadratic well

This file computes the negative gradient flow of `f(x) = x²` on `ℝ`, for the standard metric and
for its constant multiples, and uses it to test the convergence and decay theorems for gradient
trajectories of Morse functions
(`TauCeti.IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient` and
`TauCeti.IsMorse.exists_riemannianEDist_le_mul_exp_of_tendsto_neg_mgradient`).

* **The Morse data.** The function `x²` is a Morse function (`TauCeti.isMorse_sq_real`) whose
  only critical point is `0` (`TauCeti.criticalPoints_sq_real`, `TauCeti.mfderiv_sq_real_zero`),
  a minimum of index `0` (`TauCeti.manifoldMorseIndex_sq_real_zero`); its derivative is
  `v ↦ 2 x v` (`TauCeti.mvfderiv_sq_real_apply`). The inverted well `-x²` is a Morse function
  (`TauCeti.isMorse_neg_sq_real`) with the same critical point
  (`TauCeti.criticalPoints_neg_sq_real`), a maximum of index `1`
  (`TauCeti.manifoldMorseIndex_neg_sq_real`).
* **The trajectories.** The trajectory of `-grad f`
  through `x₀` is `t ↦ x₀ exp (-2 t)`, defined for all time
  (`TauCeti.maximalIntegralCurve_neg_mgradient_sq`). For `t ≥ 0` it stays in
  `[-|x₀|, |x₀|]` (`TauCeti.mapsTo_maximalIntegralCurve_neg_mgradient_sq`) and it converges to
  `0` (`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_sq`).
* **Energy, tail length and distance.** Along the trajectory the energy `f(γ t) - f(0)` is
  `x₀² exp (-4 t)` (`TauCeti.sq_maximalIntegralCurve_neg_mgradient_sq`). The length of the piece
  between the times `t ≤ s` is `|x₀| (exp (-2 t) - exp (-2 s))`
  (`TauCeti.pathELength_maximalIntegralCurve_neg_mgradient_sq`), so the tail length from time `t`
  on is `|x₀| exp (-2 t)` (`TauCeti.iSup_pathELength_maximalIntegralCurve_neg_mgradient_sq`). This
  is also the Riemannian distance from `γ t` to `0`
  (`TauCeti.riemannianEDist_maximalIntegralCurve_neg_mgradient_sq`), and it is the square root of
  the energy. So the trajectory converges at the rate `2`, the Hessian eigenvalue at `0`, and for
  `x₀ ≠ 0` at no faster rate
  (`TauCeti.not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq`). For
  `x₀ = 0` the trajectory is the equilibrium at the critical point: its energy and tail length
  vanish, and the decay bound holds with the constant `0`.
* **A forward curve with an endpoint.** The convergence and decay theorems are stated for curves
  that solve the curve equation on `[0, ∞)`, with a one-sided derivative at the endpoint `0`, and
  a prescribed continuation of such a curve to negative times need not be an integral curve. The
  curve `γ(t) = x₀ exp (-2 max(t, 0))`, which is `x₀ exp (-2 t)` for `t ≥ 0` and the constant
  `x₀` for `t < 0`, solves the curve equation on `[0, ∞)`
  (`TauCeti.isMIntegralCurveOn_Ici_neg_mgradient_sq`). For `x₀ ≠ 0` its left derivative at `0`
  vanishes while `-grad f (x₀) = -2 x₀` does not, so it is an integral curve on no open interval
  containing `0` (`TauCeti.not_isMIntegralCurveOn_Ioo_neg_mgradient_sq`). The maximal trajectory
  `Γ` through `γ(1)` agrees with `s ↦ γ(1 + s)` exactly for `s ≥ -1`
  (`TauCeti.maximalIntegralCurve_neg_mgradient_sq_eq_iff`). This is why those theorems compare a
  forward curve with the maximal trajectory through one of its values at a positive time.
* **A rescaled metric.** The rate of convergence depends on the metric, through the Hessian read
  in it. For `a > 0`, give `ℝ` the metric `a dx²` (`TauCeti.scaledLineMetric`), on the copy
  `TauCeti.WithMetric (scaledLineMetric ha)` of `ℝ`. Then `grad x² = 2 x / a`
  (`TauCeti.mgradient_sq_scaledLineMetric`), the trajectory through `x₀` is `t ↦ x₀ exp (-2 t / a)`
  (`TauCeti.maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`), and it converges to `0`
  (`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`). The Riemannian
  distance of `a dx²` is `√a |x - y|` (`TauCeti.riemannianEDist_toWithMetric_scaledLineMetric`), so
  the trajectory is at distance `√a |x₀| exp (-2 t / a)` from `0`
  (`TauCeti.riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`), and for
  `x₀ ≠ 0` no rate faster than `2 / a` holds
  (`not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`).
  For `a = 4` the trajectory is `x₀ exp (-t / 2)` at distance `2 |x₀| exp (-t / 2)`: the rate `2`
  of the standard metric is not preserved under rescaling the metric.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, second edition, Academic Press, 2004, Chapter 9 (gradient systems).
-/

public section

open Filter MeasureTheory Set Topology TauCeti.Manifold
open scoped Bundle ContDiff ENNReal Manifold

namespace TauCeti

/-- For the standard metric on `ℝ`, the negative gradient of `x ↦ x²` at `x` is `-2 x`. -/
theorem neg_mgradient_sq_real_apply (x : ℝ) :
    (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x = (-(2 * x) : ℝ) := by
  rw [Pi.neg_apply, mgradient_eq_gradient_of_eq rfl, gradient_eq_deriv']
  simp only [differentiableAt_fun_id, deriv_fun_pow, deriv_id'', Nat.cast_ofNat, mul_one,
    Nat.add_one_sub_one, pow_one]
  -- Both sides are the real number `-2 x`, read in `ℝ` and in its tangent space.
  rfl

/-- The function `x ↦ x²` on `ℝ` has the single critical point `0`. -/
theorem criticalPoints_sq_real : criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) = {0} := by
  ext x
  rw [mem_criticalPoints_iff_fderiv_eq_zero, ← toSpanSingleton_deriv, mem_singleton_iff]
  constructor
  · intro h
    simpa using congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) h
  · rintro rfl
    ext
    simp

/-- **The function `x ↦ x²` on `ℝ` is a Morse function**: its only critical point `0` has second
derivative `2 ≠ 0`. -/
theorem isMorse_sq_real : IsMorse 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) := by
  refine isMorse_modelSpace_iff.2
    ⟨contDiff_id.pow 2, hasNondegenerateCriticalPointsOn_iff.2 fun x _ hx ↦ ?_⟩
  rw [isNondegenerateCriticalPoint_real_iff (by fun_prop)]
  have hx0 : x = 0 := by simpa using congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hx
  subst hx0
  refine ⟨by simp, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv (fun y : ℝ ↦ y ^ 2) = fun y ↦ 2 * y := by
    ext y
    simp
  rw [hd]
  simp

/-- The derivative of `x ↦ x²` on `ℝ` at `x`, applied to a tangent vector `v`, is `2 x v`. -/
theorem mvfderiv_sq_real_apply (x v : ℝ) :
    mvfderiv 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x v = 2 * x * v := by
  refine (mvfderiv_eq_fderiv_apply _ x v).trans ?_
  rw [fderiv_eq_smul_deriv]
  simp
  ring

/-- `0` is the critical point of `x ↦ x²` on `ℝ`. -/
theorem mfderiv_sq_real_zero : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ) (fun y : ℝ ↦ y ^ 2) 0 = 0 := by
  refine mvfderiv_eq_zero_iff.1 (ContinuousLinearMap.ext fun v ↦ ?_)
  simp

/-- The Morse index of `x ↦ x²` at its minimum `0` is `0`. -/
theorem manifoldMorseIndex_sq_real_zero :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) 0 = 0 :=
  manifoldMorseIndex_eq_zero_of_isLocalMin (contDiff_id.pow 2).contMDiff.contMDiffAt
    BoundarylessManifold.isInteriorPoint
    (Eventually.of_forall fun y ↦ by simp [sq_nonneg])

/-- The inverted well `x ↦ -x²` is a Morse function on `ℝ`. -/
theorem isMorse_neg_sq_real : IsMorse 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) :=
  isMorse_sq_real.neg

/-- The only critical point of the inverted well is `0`. -/
theorem criticalPoints_neg_sq_real : criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) = {0} :=
  (criticalPoints_neg (f := fun x : ℝ ↦ x ^ 2)).trans criticalPoints_sq_real

/-- The critical point `0` of the inverted well is a maximum: its Morse index is `1`. -/
theorem manifoldMorseIndex_neg_sq_real :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) 0 = 1 := by
  have hcrit : (0 : ℝ) ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) := by
    simp [criticalPoints_sq_real]
  have hnd := isMorse_sq_real.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hcrit)
  have h := hnd.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  rwa [manifoldMorseIndex_sq_real_zero, Module.finrank_self] at h

/-! ### The trajectories -/

/-- **The trajectories of the quadratic well.** For the standard metric, the trajectory of
`-grad x²` through `x₀` is `t ↦ x₀ exp (-2 t)`, defined for all time. -/
theorem maximalIntegralCurve_neg_mgradient_sq (x₀ t : ℝ) :
    maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t =
      x₀ * Real.exp (-(2 * t)) := by
  have hb : 0 < |t| + 1 := by positivity
  simpa using eqOn_maximalIntegralCurve_neg_mgradient_of_hasDerivAt
    (f := fun y : ℝ ↦ y ^ 2) (by fun_prop) (a := -(|t| + 1)) (b := |t| + 1) ⟨neg_lt_zero.2 hb, hb⟩
    (fun s _ ↦ (hasDerivAt_mul_exp_neg_mul 2 x₀ s).congr_deriv (by simp [gradient_eq_deriv']))
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- The trajectories of the quadratic well, as functions of time. -/
private theorem maximalIntegralCurve_neg_mgradient_sq_eq (x₀ : ℝ) :
    maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ =
      fun t ↦ x₀ * Real.exp (-(2 * t)) :=
  funext (maximalIntegralCurve_neg_mgradient_sq x₀)

/-- The forward trajectory of `-grad x²` through `x₀` stays in the compact interval
`[-|x₀|, |x₀|]`. -/
theorem mapsTo_maximalIntegralCurve_neg_mgradient_sq (x₀ : ℝ) :
    MapsTo (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) (Ici 0)
      (Icc (-|x₀|) |x₀|) := by
  intro t (ht : 0 ≤ t)
  rw [mem_Icc, ← abs_le, maximalIntegralCurve_neg_mgradient_sq, abs_mul, Real.abs_exp]
  exact mul_le_of_le_one_right (abs_nonneg x₀) (Real.exp_le_one_iff.2 (by linarith))

/-- The trajectory of `-grad x²` through any `x₀` converges to the critical point `0`. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_sq (x₀ : ℝ) :
    Tendsto (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) atTop (𝓝 0) := by
  rw [maximalIntegralCurve_neg_mgradient_sq_eq]
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul x₀

/-! ### Energy, tail length and distance -/

/-- **The energy of a trajectory of the quadratic well.** Along the trajectory of `-grad x²`
through `x₀`, the energy `f(γ t) - f(0) = γ(t)²` is `x₀² exp (-4 t)`. -/
theorem sq_maximalIntegralCurve_neg_mgradient_sq (x₀ t : ℝ) :
    maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t ^ 2 =
      x₀ ^ 2 * Real.exp (-(4 * t)) := by
  rw [maximalIntegralCurve_neg_mgradient_sq, mul_pow, ← Real.exp_natCast_mul]
  ring_nf

/-- The length of the trajectory of `-grad x²` through `x₀` between the times `t ≤ s` is
`|x₀| (exp (-2 t) - exp (-2 s))`. -/
theorem pathELength_maximalIntegralCurve_neg_mgradient_sq (x₀ : ℝ) {t s : ℝ} (hts : t ≤ s) :
    Manifold.pathELength 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) t s =
      ENNReal.ofReal (|x₀| * (Real.exp (-(2 * t)) - Real.exp (-(2 * s)))) := by
  -- The speed of the trajectory at time `u` is `2 |x₀| exp (-2 u)`.
  have hspeed : ∀ u, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u ↦ x₀ * Real.exp (-(2 * u))) u 1‖ₑ =
      ENNReal.ofReal (2 * |x₀| * Real.exp (-(2 * u))) := by
    intro u
    -- The unit tangent vector at `u` is the real number `1`.
    have h1 : NormedSpace.fromTangentSpace u (1 : TangentSpace 𝓘(ℝ, ℝ) u) = (1 : ℝ) := rfl
    rw [mfderiv_eq_fderiv, eNorm_tangentSpace_vectorSpace,
      (hasDerivAt_mul_exp_neg_mul 2 x₀ u).hasFDerivAt.fderiv, ← ofReal_norm]
    simp [h1]
    ring_nf
  have hcont : Continuous fun u : ℝ ↦ 2 * |x₀| * Real.exp (-(2 * u)) := by fun_prop
  -- The antiderivative `-|x₀| exp (-2 u)` of the speed.
  have hF : ∀ u, HasDerivAt (fun u ↦ -(|x₀| * Real.exp (-(2 * u))))
      (2 * |x₀| * Real.exp (-(2 * u))) u := by
    intro u
    have h : HasDerivAt (fun s : ℝ ↦ -(2 * s)) (-2) u := by
      simpa using ((hasDerivAt_id u).const_mul 2).fun_neg
    convert (h.exp.const_mul |x₀|).neg using 1
    ring
  rw [maximalIntegralCurve_neg_mgradient_sq_eq, Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  simp_rw [hspeed]
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
      (Eventually.of_forall fun u ↦ by positivity),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hts,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hF u)
      (hcont.intervalIntegrable t s)]
  ring_nf

/-- **The tail length of a trajectory of the quadratic well.** From time `t` on, the trajectory
of `-grad x²` through `x₀` has length `|x₀| exp (-2 t)`. -/
theorem iSup_pathELength_maximalIntegralCurve_neg_mgradient_sq (x₀ t : ℝ) :
    ⨆ s, Manifold.pathELength 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) t s =
      ENNReal.ofReal (|x₀| * Real.exp (-(2 * t))) := by
  refine le_antisymm (iSup_le fun s ↦ ?_) ?_
  · rcases le_or_gt t s with hts | hst
    · rw [pathELength_maximalIntegralCurve_neg_mgradient_sq x₀ hts]
      gcongr
      exact sub_le_self _ (Real.exp_pos _).le
    · rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc, Icc_eq_empty hst.not_ge]
      simp
  · -- The lengths up to time `s` tend to the claimed value as `s → ∞`.
    have hlim : Tendsto (fun s ↦ ENNReal.ofReal (|x₀| * (Real.exp (-(2 * t)) -
        Real.exp (-(2 * s))))) atTop (𝓝 (ENNReal.ofReal (|x₀| * Real.exp (-(2 * t))))) := by
      refine ENNReal.tendsto_ofReal ?_
      simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_sub
          (Real.exp (-(2 * t)))).const_mul |x₀|
    refine le_of_tendsto' hlim fun s ↦ ?_
    rcases le_or_gt t s with hts | hst
    · rw [← pathELength_maximalIntegralCurve_neg_mgradient_sq x₀ hts]
      exact le_iSup (fun s ↦ Manifold.pathELength 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) t s) s
    · -- Before time `t` the length difference is negative, so its positive part is `0`.
      have : |x₀| * (Real.exp (-(2 * t)) - Real.exp (-(2 * s))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
          (sub_nonpos.2 (Real.exp_le_exp.2 (by linarith)))
      rw [ENNReal.ofReal_of_nonpos this]
      exact bot_le

/-- The trajectory of `-grad x²` through `x₀` is at Riemannian distance exactly
`|x₀| exp (-2 t)` from the critical point `0` at time `t`. -/
theorem riemannianEDist_maximalIntegralCurve_neg_mgradient_sq (x₀ t : ℝ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t) 0 =
      ENNReal.ofReal (|x₀| * Real.exp (-(2 * t))) := by
  rw [maximalIntegralCurve_neg_mgradient_sq, ← IsRiemannianManifold.out, edist_dist,
    dist_zero_right, Real.norm_eq_abs, abs_mul, Real.abs_exp]

/-- **The rate `2` is sharp.** For `x₀ ≠ 0` and `μ > 2`, the distance from the trajectory of
`-grad x²` through `x₀` to the critical point `0` is not bounded by `C exp (-μ t)` for large `t`,
for any `C > 0`. -/
theorem not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq
    {x₀ μ : ℝ} (hx₀ : x₀ ≠ 0) (hμ : 2 < μ) :
    ¬ ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist 𝓘(ℝ, ℝ)
          (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t) 0 ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  -- The distance is the same as along the stable trajectory of the saddle through `(x₀, 0)`.
  rintro ⟨C, hC, h⟩
  refine not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_sub_sq hx₀ hμ
    ⟨C, hC, h.mono fun t ht ↦ ?_⟩
  rwa [riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_sub_sq,
    ← riemannianEDist_maximalIntegralCurve_neg_mgradient_sq]

/-! ### A forward curve with an endpoint -/

/-- The curve `t ↦ x₀ exp (-2 max(t, 0))` solves the curve equation of `-grad x²` on `[0, ∞)`,
with a one-sided derivative at `0`. -/
theorem isMIntegralCurveOn_Ici_neg_mgradient_sq (x₀ : ℝ) :
    IsMIntegralCurveOn (fun t ↦ x₀ * Real.exp (-(2 * max t 0)))
      (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) (Ici 0) := by
  rw [isMIntegralCurveOn_iff_isIntegralCurveOn]
  intro t (ht : 0 ≤ t)
  have heq : ∀ u ∈ Ici (0 : ℝ),
      x₀ * Real.exp (-(2 * max u 0)) = x₀ * Real.exp (-(2 * u)) := fun u (hu : 0 ≤ u) ↦ by
    rw [max_eq_left hu]
  refine ((hasDerivAt_mul_exp_neg_mul 2 x₀ t).hasDerivWithinAt.congr_of_mem heq
    (mem_Ici.mpr ht)).congr_deriv ?_
  dsimp only
  rw [neg_mgradient_sq_real_apply, max_eq_left ht]

/-- **A prescribed backward continuation need not be an integral curve.** For `x₀ ≠ 0`, the curve
`t ↦ x₀ exp (-2 max(t, 0))` is an integral curve of `-grad x²` on no open interval containing
`0`, although its forward part extends to the trajectory `t ↦ x₀ exp (-2 t)`: it is constant for
`t ≤ 0`, so its left derivative at `0` vanishes, while `-grad x²` is `-2 x₀ ≠ 0` there. -/
theorem not_isMIntegralCurveOn_Ioo_neg_mgradient_sq {x₀ a b : ℝ} (hx₀ : x₀ ≠ 0) (ha : a < 0)
    (hb : 0 < b) :
    ¬ IsMIntegralCurveOn (fun t ↦ x₀ * Real.exp (-(2 * max t 0)))
      (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) (Ioo a b) := by
  rw [isMIntegralCurveOn_iff_isIntegralCurveOn]
  intro h
  have h0 := ((h 0 ⟨ha, hb⟩).hasDerivAt (Ioo_mem_nhds ha hb)).hasDerivWithinAt (s := Iic 0)
  -- To the left of `0` the curve is the constant `x₀`.
  have hconst : HasDerivWithinAt (fun t ↦ x₀ * Real.exp (-(2 * max t 0))) 0 (Iic 0) 0 :=
    (hasDerivWithinAt_const 0 (Iic 0) x₀).congr_of_mem
      (fun u (hu : u ≤ 0) ↦ by simp [max_eq_right hu]) (mem_Iic.mpr le_rfl)
  have := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _ h0 hconst
  dsimp only at this
  rw [neg_mgradient_sq_real_apply] at this
  simp only [max_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  exact hx₀ (by linarith)

/-- **The maximal trajectory through a later value.** For `x₀ ≠ 0`, write
`γ(t) = x₀ exp (-2 max(t, 0))`. The maximal trajectory of `-grad x²` through `γ(1)` agrees with
`s ↦ γ(1 + s)` exactly for `s ≥ -1`: it continues `x₀ exp (-2 (1 + s))` backwards past the time
`-1`, where `γ` is constant. -/
theorem maximalIntegralCurve_neg_mgradient_sq_eq_iff {x₀ : ℝ} (hx₀ : x₀ ≠ 0) (s : ℝ) :
    maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2))
        (x₀ * Real.exp (-(2 * max 1 0))) s = x₀ * Real.exp (-(2 * max (1 + s) 0)) ↔
      -1 ≤ s := by
  rw [maximalIntegralCurve_neg_mgradient_sq, max_eq_left zero_le_one, mul_assoc,
    ← Real.exp_add]
  constructor
  · intro h
    by_contra hs
    rw [max_eq_right (by linarith : 1 + s ≤ 0), mul_zero, neg_zero, Real.exp_zero,
      mul_right_inj' hx₀, Real.exp_eq_one_iff] at h
    exact hs (by linarith)
  · intro hs
    rw [max_eq_left (by linarith : 0 ≤ 1 + s)]
    ring_nf

/-! ### A rescaled metric -/

section ScaledMetric

open Bundle WithMetric

variable {a : ℝ} (ha : 0 < a)

/-- The metric `a dx²` on `ℝ`, for `a > 0`: the standard metric rescaled by the constant `a`. Its
copy of `ℝ` is `WithMetric (scaledLineMetric ha)`. -/
noncomputable def scaledLineMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ω ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
  (riemannianMetricVectorSpace ℝ).rescale (fun _ ↦ a) contMDiff_const fun _ ↦ ha

/-- The inner products of `scaledLineMetric`: `⟪v, w⟫ₓ = a v w`. -/
@[simp]
theorem scaledLineMetric_inner (x v w : ℝ) : (scaledLineMetric ha).inner x v w = a * (v * w) := by
  unfold scaledLineMetric
  -- The tangent space of `ℝ` at `x` is `ℝ` by definition, so `v` and `w` are tangent vectors.
  erw [ContMDiffRiemannianMetric.rescale_inner]
  -- The standard inner product of `ℝ` is `w * v` by definition.
  exact congrArg (a * ·) (mul_comm w v)

/-- **The gradient for the metric `a dx²`.** The gradient of `x ↦ x²` at `x` is `2 x / a`. -/
theorem mgradient_sq_scaledLineMetric (x : WithMetric (scaledLineMetric ha)) :
    mgradient 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2) x =
      (2 / a * x.ofWithMetric : ℝ) := by
  have hf : (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2) =
      (fun y : ℝ ↦ y ^ 2) ∘ ofWithMetric := rfl
  -- The tangent vectors of the copy of `ℝ` are real numbers by definition; the rewrites below
  -- see through this identification.
  have hd (v : ℝ) :
      mvfderiv 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2) x v =
        2 * x.ofWithMetric * v := by
    erw [hf, mvfderiv_comp_ofWithMetric_apply, mfderiv_ofWithMetric_apply,
      mvfderiv_eq_fderiv_apply]
    simp only [differentiableAt_fun_id, fderiv_fun_pow, fderiv_fun_id, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  refine (eq_mgradient_iff.2 fun (v : ℝ) ↦ ?_).symm
  erw [inner_def, mfderiv_ofWithMetric_apply, mfderiv_ofWithMetric_apply, scaledLineMetric_inner,
    hd]
  field_simp

/-- For the metric `a dx²`, the negative gradient of `x ↦ x²` at `x` is `-2 x / a`. -/
private theorem neg_mgradient_sq_scaledLineMetric_apply (x : WithMetric (scaledLineMetric ha)) :
    (-mgradient 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2)) x =
      (-(2 / a * x.ofWithMetric) : ℝ) := by
  rw [Pi.neg_apply, mgradient_sq_scaledLineMetric ha]
  -- Both sides are the real number `-2 x / a`, read in `ℝ` and in a tangent space of the copy.
  rfl

/-- For the metric `a dx²`, the curve `t ↦ x₀ exp (-2 t / a)` is a trajectory of `-grad x²`. -/
private theorem isMIntegralCurve_neg_mgradient_sq_scaledLineMetric (x₀ : ℝ) :
    IsMIntegralCurve (fun t ↦ toWithMetric (scaledLineMetric ha) (x₀ * Real.exp (-(2 / a * t))))
      (-mgradient 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2)) := by
  intro t
  have h := (hasMFDerivAt_toWithMetric (g := scaledLineMetric ha) _).comp t
    (hasDerivAt_mul_exp_neg_mul (2 / a) x₀ t).hasFDerivAt.hasMFDerivAt
  refine h.congr_mfderiv ?_
  -- The derivative of `toWithMetric` is the identity of `ℝ`, read in the tangent spaces.
  erw [neg_mgradient_sq_scaledLineMetric_apply]
  exact ContinuousLinearMap.id_comp _

/-- **The trajectories of the quadratic well for the metric `a dx²`.** The trajectory of `-grad x²`
through `x₀` is `t ↦ x₀ exp (-2 t / a)`, defined for all time. For `a = 4` it is
`t ↦ x₀ exp (-t / 2)`. -/
theorem maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (x₀ t : ℝ) :
    maximalIntegralCurve
        (-mgradient 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2))
        (toWithMetric _ x₀) t =
      toWithMetric _ (x₀ * Real.exp (-(2 / a * t))) := by
  have hb : 0 < |t| + 1 := by positivity
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ) 2
      (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2) :=
    (contDiff_id.pow 2).contMDiff.comp contMDiff_ofWithMetric
  simpa using ((isMIntegralCurve_neg_mgradient_sq_scaledLineMetric ha x₀).isMIntegralCurveOn
    (Ioo (-(|t| + 1)) (|t| + 1))).eqOn_maximalIntegralCurve (contMDiff_neg_mgradient_one hf)
    ⟨neg_lt_zero.2 hb, hb⟩ (by simp)
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- For the metric `a dx²`, the trajectory of `-grad x²` through any `x₀` converges to the critical
point `0`. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (x₀ : ℝ) :
    Tendsto (maximalIntegralCurve
        (-mgradient 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2))
        (toWithMetric _ x₀)) atTop (𝓝 (toWithMetric _ 0)) := by
  rw [funext (maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric ha x₀)]
  refine (continuous_toWithMetric.tendsto 0).comp ?_
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (div_pos two_pos ha))).const_mul x₀

/-- **The distance for the metric `a dx²`.** The Riemannian distance between `x` and `y` is
`√a |x - y|`. -/
theorem riemannianEDist_toWithMetric_scaledLineMetric (x y : ℝ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℝ) (toWithMetric (scaledLineMetric ha) x)
        (toWithMetric (scaledLineMetric ha) y) =
      ENNReal.ofReal (√a * |x - y|) := by
  have hC : (Real.toNNReal √a : ℝ) = √a := Real.coe_toNNReal _ (Real.sqrt_nonneg a)
  rw [riemannianEDist_toWithMetric_eq_mul (C := Real.toNNReal √a)
      (by simpa using Real.sqrt_pos.2 ha) (fun x (v : ℝ) ↦ ?_),
    ← IsRiemannianManifold.out, edist_dist, Real.dist_eq,
    ENNReal.ofReal_mul (Real.sqrt_nonneg a)]
  · -- `ENNReal.ofReal √a` is by definition the coercion of `Real.toNNReal √a`.
    rfl
  · -- The tangent vector `v` is a real number, whose standard tangent norm is `|v|`.
    erw [scaledLineMetric_inner, hC, Real.sq_sqrt ha.le, norm_tangentSpace_vectorSpace]
    rw [Real.norm_eq_abs, sq_abs, sq]
    -- `NormedSpace.fromTangentSpace x v` is `v` itself, read in `ℝ`, by definition.
    rfl

/-- For the metric `a dx²`, the trajectory of `-grad x²` through `x₀` is at Riemannian distance
exactly `√a |x₀| exp (-2 t / a)` from the critical point `0` at time `t`. For `a = 4` this is
`2 |x₀| exp (-t / 2)`. -/
theorem riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (x₀ t : ℝ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℝ)
        (maximalIntegralCurve
          (-mgradient 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2))
          (toWithMetric _ x₀) t) (toWithMetric _ 0) =
      ENNReal.ofReal (√a * |x₀| * Real.exp (-(2 / a * t))) := by
  rw [maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric,
    riemannianEDist_toWithMetric_scaledLineMetric, sub_zero, abs_mul, Real.abs_exp, mul_assoc]

/-- **The rate `2 / a` is sharp.** For the metric `a dx²`, `x₀ ≠ 0` and `μ > 2 / a`, the distance
from the trajectory of `-grad x²` through `x₀` to the critical point `0` is not bounded by
`C exp (-μ t)` for large `t`, for any `C > 0`. So the rate of convergence depends on the metric:
it is `2` for the standard metric
(`TauCeti.not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq`) and `1 / 2`
for `4 dx²`. -/
theorem not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric
    {x₀ μ : ℝ} (hx₀ : x₀ ≠ 0) (hμ : 2 / a < μ) :
    ¬ ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist 𝓘(ℝ, ℝ)
          (maximalIntegralCurve
            (-mgradient 𝓘(ℝ, ℝ) (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2))
            (toWithMetric _ x₀) t) (toWithMetric _ 0) ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  rintro ⟨C, hC, h⟩
  refine not_exists_ofReal_mul_exp_le_mul_exp (mul_pos (Real.sqrt_pos.2 ha) (abs_pos.2 hx₀)) hμ
    ⟨C, hC, h.mono fun t ht ↦ ?_⟩
  rwa [← riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric]

end ScaledMetric

end TauCeti
