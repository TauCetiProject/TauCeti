/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Trajectory
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Geometry.Manifold.Morse.Examples.ExponentialConvergence

/-!
# Gradient trajectories of the quadratic well

This file computes the negative gradient flow of `f(x) = x²` on `ℝ`, for the standard metric, and
uses it to test the convergence and decay theorems for gradient trajectories of Morse functions
(`TauCeti.IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient` and
`TauCeti.IsMorse.exists_edist_le_exp_of_tendsto_neg_mgradient`).

* **The trajectories.** The function `x²` is a Morse function (`TauCeti.isMorse_sq_real`) whose
  only critical point is `0` (`TauCeti.criticalPoints_sq_real`). The trajectory of `-grad f`
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

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, second edition, Academic Press, 2004, Chapter 9 (gradient systems).
-/

public section

open Filter MeasureTheory Set Topology TauCeti.Manifold
open scoped Bundle ContDiff ENNReal Manifold

namespace TauCeti

/-- For the standard metric on `ℝ`, the negative gradient of `x ↦ x²` at `x` is `-2 x`. -/
private theorem neg_mgradient_sq_real_apply (x : ℝ) :
    (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x = (-(2 * x) : ℝ) := by
  rw [Pi.neg_apply, mgradient_eq_gradient_of_eq rfl, gradient_eq_deriv']
  simp only [differentiableAt_fun_id, deriv_fun_pow, deriv_id'', Nat.cast_ofNat, mul_one,
    Nat.add_one_sub_one, pow_one]
  -- Both sides are the real number `-2 x`, read in `ℝ` and in its tangent space.
  rfl

/-- The curve `t ↦ x₀ exp (-2 t)` solves `x' = -2 x`. -/
private theorem hasDerivAt_quadraticTrajectory (x₀ t : ℝ) :
    HasDerivAt (fun s ↦ x₀ * Real.exp (-(2 * s))) (-(2 * (x₀ * Real.exp (-(2 * t))))) t := by
  have h : HasDerivAt (fun s : ℝ ↦ -(2 * s)) (-2) t := by
    simpa using ((hasDerivAt_id t).const_mul 2).fun_neg
  convert h.exp.const_mul x₀ using 1
  ring

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

/-! ### The trajectories -/

/-- **The trajectories of the quadratic well.** For the standard metric, the trajectory of
`-grad x²` through `x₀` is `t ↦ x₀ exp (-2 t)`, defined for all time. -/
theorem maximalIntegralCurve_neg_mgradient_sq (x₀ t : ℝ) :
    maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t =
      x₀ * Real.exp (-(2 * t)) := by
  have hb : 0 < |t| + 1 := by positivity
  simpa using eqOn_maximalIntegralCurve_neg_mgradient_of_hasDerivAt
    (f := fun y : ℝ ↦ y ^ 2) (by fun_prop) (a := -(|t| + 1)) (b := |t| + 1) ⟨neg_lt_zero.2 hb, hb⟩
    (fun s _ ↦ (hasDerivAt_quadraticTrajectory x₀ s).congr_deriv (by simp [gradient_eq_deriv']))
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
  rw [maximalIntegralCurve_neg_mgradient_sq, mul_pow, ← Real.exp_nat_mul]
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
      (hasDerivAt_quadraticTrajectory x₀ u).hasFDerivAt.fderiv, ← ofReal_norm]
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
  refine ((hasDerivAt_quadraticTrajectory x₀ t).hasDerivWithinAt.congr_of_mem heq
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

end TauCeti
