/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.Morse.Pi

/-!
# Exponential convergence of gradient trajectories: two test cases

A negative gradient trajectory converging to a nondegenerate critical point converges to it
exponentially fast in the Riemannian distance
(`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`). This file
computes two explicit trajectories, for the standard flat metric, which test the hypothesis and
the rate of that theorem.

* **The nondegeneracy hypothesis cannot be dropped.** For `f(x) = x⁴` on `ℝ`, the trajectory of
  `-grad f` through `x₀` is `x₀ (1 + 8 x₀² t)^(-1/2)`
  (`TauCeti.maximalIntegralCurve_neg_mgradient_pow_four`). It converges to the critical point `0`
  (`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_pow_four`), which is degenerate
  (`TauCeti.not_isManifoldNondegenerateCriticalPoint_pow_four`), but only at a polynomial rate: for
  `x₀ ≠ 0` its distance to `0` admits no bound `C exp (-μ t)` with `μ > 0`
  (`TauCeti.not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_pow_four`).
* **The rate at a saddle is the Hessian eigenvalue.** For `f(x, y) = x² - y²` on the Euclidean
  plane, the origin is a nondegenerate critical point
  (`TauCeti.isManifoldNondegenerateCriticalPoint_sq_sub_sq`) and a saddle: `f` takes values of
  both signs arbitrarily close to it (`TauCeti.not_isLocalMin_sq_sub_sq`,
  `TauCeti.not_isLocalMax_sq_sub_sq`), so `f - f 0` is not of one sign near the limit. The
  trajectory through `(a, 0)` is `(a exp (-2 t), 0)`
  (`TauCeti.maximalIntegralCurve_neg_mgradient_sq_sub_sq`), at distance exactly `|a| exp (-2 t)`
  from the origin (`TauCeti.riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_sub_sq`). So
  the exponential bound holds with the rate `2`, the positive eigenvalue of the Hessian, and for
  `a ≠ 0` with no larger rate
  (`TauCeti.not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_sub_sq`).

The trajectories are identified with the maximal integral curves of `-grad f` by uniqueness of
integral curves (`TauCeti.Manifold.eqOn_maximalIntegralCurve_neg_mgradient_of_hasDerivAt`), and on
a flat space the Riemannian distance is the norm distance (`IsRiemannianManifold`).

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, second edition, Academic Press, 2004, Chapter 9 (gradient systems).
-/

public section

open Bundle Filter Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

/-! ### A degenerate minimum: `x⁴` on `ℝ` -/

section QuarticWell

/-- The gradient of `x ↦ x⁴` on `ℝ` is `x ↦ 4 x³`. -/
private theorem gradient_pow_four (x : ℝ) : gradient (fun y : ℝ ↦ y ^ 4) x = 4 * x ^ 3 := by
  rw [gradient_eq_deriv']
  simp

/-- The curve `t ↦ x₀ (1 + 8 x₀² t)^(-1/2)` solves `x' = -4 x³` where `1 + 8 x₀² t > 0`. -/
private theorem hasDerivAt_quarticTrajectory {x₀ t : ℝ} (ht : 0 < 1 + 8 * x₀ ^ 2 * t) :
    HasDerivAt (fun s ↦ x₀ * (1 + 8 * x₀ ^ 2 * s) ^ (-(1 / 2 : ℝ)))
      (-gradient (fun y : ℝ ↦ y ^ 4) (x₀ * (1 + 8 * x₀ ^ 2 * t) ^ (-(1 / 2 : ℝ)))) t := by
  have h1 : HasDerivAt (fun s ↦ 1 + 8 * x₀ ^ 2 * s) (8 * x₀ ^ 2) t := by
    simpa using ((hasDerivAt_id t).const_mul (8 * x₀ ^ 2)).const_add 1
  have key : ((1 + 8 * x₀ ^ 2 * t) ^ (-(1 / 2 : ℝ))) ^ 3 =
      (1 + 8 * x₀ ^ 2 * t) ^ (-(1 / 2 : ℝ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  convert (h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl ht.ne')).const_mul x₀ using 1
  rw [gradient_pow_four, mul_pow, key]
  ring

/-- **The trajectory of `-grad x⁴` through `x₀`** is `t ↦ x₀ (1 + 8 x₀² t)^(-1/2)`, wherever
`1 + 8 x₀² t > 0`. -/
theorem maximalIntegralCurve_neg_mgradient_pow_four {x₀ t : ℝ} (ht : 0 < 1 + 8 * x₀ ^ 2 * t) :
    maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 4)) x₀ t =
      x₀ * (1 + 8 * x₀ ^ 2 * t) ^ (-(1 / 2 : ℝ)) := by
  -- An open interval around `0` and `t` on which `1 + 8 x₀² s` stays positive.
  set m := min t 0
  set q := 1 + 8 * x₀ ^ 2 * m
  have hq : 0 < q := by
    rcases min_choice t 0 with h | h <;> simp only [q, m, h] <;> linarith
  have hx : 0 ≤ 8 * x₀ ^ 2 := by positivity
  set a := m - q / (8 * x₀ ^ 2 + 1)
  have hpos : ∀ s, a < s → 0 < 1 + 8 * x₀ ^ 2 * s := by
    intro s hs
    have hqa : 1 + 8 * x₀ ^ 2 * a = q / (8 * x₀ ^ 2 + 1) := by
      simp only [a, q]
      field_simp
      ring
    have : 0 < q / (8 * x₀ ^ 2 + 1) := by positivity
    nlinarith
  have ha0 : a < m := sub_lt_self _ (by positivity)
  have hIoo : t ∈ Ioo a (max t 0 + 1) :=
    ⟨ha0.trans_le (min_le_left _ _), by linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ) ∈ Ioo a (max t 0 + 1) :=
    ⟨ha0.trans_le (min_le_right _ _), by linarith [le_max_right t 0]⟩
  simpa using eqOn_maximalIntegralCurve_neg_mgradient_of_hasDerivAt (f := fun y : ℝ ↦ y ^ 4)
    (contDiff_id.pow 4) h0 (fun s hs ↦ hasDerivAt_quarticTrajectory (hpos s hs.1)) hIoo

/-- The trajectory of `-grad x⁴` through any `x₀` converges to the critical point `0`. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_pow_four (x₀ : ℝ) :
    Tendsto (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 4)) x₀) atTop (𝓝 0) := by
  have heq : (fun t ↦ x₀ * (1 + 8 * x₀ ^ 2 * t) ^ (-(1 / 2 : ℝ))) =ᶠ[atTop]
      maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 4)) x₀ := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (maximalIntegralCurve_neg_mgradient_pow_four
      (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (by positivity) ht))).symm
  refine Tendsto.congr' heq ?_
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · simp
  · have hlin : Tendsto (fun t : ℝ ↦ 1 + 8 * x₀ ^ 2 * t) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop (by positivity))
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hlin).const_mul x₀

/-- The critical point `0` of `x ↦ x⁴` is degenerate: its second derivative vanishes. -/
theorem not_isManifoldNondegenerateCriticalPoint_pow_four :
    ¬ IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 4) 0 := by
  rw [isManifoldNondegenerateCriticalPoint_iff]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, id_eq]
  rw [isNondegenerateCriticalPoint_real_iff (by fun_prop)]
  simp

/-- **Polynomial, not exponential, convergence to a degenerate minimum.** For `x₀ ≠ 0`, the
trajectory of `-grad x⁴` through `x₀` converges to `0`, but its distance to `0` is bounded by
`C exp (-μ t)` for large `t` for no `μ > 0` and `C > 0`. So the nondegeneracy hypothesis of
`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient` cannot be
dropped. -/
theorem not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_pow_four
    {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    ¬ ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist 𝓘(ℝ, ℝ)
          (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 4)) x₀ t) 0 ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  rintro ⟨μ, hμ, C, hC, h⟩
  have hx : 0 < |x₀| := abs_pos.2 hx₀
  set K := C * (1 + 8 * x₀ ^ 2) / |x₀|
  -- `exp (μ t) / t` is eventually larger than `K`, while the bound would keep it below `K`.
  have hgrow := (tendsto_exp_mul_div_rpow_atTop 1 μ hμ).eventually_gt_atTop K
  obtain ⟨t, ht, hgrow, ht1⟩ := (h.and (hgrow.and (eventually_ge_atTop 1))).exists
  have hy1 : 1 ≤ 1 + 8 * x₀ ^ 2 * t := by nlinarith [sq_nonneg x₀]
  have hy : 0 < 1 + 8 * x₀ ^ 2 * t := one_pos.trans_le hy1
  rw [maximalIntegralCurve_neg_mgradient_pow_four hy, ← IsRiemannianManifold.out, edist_dist,
    dist_zero_right, ENNReal.ofReal_le_ofReal_iff (by positivity), Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hy _)] at ht
  -- Since `1 + 8 x₀² t ≥ 1`, its inverse is at most its inverse square root.
  have hrp : (1 + 8 * x₀ ^ 2 * t)⁻¹ ≤ (1 + 8 * x₀ ^ 2 * t) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have h2 : |x₀| * (1 + 8 * x₀ ^ 2 * t)⁻¹ ≤ C * Real.exp (-(μ * t)) :=
    (mul_le_mul_of_nonneg_left hrp hx.le).trans ht
  rw [Real.exp_neg, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_div_iff₀ hy (Real.exp_pos _)] at h2
  rw [Real.rpow_one, lt_div_iff₀ (by linarith)] at hgrow
  have hK : |x₀| * K = C * (1 + 8 * x₀ ^ 2) := by
    simp only [K]
    field_simp
  nlinarith [mul_lt_mul_of_pos_left hgrow hx, sq_nonneg x₀]

end QuarticWell

/-! ### A saddle: `x² - y²` on the Euclidean plane -/

section Saddle

/-- The gradient of `x² - y²` at `p` is `(2 p₀, -2 p₁)`. -/
private theorem hasGradientAt_sq_sub_sq (p : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2)
      (EuclideanSpace.single 0 (2 * p 0) - EuclideanSpace.single 1 (2 * p 1)) p := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 := ((EuclideanSpace.proj (0 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt (x := p)).pow 2
  have h1 := ((EuclideanSpace.proj (1 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt (x := p)).pow 2
  refine (h0.sub h1).congr_fderiv ?_
  ext v
  simp [EuclideanSpace.inner_single_left]

/-- `x² - y²` is smooth. -/
private theorem contDiff_sq_sub_sq :
    ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2) :=
  ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.pow 2).sub
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.pow 2)

/-- The curve `t ↦ (a exp (-2 t), 0)` solves `γ' = -∇ (x² - y²) (γ)`. -/
private theorem hasDerivAt_sqSubSqTrajectory (a t : ℝ) :
    HasDerivAt (fun s ↦ EuclideanSpace.single (0 : Fin 2) (a * Real.exp (-(2 * s))))
      (-gradient (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2)
        (EuclideanSpace.single 0 (a * Real.exp (-(2 * t))))) t := by
  rw [(hasGradientAt_sq_sub_sq _).gradient]
  have h : HasDerivAt (fun s ↦ a * Real.exp (-(2 * s))) (a * (Real.exp (-(2 * t)) * -2)) t := by
    simpa using (((hasDerivAt_id t).const_mul 2).neg.exp).const_mul a
  convert h.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) using 1
  · ext s i
    fin_cases i <;> simp
  · ext i
    fin_cases i
    · simp
      ring
    · simp

/-- **The stable trajectory of the saddle `x² - y²`.** The trajectory of `-grad (x² - y²)` through
`(a, 0)` is `t ↦ (a exp (-2 t), 0)`, defined for all time. -/
theorem maximalIntegralCurve_neg_mgradient_sq_sub_sq (a t : ℝ) :
    maximalIntegralCurve (-mgradient 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2)) (EuclideanSpace.single 0 a) t =
      EuclideanSpace.single 0 (a * Real.exp (-(2 * t))) := by
  have hb : 0 < |t| + 1 := by positivity
  simpa using eqOn_maximalIntegralCurve_neg_mgradient_of_hasDerivAt contDiff_sq_sub_sq
    (a := -(|t| + 1)) (b := |t| + 1) ⟨neg_lt_zero.2 hb, hb⟩
    (fun s _ ↦ hasDerivAt_sqSubSqTrajectory a s)
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- The trajectory of `-grad (x² - y²)` through `(a, 0)` is at Riemannian distance exactly
`|a| exp (-2 t)` from the saddle point `0` at time `t`. -/
theorem riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_sub_sq (a t : ℝ) :
    Manifold.riemannianEDist 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2)) (EuclideanSpace.single 0 a) t)
        0 =
      ENNReal.ofReal (|a| * Real.exp (-(2 * t))) := by
  rw [maximalIntegralCurve_neg_mgradient_sq_sub_sq, ← IsRiemannianManifold.out, edist_dist,
    dist_zero_right, PiLp.norm_single, Real.norm_eq_abs, abs_mul, Real.abs_exp]

/-- **The rate `2` at the saddle is sharp.** For `a ≠ 0` and `μ > 2`, the distance from the
trajectory of `-grad (x² - y²)` through `(a, 0)` to the saddle point is not bounded by
`C exp (-μ t)` for large `t`, for any `C > 0`. -/
theorem not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_sub_sq
    {a μ : ℝ} (ha : a ≠ 0) (hμ : 2 < μ) :
    ¬ ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (maximalIntegralCurve (-mgradient 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2)) (EuclideanSpace.single 0 a) t)
          0 ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  rintro ⟨C, hC, h⟩
  have hgrow : Tendsto (fun t : ℝ ↦ Real.exp ((μ - 2) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.2 hμ))
  obtain ⟨t, ht, hbig⟩ := (h.and (hgrow.eventually_gt_atTop (C / |a|))).exists
  rw [riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_sub_sq,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at ht
  -- Multiplying the bound by `exp (μ t)` gives `|a| exp ((μ - 2) t) ≤ C`.
  have hprod : Real.exp (-(2 * t)) * Real.exp (μ * t) = Real.exp ((μ - 2) * t) := by
    rw [← Real.exp_add]
    ring_nf
  have hone : Real.exp (-(μ * t)) * Real.exp (μ * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hle := mul_le_mul_of_nonneg_right ht (Real.exp_pos (μ * t)).le
  rw [mul_assoc, hprod, mul_assoc, hone, mul_one] at hle
  rw [div_lt_iff₀ (abs_pos.2 ha)] at hbig
  linarith

/-- The saddle point `0` of `x² - y²` is not a local minimum: `f` is negative along the second
axis. -/
theorem not_isLocalMin_sq_sub_sq :
    ¬ IsLocalMin (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2) 0 := by
  intro h
  have hcont : Continuous fun s : ℝ ↦ s • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) :=
    continuous_id.smul continuous_const
  have hc : Tendsto (fun s : ℝ ↦ s • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (𝓝[≠] 0)
      (𝓝 0) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs, hne⟩ := ((hc.eventually h).and self_mem_nhdsWithin).exists
  exact hne (by simpa using hs)

/-- The saddle point `0` of `x² - y²` is not a local maximum: `f` is positive along the first
axis. -/
theorem not_isLocalMax_sq_sub_sq :
    ¬ IsLocalMax (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2) 0 := by
  intro h
  have hcont : Continuous fun s : ℝ ↦ s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :=
    continuous_id.smul continuous_const
  have hc : Tendsto (fun s : ℝ ↦ s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (𝓝[≠] 0)
      (𝓝 0) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs, hne⟩ := ((hc.eventually h).and self_mem_nhdsWithin).exists
  exact hne (by simpa using hs)

/-- **The saddle point is nondegenerate.** The origin is a nondegenerate critical point of
`x² - y²`, so the exponential convergence theorem applies to the trajectories converging to it. -/
theorem isManifoldNondegenerateCriticalPoint_sq_sub_sq :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 ^ 2 - z 1 ^ 2) 0 := by
  rw [isManifoldNondegenerateCriticalPoint_iff]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, id_eq]
  -- In the coordinates of `ℝ²`, the function is the separated sum of `s²` and `-s²`.
  let φ : Fin 2 → ℝ → ℝ := ![fun s ↦ s ^ 2, fun s ↦ -s ^ 2]
  have hφ : ∀ i, ContDiffAt ℝ 2 (φ i) ((0 : Fin 2 → ℝ) i) := by
    intro i
    fin_cases i
    · simpa [φ] using (contDiff_id.pow 2 : ContDiff ℝ 2 fun s : ℝ ↦ s ^ 2).contDiffAt
    · simpa [φ] using ((contDiff_id.pow 2).neg : ContDiff ℝ 2 fun s : ℝ ↦ -s ^ 2).contDiffAt
  have hd : deriv (fun s : ℝ ↦ s ^ 2) = fun s ↦ 2 * s := by
    ext s
    simp
  have hsum : IsNondegenerateCriticalPoint (fun y : Fin 2 → ℝ ↦ ∑ i, φ i (y i))
      (EuclideanSpace.equiv (Fin 2) ℝ 0) := by
    refine (isNondegenerateCriticalPoint_sum_comp_eval_iff (y := 0) hφ).2 fun i ↦ ?_
    fin_cases i
    · simp [φ, hd]
    · simp [φ, deriv.fun_neg']
  have hinv : (fderiv ℝ (EuclideanSpace.equiv (Fin 2) ℝ) 0).IsInvertible := by
    rw [ContinuousLinearEquiv.fderiv]
    exact ⟨_, rfl⟩
  convert hsum.comp (EuclideanSpace.equiv (Fin 2) ℝ).contDiff.contDiffAt hinv using 1
  ext z
  simp [φ, Fin.sum_univ_two, sub_eq_add_neg]

end Saddle

end TauCeti
