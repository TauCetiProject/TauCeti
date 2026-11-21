/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The Gamma integral with a complex rate

For `Re s > 0` and `Re z > 0`,
`∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s} = Γ(s) exp(-s log z)` with the principal logarithm and power.

Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` is the case of a positive real rate. Both
sides are holomorphic in `z` on the right half-plane: the integral by differentiation under the
integral sign, the right side because the half-plane lies in the slit plane. They agree on the
positive reals, so they agree on the half-plane by the identity theorem. On compact subsets of
`{p : ℂ × ℂ | -1 < p.1.re ∧ 0 < p.2.re}`, `t^{p.1} (log t)^k e^{-p.2 t}` admits a single
integrable real majorant on `(0, ∞)`, giving holomorphy in `s` and joint analyticity in `(s, z)`.

## Main results

* `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`,
  `Complex.integral_cpow_mul_exp_neg_mul_Ioi_eq_Gamma_mul_exp`: the Gamma integral with complex
  rate, in principal-power and principal-logarithm forms.
* `Complex.integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi`,
  `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi`,
  `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi`: convergence and holomorphy in the
  rate on the right half-plane.
* `IsCompact.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le`: compact-set
  majorants on `(0, ∞)` with logarithmic power factors.
* `Complex.analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi_prod`,
  `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_prod`,
  `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_left`: joint analyticity and
  holomorphy in `(s, z)` on `{0 < Re s} × {0 < Re z}`, and holomorphy in `s`.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  24 (2012), 49–84, §2, (2.2)–(2.4), p. 53.
* The complex-rate evaluation proof is adapted from the lean-DLMF project
  (<https://github.com/bjbraams/lean-DLMF>), file
  `DLMFMathlib/Analysis/Asymptotics/WatsonSector.lean`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Complex

/-- For `Re s > -1`, `Re w > 0`, and `k : ℕ`, `t ↦ t^s (log t)^k e^{-wt}` is integrable on
`(0, ∞)`. -/
theorem integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : -1 < s.re)
    (hw : 0 < w.re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ s * (log t) ^ k * exp (-(w * t))) (Ioi 0) := by
  refine (Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi hs hw k).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_cpow_mul_log_pow_mul_exp_neg_mul s w k ht]

/-- For `Re s > 0` and `Re w > 0`, `t ↦ t^{s-1} e^{-wt}` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(w * t))) (Ioi 0) := by
  have hs' : -1 < (s - 1).re := by simp; linarith
  simpa using integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi hs' hw 0

/-- For `Re s > 0`, the Gamma integral `w ↦ ∫₀^∞ t^{s-1} e^{-wt} dt` is holomorphic in the rate
`w` on the right half-plane. -/
theorem differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi {s : ℂ} (hs : 0 < s.re) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t)))
      {w | 0 < w.re} :=
  TauCeti.differentiableOn_of_hasLaplace_re_gt (f := fun t : ℝ ↦ (t : ℂ) ^ (s - 1)) (a := 0)
    fun w hw ↦ TauCeti.HasLaplace.intro
      (by simpa only [IntegrableOn, smul_eq_mul, mul_comm (exp _), neg_mul] using
        integrableOn_cpow_mul_exp_neg_mul_Ioi hs hw)
      (by simp only [smul_eq_mul, mul_comm (exp _), neg_mul])

/-- The Gamma integral with a complex rate: for `Re s > 0` and `Re z > 0`,
`∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s}`. Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`
is the case of a positive real rate. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(z * t)) = Gamma s * z ^ (-s) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  let I : ℂ → ℂ := fun w => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t))
  -- Both sides are analytic on the right half-plane `U`.
  have hanI : AnalyticOnNhd ℂ I U :=
    (differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi hs).analyticOnNhd hUo
  have hanR : AnalyticOnNhd ℂ (fun w => Gamma s * w ^ (-s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hslit : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hw)
    exact ((differentiableAt_id.cpow (differentiableAt_const _) hslit).const_mul
      _).differentiableWithinAt
  -- They agree on the positive reals, by Mathlib's real-rate formula.
  have hreal (r : ℝ) (hr : 0 < r) : I r = Gamma s * (r : ℂ) ^ (-s) := by
    have harg : arg (r : ℂ) ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne
    simp only [I]
    rw [integral_cpow_mul_exp_neg_mul_Ioi hs hr, one_div, inv_cpow _ _ harg, ← cpow_neg,
      mul_comm]
  -- So they agree frequently near `1`, and hence on `U` by the identity theorem.
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), I w = Gamma s * w ^ (-s) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hreal r hr
  exact hanI.eqOn_of_preconnected_of_frequently_eq hanR (convex_halfSpace_re_gt 0).isPreconnected
    (by simp [hU]) hfreq hz

/-- The Gamma integral with a complex rate in principal-logarithm form: for `Re s > 0` and
`Re z > 0`, `∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) exp (-s * log z)`. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq_Gamma_mul_exp {s z : ℂ} (hs : 0 < s.re)
    (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(z * t)) = Gamma s * exp (-s * log z) := by
  have hz0 : z ≠ 0 := by intro h; rw [h, zero_re] at hz; exact lt_irrefl 0 hz
  rw [integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hz, cpow_def_of_ne_zero hz0, mul_comm (log z)]

/-- On any compact subset `K` of `{p : ℂ × ℂ | -1 < p.1.re ∧ 0 < p.2.re}`, the weighted
Gamma-Laplace integrand `t^{p.1} (log t)^k e^{-p.2 t}` admits a single integrable real majorant
on `(0, ∞)`. -/
theorem _root_.IsCompact.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (hKs : ∀ p ∈ K, -1 < p.1.re)
    (hKw : ∀ p ∈ K, 0 < p.2.re) (k : ℕ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ p ∈ K, ∀ t > (0 : ℝ),
        ‖(t : ℂ) ^ p.1 * (log t) ^ k * exp (-(p.2 * t))‖ ≤ g t := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, integrableOn_zero, by simp⟩
  obtain ⟨p₁, hp₁, hmin_s⟩ := hK.exists_isMinOn hne (continuous_re.comp continuous_fst).continuousOn
  obtain ⟨p₂, hp₂, hmax_s⟩ := hK.exists_isMaxOn hne (continuous_re.comp continuous_fst).continuousOn
  obtain ⟨q, hq, hmin_w⟩ := hK.exists_isMinOn hne (continuous_re.comp continuous_snd).continuousOn
  refine ⟨fun t => |Real.log t| ^ k * t ^ p₁.1.re * Real.exp (-q.2.re * t) +
      |Real.log t| ^ k * t ^ p₂.1.re * Real.exp (-q.2.re * t),
    (Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi (hKs p₁ hp₁) (hKw q hq) k).add
      (Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi (hKs p₂ hp₂) (hKw q hq) k),
    fun p hp t ht => ?_⟩
  rw [norm_cpow_mul_log_pow_mul_exp_neg_mul p.1 p.2 k ht]
  have hexp : Real.exp (-p.2.re * t) ≤ Real.exp (-q.2.re * t) :=
    Real.exp_le_exp.mpr (by have : q.2.re ≤ p.2.re := hmin_w hp; nlinarith)
  rcases le_or_gt t 1 with ht1 | ht1
  · have hrp : t ^ p.1.re ≤ t ^ p₁.1.re := Real.rpow_le_rpow_of_exponent_ge ht ht1 (hmin_s hp)
    exact le_add_of_le_of_nonneg (by gcongr) (by positivity)
  · have hrp : t ^ p.1.re ≤ t ^ p₂.1.re := Real.rpow_le_rpow_of_exponent_le ht1.le (hmax_s hp)
    exact le_add_of_nonneg_of_le (by positivity) (by gcongr)

/-- The complex-rate Gamma integral `(s, z) ↦ ∫₀^∞ t^{s-1} e^{-zt} dt` is jointly analytic on
`{p : ℂ × ℂ | 0 < p.1.re ∧ 0 < p.2.re}`. -/
theorem analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi_prod :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (p.1 - 1) * exp (-(p.2 * t)))
      {p : ℂ × ℂ | 0 < p.1.re ∧ 0 < p.2.re} := by
  set U : Set (ℂ × ℂ) := {p | 0 < p.1.re ∧ 0 < p.2.re}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_re.comp continuous_fst)).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd))
  have hF : DifferentiableOn ℂ (fun p : ℂ × ℂ => Gamma p.1 * p.2 ^ (-p.1)) U := fun p hp =>
    (((hasDerivAt_Gamma_of_re_pos hp.1).differentiableAt.comp p differentiableAt_fst).mul
      (differentiableAt_snd.cpow differentiableAt_fst.neg
        (mem_slitPlane_iff.mpr (Or.inl hp.2)))).differentiableWithinAt
  exact (DifferentiableOn.analyticOnNhd_of_finiteDimensional hF hUo).congr hUo fun p hp =>
    (integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hp.1 hp.2).symm

/-- The complex-rate Gamma integral `(s, z) ↦ ∫₀^∞ t^{s-1} e^{-zt} dt` is jointly complex
differentiable on `{p : ℂ × ℂ | 0 < p.1.re ∧ 0 < p.2.re}`. -/
theorem differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_prod :
    DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (p.1 - 1) * exp (-(p.2 * t)))
      {p : ℂ × ℂ | 0 < p.1.re ∧ 0 < p.2.re} :=
  analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi_prod.differentiableOn

/-- For `Re w > 0`, the Gamma integral `s ↦ ∫₀^∞ t^{s-1} e^{-wt} dt` is holomorphic on the right
half-plane `{s | 0 < s.re}`. -/
theorem differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_left {w : ℂ} (hw : 0 < w.re) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t)))
      {s | 0 < s.re} :=
  differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_prod.comp
    (differentiableOn_id.prodMk (differentiableOn_const w)) fun _ hs => ⟨hs, hw⟩

end Complex

end
