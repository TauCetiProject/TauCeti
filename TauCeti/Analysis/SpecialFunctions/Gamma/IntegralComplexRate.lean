/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

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
  rate, written with `z^{-s}` and with `exp(-s log z)`.
* `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi`,
  `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi`: convergence and holomorphy in the
  rate on the right half-plane.
* `Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi`,
  `Complex.integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi`,
  `Complex.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le`: integrability and
  compact-set majorants on `(0, ∞)` with logarithmic power factors.
* `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_left`,
  `Complex.analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi_prod`,
  `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_prod`: holomorphy in `s` and joint
  analyticity and holomorphy in `(s, z)` on `{0 < Re s} × {0 < Re z}`.

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

/-- The norm of the integrand `t^{s-1} e^{-wt}` for `t > 0`. -/
private theorem norm_cpow_mul_exp_neg_mul (s w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * exp (-(w * t))‖ = t ^ (s.re - 1) * Real.exp (-w.re * t) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  simp

/-- For `Re s > 0` and `Re w > 0`, `t ↦ t^{s-1} e^{-wt}` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(w * t))) (Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
    (by linarith) one_pos hw
  refine Integrable.mono' hb (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_cpow_mul_exp_neg_mul s w ht, Real.rpow_one]

/-- For `Re s > 0`, the Gamma integral `w ↦ ∫₀^∞ t^{s-1} e^{-wt} dt` is holomorphic in the rate
`w` on the right half-plane. -/
theorem differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi {s : ℂ} (hs : 0 < s.re) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t)))
      {w | 0 < w.re} := by
  intro w₀ hw₀
  have hw₀' : 0 < w₀.re := hw₀
  -- On the ball of radius `δ = Re w₀ / 2` about `w₀` we have `Re w > δ`, which gives the
  -- integrable bound `t^{Re s} e^{-δt}` for the `w`-derivative `−t · t^{s-1} e^{-wt}`.
  set δ := w₀.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hball : Metric.ball w₀ δ ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hδ0
  have hre : ∀ w ∈ Metric.ball w₀ δ, δ < w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - w₀)
    rw [sub_re] at h1
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hw)).1
    linarith
  have hbint : Integrable (fun t : ℝ => t ^ s.re * Real.exp (-δ * t))
      (volume.restrict (Ioi 0)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re) (b := δ)
      (by linarith) one_pos hδ0
    simp only [Real.rpow_one] at this
    exact this
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) => (t : ℂ) ^ (s - 1) * exp (-(w * t)))
    (F' := fun w (t : ℝ) => (t : ℂ) ^ (s - 1) * exp (-(w * t)) * -(t : ℂ))
    (bound := fun t : ℝ => t ^ s.re * Real.exp (-δ * t))
    hball (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_exp_neg_mul_Ioi hs hw₀')
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
  · exact h.2.differentiableAt.differentiableWithinAt
  · -- The bound: `‖t^{s-1} e^{-wt} · (−t)‖ = t^{Re s} e^{-(Re w) t} ≤ t^{Re s} e^{-δt}`.
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have ht' : 0 < t := ht
    rw [norm_mul, norm_cpow_mul_exp_neg_mul s w ht', norm_neg, norm_real,
      Real.norm_of_nonneg ht'.le, mul_right_comm, ← Real.rpow_add_one ht'.ne', sub_add_cancel]
    gcongr
    nlinarith [hre w hw]
  · filter_upwards with t w _
    have := ((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp.const_mul ((t : ℂ) ^ (s - 1))
    simpa [mul_assoc] using this

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

end Complex

end

public section

open MeasureTheory Set Filter
open scoped Topology

private theorem abs_log_pow_mul_rpow_le {s t : ℝ} (hs : -1 < s) (ht : 0 < t) {k : ℕ}
    (hk : 0 < k) :
    |Real.log t| ^ k * t ^ s ≤
      (2 : ℝ) ^ (k - 1) * (((s + 1) / (2 * k))⁻¹ ^ k * t ^ (s - (s + 1) / 2) + t ^ (s + k)) := by
  set ε : ℝ := (s + 1) / (2 * k) with hε_def
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hlow := Real.neg_rpow_div_le_log ht.le hε
  rw [neg_div] at hlow
  have hlog : |Real.log t| ≤ t ^ (-ε) / ε + t :=
    abs_le.mpr ⟨by linarith [Real.rpow_nonneg ht.le (-ε)],
      by linarith [Real.log_le_self ht.le, div_nonneg (Real.rpow_nonneg ht.le (-ε)) hε.le]⟩
  have hrpow : (t ^ (-ε) / ε) ^ k = ε⁻¹ ^ k * t ^ (-(s + 1) / 2) := by
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [div_eq_mul_inv, mul_pow, mul_comm _ (ε⁻¹ ^ k), ← Real.rpow_natCast (t ^ (-ε)) k,
      ← Real.rpow_mul ht.le, hε_def]
    congr 2; field_simp
  have ha : t ^ (-(s + 1) / 2) * t ^ s = t ^ (s - (s + 1) / 2) := by
    rw [← Real.rpow_add ht]; ring_nf
  have hb : t ^ k * t ^ s = t ^ (s + k) := by
    rw [← Real.rpow_natCast t k, ← Real.rpow_add ht, add_comm]
  calc |Real.log t| ^ k * t ^ s ≤ (t ^ (-ε) / ε + t) ^ k * t ^ s := by gcongr
    _ ≤ (2 : ℝ) ^ (k - 1) * ((t ^ (-ε) / ε) ^ k + t ^ k) * t ^ s := by
        gcongr; exact add_pow_le (by positivity) ht.le k
    _ = (2 : ℝ) ^ (k - 1) * (ε⁻¹ ^ k * t ^ (s - (s + 1) / 2) + t ^ (s + k)) := by
        rw [hrpow]; linear_combination (2 : ℝ) ^ (k - 1) * ε⁻¹ ^ k * ha + (2 : ℝ) ^ (k - 1) * hb

/-- For `s > -1`, `b > 0`, and any natural power `k`, `t ↦ |log t|^k t^s e^{-bt}` is integrable
on `(0, ∞)`. Bounding `|log t|` by `t^{-ε}/ε + t` with `ε = (s + 1) / (2k)` reduces both the
origin singularity and the tail at infinity to `integrableOn_rpow_mul_exp_neg_mul_rpow`. -/
theorem Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi {s b : ℝ} (hs : -1 < s)
    (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb
  set ε : ℝ := (s + 1) / (2 * k)
  have h1 : Integrable
      (fun t : ℝ => (2 : ℝ) ^ (k - 1) * ε⁻¹ ^ k * (t ^ (s - (s + 1) / 2) * Real.exp (-b * t)))
      (volume.restrict (Ioi 0)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hb).const_mul
        ((2 : ℝ) ^ (k - 1) * ε⁻¹ ^ k)
  have h2 : Integrable (fun t : ℝ => (2 : ℝ) ^ (k - 1) * (t ^ (s + k) * Real.exp (-b * t)))
      (volume.restrict (Ioi 0)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [(Nat.cast_pos (α := ℝ)).2 hk])
        one_pos hb).const_mul ((2 : ℝ) ^ (k - 1))
  refine (h1.add h2).mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
  linarith [mul_le_mul_of_nonneg_right (abs_log_pow_mul_rpow_le hs ht hk)
    (Real.exp_pos (-b * t)).le]

namespace Complex

private theorem norm_cpow_mul_log_pow_mul_exp_neg_mul (s w : ℂ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ s * (log t) ^ k * exp (-(w * t))‖ =
      |Real.log t| ^ k * t ^ s.re * Real.exp (-w.re * t) := by
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_pow, ← ofReal_log ht.le,
    norm_real, Real.norm_eq_abs, norm_exp]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, neg_mul]; ring

/-- For `Re s > -1`, `Re w > 0`, and `k : ℕ`, `t ↦ t^s (log t)^k e^{-wt}` is integrable on
`(0, ∞)`. -/
theorem integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : -1 < s.re)
    (hw : 0 < w.re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ s * (log t) ^ k * exp (-(w * t))) (Ioi 0) := by
  refine (Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi hs hw k).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_cpow_mul_log_pow_mul_exp_neg_mul s w k ht]

/-- On any compact subset `K` of `{p : ℂ × ℂ | -1 < p.1.re ∧ 0 < p.2.re}`, the weighted
Gamma-Laplace integrand `t^{p.1} (log t)^k e^{-p.2 t}` admits a single integrable real majorant
on `(0, ∞)`. -/
theorem exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hKs : ∀ p ∈ K, -1 < p.1.re) (hKw : ∀ p ∈ K, 0 < p.2.re) (k : ℕ) :
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

/-- The Gamma integral with a complex rate written in principal-logarithm form: for `Re s > 0` and
`Re z > 0`, `∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) exp(-s log z)`. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq_Gamma_mul_exp {s z : ℂ} (hs : 0 < s.re)
    (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(z * t)) = Gamma s * exp (-s * log z) := by
  have hzne : z ≠ 0 := fun h => by simp [h] at hz
  rw [integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hz, cpow_def_of_ne_zero hzne, mul_comm (log z)]

/-- For `Re w > 0`, the Gamma integral `s ↦ ∫₀^∞ t^{s-1} e^{-wt} dt` is holomorphic on the right
half-plane `{s | 0 < s.re}`. -/
theorem differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi_left {w : ℂ} (hw : 0 < w.re) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t)))
      {s | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set r : ℝ := s₀.re / 2 with hr_def
  have hr : 0 < r := half_pos hs₀'
  have hK : IsCompact ((fun s : ℂ => (s - 1, w)) '' Metric.closedBall s₀ r) :=
    (isCompact_closedBall s₀ r).image (by fun_prop)
  obtain ⟨g, hg, hbound⟩ := exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le hK
    (by
      rintro _ ⟨s, hs, rfl⟩
      have habs := (abs_re_le_norm (s - s₀)).trans (mem_closedBall_iff_norm.mp hs)
      rw [sub_re] at habs
      dsimp only; rw [sub_re, one_re]; linarith [hr_def, hs₀', (abs_le.mp habs).1])
    (by rintro _ ⟨_, _, rfl⟩; exact hw) 1
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s (t : ℝ) => (t : ℂ) ^ (s - 1) * exp (-(w * t)))
    (F' := fun s (t : ℝ) => (t : ℂ) ^ (s - 1) * log t * exp (-(w * t))) (bound := g)
    (Metric.closedBall_mem_nhds s₀ hr)
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_exp_neg_mul_Ioi hs₀' hw)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hg ?_).2.differentiableAt
    |>.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    simpa only [pow_one] using hbound (s - 1, w) ⟨s, hs, rfl⟩ t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have hd : HasDerivAt (fun s : ℂ => (t : ℂ) ^ (s - 1)) ((t : ℂ) ^ (s - 1) * log t) s := by
      simpa using (((hasDerivAt_id s).sub_const 1).const_cpow
        (Or.inl (ofReal_ne_zero.mpr (ne_of_gt ht))))
    simpa [mul_assoc] using hd.mul_const (exp (-(w * t)))

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
  have hF : DifferentiableOn ℂ (fun p : ℂ × ℂ => Gamma p.1 * p.2 ^ (-p.1)) U := fun p hp => by
    have hs0 : ∀ m : ℕ, p.1 ≠ -(m : ℂ) := fun m h => by
      have hre := congrArg re h; simp only [neg_re, natCast_re] at hre
      linarith [hp.1, Nat.cast_nonneg (α := ℝ) m]
    exact (((differentiableAt_Gamma p.1 hs0).comp p differentiableAt_fst).mul
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

end Complex

end
