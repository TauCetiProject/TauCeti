/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Decay
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower

/-!
# The Gamma integral with a complex rate

For `Re s > 0` and `Re z > 0`,
`∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s} = Γ(s) exp(-s log z)` with the principal logarithm and power.

Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` is the case of a positive real rate. Both
sides are holomorphic in `z` on the right half-plane: the integral by differentiation under the
integral sign, the right side because the half-plane lies in the slit plane. They agree on the
positive reals, so they agree on the half-plane by the identity theorem. Joint analyticity of
`(s, z) ↦ ∫₀^∞ t^{s-1} e^{-zt} dt` on `{0 < Re s} × {0 < Re z}` follows directly from this
`Γ(s) z^{-s}` closed form. As a standalone integrability tool, on compact subsets of
`{p : ℂ × ℂ | -1 < p.1.re ∧ 0 < p.2.re}` the weighted integrand `t^{p.1} (log t)^k e^{-p.2 t}`
admits a single integrable real majorant on `(0, ∞)`.

On a half-line `(δ, ∞)` with `δ > 0` the integrand `t^γ e^{-zt}` is integrable for every `γ`, and
integration by parts lowers the exponent. Splitting the Gamma integral at `δ` and integrating the
part over `(δ, ∞)` by parts `n > Re s` times gives an expression that stays continuous as the rate
reaches the imaginary axis. At the rate `-ix`, `x > 0`, its value is `e^{iπs/2} Γ(s) x^{-s}`: this
is the Fourier integral of `t^{s-1}`, regularised at `∞`.

## Main results

* `Complex.norm_cpow_mul_exp_neg_mul`: norm identity for `t^{s-1} e^{-wt}` on `t > 0`.
* `Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi`,
  `Complex.norm_cpow_mul_log_pow_mul_exp_neg_mul`,
  `Complex.integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi`,
  `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi`,
  `Complex.summable_integral_norm_mul_cpow_mul_exp_neg_mul_Ioi`,
  `IsCompact.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le`:
  `(0, ∞)` integrability, weighted series-norm summability, and compact real majorant for
  `t^s (log t)^k e^{-wt}`-type integrands.
* `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`: the Gamma integral with complex rate.
* `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi`: holomorphy in the rate on the
  right half-plane.
* `Complex.analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi_prod`: joint analyticity in `(s, z)` on
  `{0 < Re s} × {0 < Re z}`.
* `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi_of_pos`,
  `Complex.integral_cpow_mul_exp_neg_mul_Ioi_eq_add_integral`,
  `Complex.integral_cpow_mul_exp_neg_mul_Ioi_eq_sum_add_integral`: integrability on `(δ, ∞)`
  for `δ > 0` and one or `n` integrations by parts.
* `Complex.norm_cpow_mul_exp_neg_mul_le`: the bound `‖t^γ e^{-wt}‖ ≤ t^{Re γ}` for `Re w ≥ 0`.
* `Complex.integrableOn_cpow_mul_exp_mul_I_Ioi`: on the imaginary axis, `t^γ e^{ixt}` is
  integrable on `(δ, ∞)` for `Re γ < -1`.
* `Complex.integral_cpow_mul_exp_mul_I_add_sum_eq`: the Fourier integral of `t^{s-1}`,
  regularised by integration by parts, is `e^{iπs/2} Γ(s) x^{-s}`.
* `TauCeti.integral_norm_cpow_mul_exp_neg_mul_Ioi`: the integral of the norm of the integrand is
  `(1 / Re w)^{Re s} Γ(Re s)`.

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

/-- For `s > -1`, `b > 0`, and any natural power `k`, `t ↦ |log t|^k t^s e^{-bt}` is integrable
on `(0, ∞)`. -/
theorem Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi {s b : ℝ} (hs : -1 < s)
    (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t))
      volume := (Measurable.aestronglyMeasurable (by fun_prop))
  have hIoo :
      IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioo 0 1) := by
    refine (TauCeti.integrableOn_Ioo_rpow_mul_neg_log_rpow hs
      (by linarith [Nat.cast_nonneg (α := ℝ) k] : (-1 : ℝ) < k)).mono' hm.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have hlog : Real.log t < 0 := Real.log_neg ht.1 ht.2
    have hlog_nn : 0 ≤ -Real.log t := neg_nonneg.mpr hlog.le
    have hexp : Real.exp (-b * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Real.norm_of_nonneg (by positivity), abs_of_neg hlog, ← Real.rpow_natCast (-Real.log t) k]
    calc (-Real.log t) ^ (k : ℝ) * t ^ s * Real.exp (-b * t)
        ≤ (-Real.log t) ^ (k : ℝ) * t ^ s * 1 := by gcongr
      _ = t ^ s * (-Real.log t) ^ (k : ℝ) := by ring
  have hIoc :
      IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioc 0 1) :=
    hIoo.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hIoi :
      IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioi 1) := by
    have hsk : -1 < s + k := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hdom : IntegrableOn (fun t : ℝ => t ^ (s + k) * Real.exp (-b * t ^ (1 : ℝ))) (Ioi 1) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow hsk one_pos hb).mono_set (Ioi_subset_Ioi zero_le_one)
    refine hdom.mono' hm.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlog_le : |Real.log t| ^ k ≤ t ^ k := by
      rw [abs_of_nonneg hlog_nn]
      exact pow_le_pow_left₀ hlog_nn (Real.log_le_self ht0.le) k
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_one]
    calc |Real.log t| ^ k * t ^ s * Real.exp (-b * t)
        ≤ t ^ k * t ^ s * Real.exp (-b * t) := by gcongr
      _ = t ^ (s + k) * Real.exp (-b * t) := by
          rw [← Real.rpow_natCast t k, ← Real.rpow_add ht0, add_comm (k : ℝ) s]
  exact (hIoc.union hIoi).mono_set fun t ht => by
    rcases le_or_gt t 1 with ht1 | ht1
    · exact Or.inl ⟨ht, ht1⟩
    · exact Or.inr ht1

namespace Complex

/-- The norm of the integrand `t^{s-1} e^{-wt}` for `t > 0`. -/
theorem norm_cpow_mul_exp_neg_mul (s w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * exp (-(w * t))‖ = t ^ (s.re - 1) * Real.exp (-w.re * t) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  simp

/-- The norm of `(t : ℂ) ^ s * (log t) ^ k * exp (-(w * t))` for `t > 0`. -/
theorem norm_cpow_mul_log_pow_mul_exp_neg_mul (s w : ℂ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ s * (log t) ^ k * exp (-(w * t))‖ =
      |Real.log t| ^ k * t ^ s.re * Real.exp (-w.re * t) := by
  rw [norm_mul, norm_mul, norm_pow, norm_cpow_eq_rpow_re_of_pos ht, ← ofReal_log ht.le,
    norm_real, Real.norm_eq_abs, norm_exp_neg_mul_ofReal, neg_mul]
  ring

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

/-- If `∑' n, ‖a n‖` converges and the rates `w n` satisfy `0 < b ≤ (w n).re` for all `n`, then
for `0 < s.re` the sequence of `(0, ∞)` `L¹`-norms
`∫ t in Ioi 0, ‖a n * (t ^ (s - 1) * e^{-w n * t})‖` is summable. -/
theorem summable_integral_norm_mul_cpow_mul_exp_neg_mul_Ioi {a w : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) {b : ℝ} (hb : 0 < b) (hw : ∀ n, b ≤ (w n).re)
    {s : ℂ} (hs : 0 < s.re) :
    Summable fun n : ℕ =>
      ∫ t : ℝ in Ioi 0, ‖a n * ((t : ℂ) ^ (s - 1) * exp (-(w n * t)))‖ := by
  let g₀ : ℝ → ℝ := fun t => ‖(t : ℂ) ^ (s - 1) * exp (-((b : ℂ) * t))‖
  have hb' : 0 < (b : ℂ).re := by simpa using hb
  have hg₀ : Integrable g₀ (volume.restrict (Ioi 0)) :=
    (integrableOn_cpow_mul_exp_neg_mul_Ioi hs hb').norm
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    (ha.mul_right (∫ t : ℝ in Ioi 0, g₀ t))
  rw [← integral_const_mul]
  have hwn : 0 < (w n).re := hb.trans_le (hw n)
  refine integral_mono_ae
    ((integrableOn_cpow_mul_exp_neg_mul_Ioi hs hwn).const_mul (a n)).norm
    (hg₀.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have h1 := norm_cpow_mul_log_pow_mul_exp_neg_mul (s - 1) (w n) 0 ht0
  have h2 := norm_cpow_mul_log_pow_mul_exp_neg_mul (s - 1) b 0 ht0
  simp only [pow_zero, mul_one, one_mul, ofReal_re] at h1 h2
  dsimp only [g₀]
  rw [norm_mul, h1, h2]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hw n]))
      (Real.rpow_nonneg ht0.le _))
    (norm_nonneg _)

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

section HalfLine

open Finset intervalIntegral
open scoped Real

/-- For `Re z > 0` and `δ > 0`, `t ↦ t^γ e^{-zt}` is integrable on `(δ, ∞)` for every `γ`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi_of_pos (γ : ℂ) {z : ℂ} (hz : 0 < z.re) {δ : ℝ}
    (hδ : 0 < δ) : IntegrableOn (fun t : ℝ => (t : ℂ) ^ γ * cexp (-(z * t))) (Ioi δ) := by
  set b : ℝ := max γ.re 0
  have hb : -1 < ((b : ℂ)).re := by simp only [ofReal_re]; linarith [le_max_right γ.re 0]
  have hI := ((integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi hb hz 0).mono_set
    (Ioi_subset_Ioi hδ.le)).norm.const_mul (δ ^ (γ.re - b))
  refine Integrable.mono' hI (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : δ < t)
  have ht0 : 0 < t := hδ.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, pow_zero, mul_one, norm_mul,
    norm_cpow_eq_rpow_re_of_pos ht0, ofReal_re, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (cexp (-(z * t))))
  have h1 : t ^ γ.re = t ^ (γ.re - b) * t ^ b := by
    rw [← Real.rpow_add ht0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hδ ht.le (by linarith [le_max_left γ.re 0])) (by positivity)

/-- One integration by parts in `∫_δ^∞ t^γ e^{-zt} dt`, for `Re z > 0` and `δ > 0`:
it equals `z⁻¹ δ^γ e^{-zδ} + z⁻¹ γ ∫_δ^∞ t^{γ-1} e^{-zt} dt`. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq_add_integral (γ : ℂ) {z : ℂ} (hz : 0 < z.re)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ t in Ioi δ, (t : ℂ) ^ γ * cexp (-(z * t)) =
      z⁻¹ * ((δ : ℂ) ^ γ * cexp (-(z * δ))) +
        z⁻¹ * (γ * ∫ t in Ioi δ, (t : ℂ) ^ (γ - 1) * cexp (-(z * t))) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hint₁ := integrableOn_cpow_mul_exp_neg_mul_Ioi_of_pos γ hz hδ
  have hu : ∀ t ∈ Ioi δ, HasDerivAt (fun t : ℝ => (t : ℂ) ^ γ) (γ * (t : ℂ) ^ (γ - 1)) t :=
    fun t (ht : δ < t) => by
      simpa using ((hasDerivAt_id (t : ℂ)).cpow_const (c := γ)
        (ofReal_mem_slitPlane.2 (hδ.trans ht))).comp_ofReal
  have hv : ∀ t ∈ Ioi δ, HasDerivAt (fun t : ℝ => -z⁻¹ * cexp (-(z * t))) (cexp (-(z * t))) t :=
    fun t _ => by
      have h : HasDerivAt (fun w : ℂ => -z⁻¹ * cexp (-(z * w)))
          (-z⁻¹ * (cexp (-(z * t)) * -(z * 1))) (t : ℂ) :=
        (((hasDerivAt_id (t : ℂ)).const_mul z).fun_neg.cexp).const_mul (-z⁻¹)
      convert h.comp_ofReal using 1
      field_simp
  have hint : IntegrableOn (fun t : ℝ => γ * (t : ℂ) ^ (γ - 1) * (-z⁻¹ * cexp (-(z * t))))
      (Ioi δ) := by
    have h : IntegrableOn (fun t : ℝ => -(γ * z⁻¹) * ((t : ℂ) ^ (γ - 1) * cexp (-(z * t))))
        (Ioi δ) := (integrableOn_cpow_mul_exp_neg_mul_Ioi_of_pos (γ - 1) hz hδ).const_mul _
    exact h.congr_fun (fun t _ => by ring) measurableSet_Ioi
  have hzero : Tendsto (fun t : ℝ => (t : ℂ) ^ γ * (-z⁻¹ * cexp (-(z * t)))) (𝓝[>] δ)
      (𝓝 ((δ : ℂ) ^ γ * (-z⁻¹ * cexp (-(z * δ))))) := by
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact (((hasDerivAt_id (δ : ℂ)).cpow_const (c := γ)
      (ofReal_mem_slitPlane.2 hδ)).comp_ofReal.continuousAt).mul (by fun_prop)
  have hinf : Tendsto (fun t : ℝ => (t : ℂ) ^ γ * (-z⁻¹ * cexp (-(z * t)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero γ.re z.re hz).const_mul ‖z⁻¹‖
    rw [mul_zero] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, neg_mul]
    exact le_of_eq (by ring)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint₁ hint hzero hinf
  have hc : ∫ t in Ioi δ, γ * (t : ℂ) ^ (γ - 1) * (-z⁻¹ * cexp (-(z * t))) =
      -(z⁻¹ * γ) * ∫ t in Ioi δ, (t : ℂ) ^ (γ - 1) * cexp (-(z * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun t => by ring)
  rw [h, hc]
  ring

/-- `n` integrations by parts in `∫_δ^∞ t^{α-1} e^{-zt} dt`, for `Re z > 0` and `δ > 0`. The
`k`-th endpoint term carries the falling factorial `(α - 1)(α - 2)⋯(α - k)`. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq_sum_add_integral (α : ℂ) {z : ℂ} (hz : 0 < z.re)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ t in Ioi δ, (t : ℂ) ^ (α - 1) * cexp (-(z * t)) =
      ∑ k ∈ range n, z⁻¹ ^ (k + 1) * ((descPochhammer ℂ k).eval (α - 1) *
          ((δ : ℂ) ^ (α - 1 - k) * cexp (-(z * δ)))) +
        z⁻¹ ^ n * ((descPochhammer ℂ n).eval (α - 1) *
          ∫ t in Ioi δ, (t : ℂ) ^ (α - 1 - n) * cexp (-(z * t))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- The exponent produced by the last integration by parts, `α - 1 - n - 1`, must be put in
    -- the form `α - 1 - (n + 1)` with a cast natural number to match the statement at `n + 1`.
    have hexp : α - 1 - (n : ℂ) - 1 = α - 1 - ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [ih, integral_cpow_mul_exp_neg_mul_Ioi_eq_add_integral (α - 1 - n) hz hδ,
      sum_range_succ, descPochhammer_succ_eval, hexp]
    ring

/-- For `Re w ≥ 0` and `t > 0`, `‖t^γ e^{-wt}‖ ≤ t^{Re γ}`. -/
theorem norm_cpow_mul_exp_neg_mul_le (γ : ℂ) {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ}
    (ht : 0 < t) : ‖(t : ℂ) ^ γ * cexp (-(w * t))‖ ≤ t ^ γ.re := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, Left.neg_nonpos_iff]
  positivity

/-- For `Re γ < -1` and `δ > 0`, the oscillatory power `t ↦ t^γ e^{ixt}` is integrable on
`(δ, ∞)` for every real `x`. -/
theorem integrableOn_cpow_mul_exp_mul_I_Ioi {γ : ℂ} (hγ : γ.re < -1) (x : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ γ * cexp (((x * t : ℝ) : ℂ) * I)) (Ioi δ) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hγ hδ) (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : δ < t)
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_cpow_eq_rpow_re_of_pos (hδ.trans ht)]

/-- The Gamma integral `∫₀^∞ t^{α-1} e^{-wt} dt` split at `δ`, with the part over `(δ, ∞)`
integrated by parts `n` times. For `0 < Re α < n` each term is defined and continuous on the closed
half-plane `Re w ≥ 0` away from `w = 0`, so this continues the Gamma integral to the imaginary
axis. -/
private noncomputable def gammaSplit (α : ℂ) (δ : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..δ, (t : ℂ) ^ (α - 1) * cexp (-(w * t))) +
    ∑ k ∈ range n, w⁻¹ ^ (k + 1) * ((descPochhammer ℂ k).eval (α - 1) *
      ((δ : ℂ) ^ (α - 1 - k) * cexp (-(w * δ)))) +
    w⁻¹ ^ n * ((descPochhammer ℂ n).eval (α - 1) *
      ∫ t in Ioi δ, (t : ℂ) ^ (α - 1 - n) * cexp (-(w * t)))

/-- On `Re z > 0` the split Gamma integral is `Γ(α) z^{-α}`. -/
private theorem gammaSplit_of_re_pos {α z : ℂ} (hα : 0 < α.re) (hz : 0 < z.re) {δ : ℝ}
    (hδ : 0 < δ) (n : ℕ) : gammaSplit α δ n z = Gamma α * z ^ (-α) := by
  have hint := integrableOn_cpow_mul_exp_neg_mul_Ioi hα hz
  rw [gammaSplit, add_assoc, ← integral_cpow_mul_exp_neg_mul_Ioi_eq_sum_add_integral α hz hδ n,
    intervalIntegral.integral_of_le hδ.le,
    ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hδ.le)),
    Ioc_union_Ioi_eq_Ioi hδ.le, integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hα hz]

/-- The split Gamma integral is continuous at the boundary point `-ix`, approached along
`ε - ix` as `ε → 0+`; the integrals converge by dominated convergence. -/
private theorem tendsto_gammaSplit {α : ℂ} (hα : 0 < α.re) {n : ℕ} (hn : α.re < n) {x δ : ℝ}
    (hx : x ≠ 0) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ => gammaSplit α δ n (ε - x * I)) (𝓝[>] 0)
      (𝓝 (gammaSplit α δ n (-(x * I)))) := by
  set z : ℝ → ℂ := fun ε => (ε : ℂ) - x * I with hzdef
  have hz0 : z 0 = -(x * I) := by simp [hzdef]
  have hzc : Continuous z := by fun_prop
  have hzne : z 0 ≠ 0 := by simp [hz0, hx]
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ (z ε).re :=
    eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => by simpa [hzdef] using hε.le
  have hk : ∀ t : ℝ, Tendsto (fun ε => cexp (-(z ε * t))) (𝓝[>] 0) (𝓝 (cexp (-(z 0 * t)))) :=
    fun t => ((by fun_prop : Continuous fun ε => cexp (-(z ε * t))).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hinv := ((hzc.tendsto 0).inv₀ hzne).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [← hz0]
  refine Tendsto.add (Tendsto.add ?_ (tendsto_finsetSum _ fun k _ => (hinv.pow (k + 1)).mul
    (((hk δ).const_mul _).const_mul _))) ((hinv.pow n).mul (Tendsto.const_mul _ ?_))
  · refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t => t ^ (α.re - 1)) (Eventually.of_forall fun ε => by fun_prop) ?_
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      (Eventually.of_forall fun t _ => (hk t).const_mul _)
    filter_upwards [hpos] with ε hε
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hδ.le] at ht
    simpa using norm_cpow_mul_exp_neg_mul_le (α - 1) hε ht.1
  · refine tendsto_integral_filter_of_dominated_convergence (fun t => t ^ (α.re - 1 - n))
      (Eventually.of_forall fun ε => by fun_prop) ?_
      (integrableOn_Ioi_rpow_of_lt (by linarith) hδ)
      (Eventually.of_forall fun t => (hk t).const_mul _)
    filter_upwards [hpos] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : δ < t)
    simpa using norm_cpow_mul_exp_neg_mul_le (α - 1 - n) hε (hδ.trans ht)

/-- The value of the split Gamma integral at `-ix`, `x > 0`, is `Γ(α) (-ix)^{-α} =
e^{iπα/2} Γ(α) x^{-α}`. -/
private theorem gammaSplit_neg_mul_I {α : ℂ} (hα : 0 < α.re) {n : ℕ} (hn : α.re < n) {x δ : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) :
    gammaSplit α δ n (-(x * I)) = cexp (π * I * α / 2) * Gamma α * (x : ℂ) ^ (-α) := by
  have hslit : -((x : ℂ) * I) ∈ slitPlane := by simp [mem_slitPlane_iff, hx.ne']
  have hlim : Tendsto (fun ε : ℝ => gammaSplit α δ n (ε - x * I)) (𝓝[>] 0)
      (𝓝 (Gamma α * (-(x * I)) ^ (-α))) := by
    have hc : Tendsto (fun ε : ℝ => ((ε : ℂ) - x * I)) (𝓝 0) (𝓝 (-(x * I))) := by
      simpa using ((by fun_prop : Continuous fun ε : ℝ => ((ε : ℂ) - x * I)).tendsto 0)
    refine ((((continuousAt_cpow_const hslit).tendsto.comp hc).const_mul _).mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (gammaSplit_of_re_pos hα (by simpa using hε) hδ n).symm
  -- Writing `-ix` as the product `x • (-i)` of a positive real and `-i` lets the power split as
  -- `x^{-α} (-i)^{-α}`, and `(-i)^{-α} = e^{iπα/2}` since `log (-i) = -iπ/2`.
  have hfac : -((x : ℂ) * I) = x * (-I) := by ring
  rw [tendsto_nhds_unique (tendsto_gammaSplit hα hn hx.ne' hδ) hlim, hfac,
    ofReal_mul_cpow hx.le, cpow_def_of_ne_zero (neg_ne_zero.2 I_ne_zero), log_neg_I]
  ring_nf

/-- **The Fourier integral of `t^{α-1}`, regularised by integration by parts.** For
`0 < Re α < n`, `x > 0` and `δ > 0`, split `∫₀^∞ e^{ixt} t^{α-1} dt` at `δ` and integrate the part
over `(δ, ∞)` by parts `n` times, so that the remaining integral converges absolutely. The
resulting expression is `e^{iπα/2} Γ(α) x^{-α}`, the value at `z = -ix` of the Gamma integral
`∫₀^∞ t^{α-1} e^{-zt} dt = Γ(α) z^{-α}`, which it continues to the imaginary axis. -/
theorem integral_cpow_mul_exp_mul_I_add_sum_eq {α : ℂ} (hα : 0 < α.re) {n : ℕ} (hn : α.re < n)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..δ, (t : ℂ) ^ (α - 1) * cexp (((x * t : ℝ) : ℂ) * I)) +
        ∑ k ∈ range n, (I / x) ^ (k + 1) * ((descPochhammer ℂ k).eval (α - 1) *
          ((δ : ℂ) ^ (α - 1 - k) * cexp (((x * δ : ℝ) : ℂ) * I))) +
        (I / x) ^ n * ((descPochhammer ℂ n).eval (α - 1) *
          ∫ t in Ioi δ, (t : ℂ) ^ (α - 1 - n) * cexp (((x * t : ℝ) : ℂ) * I)) =
      cexp (π * I * α / 2) * Gamma α * (x : ℂ) ^ (-α) := by
  have hinv : (-((x : ℂ) * I))⁻¹ = I / x := by
    have : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
    field_simp
    ring_nf
    simp
  have hexp : ∀ t : ℝ, cexp (-(-((x : ℂ) * I) * t)) = cexp (((x * t : ℝ) : ℂ) * I) := fun t => by
    push_cast; ring_nf
  rw [← gammaSplit_neg_mul_I hα hn hx hδ, gammaSplit]
  simp only [hinv, hexp]

end HalfLine

end Complex

namespace TauCeti

open Complex

/-- For `Re s > 0` and `Re w > 0`, the integral of `|t^{s-1} e^{-wt}|` over `(0, ∞)` is
`(1 / Re w)^{Re s} Γ(Re s)`. -/
theorem integral_norm_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * cexp (-(w * t))‖ =
      (1 / w.re) ^ s.re * Real.Gamma s.re := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs hw]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simpa [neg_mul] using norm_cpow_mul_log_pow_mul_exp_neg_mul (s - 1) w 0 ht

end TauCeti
