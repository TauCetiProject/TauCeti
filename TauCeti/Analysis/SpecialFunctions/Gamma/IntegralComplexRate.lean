/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import TauCeti.Analysis.LaplaceTransform.Basic

/-!
# The Gamma integral with a complex rate

For `Re s > 0` and `Re z > 0`,
`∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s}` with the principal power `z^{-s}`.

Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` is the case of a positive real rate. Both
sides are holomorphic in `z` on the right half-plane: the integral by differentiation under the
integral sign, the right side because the half-plane lies in the slit plane. They agree on the
positive reals, so they agree on the half-plane by the identity theorem.

## Main results

* `Complex.norm_cpow_mul_exp_neg_mul`: norm identity for `t^{s-1} e^{-wt}` on `t > 0`.
* `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`: the Gamma integral with complex rate.
* `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi` and
  `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi`: the integral converges and is
  holomorphic in the rate on the right half-plane.
* `TauCeti.integral_norm_cpow_mul_exp_neg_mul_Ioi`: the integral of the norm of the integrand is
  `(1 / Re w)^{Re s} Γ(Re s)`.
* `TauCeti.exists_summable_integral_norm_cpow_mul_exp_neg_natCast_add_le` and
  `TauCeti.exists_mem_nhds_summable_integral_norm_cpow_mul_exp_neg_natCast_add_le`: compact and
  local uniform summable majorants for `∫ t in Ioi 0, ‖t ^ (p.1 - 1) * cexp (-((n + p.2) * t))‖`
  on `{p | 1 < p.1.re ∧ 0 < p.2.re}`.

The proof is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMFMathlib/Analysis/Asymptotics/WatsonSector.lean`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Complex

/-- The norm of the integrand `t^{s-1} e^{-wt}` for `t > 0`. -/
theorem norm_cpow_mul_exp_neg_mul (s w : ℂ) {t : ℝ} (ht : 0 < t) :
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
  rw [norm_cpow_mul_exp_neg_mul s w ht, neg_mul]

/-- On any compact subset `K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ 0 < p.2.re}`, the `L¹((0, ∞))`
norms `∫ t in Ioi 0, ‖t ^ (p.1 - 1) * cexp (-((n + p.2) * t))‖` admit a uniform summable
majorant. -/
theorem exists_summable_integral_norm_cpow_mul_exp_neg_natCast_add_le {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hK_sub : K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ 0 < p.2.re}) :
    ∃ a : ℕ → ℝ, Summable a ∧ ∀ p ∈ K, ∀ n : ℕ,
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (p.1 - 1) * cexp (-((n + p.2) * t))‖ ≤ a n := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨fun _ => 0, summable_zero, fun _ hp => False.elim hp⟩
  obtain ⟨p₀, hp₀, hp₀_min⟩ :=
    hK.exists_isMinOn hKne (continuous_re.comp continuous_fst).continuousOn
  obtain ⟨p₁, hp₁, hp₁_min⟩ :=
    hK.exists_isMinOn hKne (continuous_re.comp continuous_snd).continuousOn
  obtain ⟨B_re, hB_re⟩ :=
    hK.exists_bound_of_continuousOn (continuous_re.comp continuous_fst).continuousOn
  have hB_re' : ∀ p ∈ K, p.1.re ≤ max B_re 0 := fun p hp =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB_re p hp)).trans (le_max_left _ _)
  have hcont_G : ContinuousOn (fun p : ℂ × ℂ => Real.Gamma p.1.re) K :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_re.comp continuous_fst).continuousOn
      fun p hp => lt_trans zero_lt_one (hK_sub hp).1
  obtain ⟨G, hG⟩ := hK.exists_bound_of_continuousOn hcont_G
  have hG' : ∀ p ∈ K, Real.Gamma p.1.re ≤ max G 0 := fun p hp =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hG p hp)).trans (le_max_left _ _)
  let a : ℕ → ℝ := fun n =>
    max G 0 * if n = 0 then (max 1 p₁.2.re⁻¹) ^ max B_re 0 else (n : ℝ) ^ (-p₀.1.re)
  refine ⟨a, ?_, fun p hp n => ?_⟩
  · rw [← summable_nat_add_iff 1]
    exact (((summable_nat_add_iff 1).mpr ((Real.summable_nat_rpow (p := -p₀.1.re)).mpr
      (by linarith [(hK_sub hp₀).1]))).mul_left (max G 0)).congr fun n => by simp [a]
  · have hpos : 0 < ((n : ℂ) + p.2).re := by
      simp only [add_re, natCast_re]
      linarith [(hK_sub hp).2, Nat.cast_nonneg (α := ℝ) n]
    rw [integral_norm_cpow_mul_exp_neg_mul_Ioi (by linarith [(hK_sub hp).1]) hpos,
      one_div, ← Real.rpow_neg_eq_inv_rpow, add_re, natCast_re, mul_comm]
    refine mul_le_mul (hG' p hp) ?_ (Real.rpow_nonneg (by linarith [(hK_sub hp).2]) _)
      (le_max_right _ _)
    have hη_pos : 0 < p₁.2.re := (hK_sub hp₁).2
    rcases n with _ | m
    · simp only [Nat.cast_zero, zero_add, ↓reduceIte]
      have h1 : p.2.re ^ (-p.1.re) ≤ p₁.2.re ^ (-p.1.re) :=
        Real.rpow_le_rpow_of_nonpos hη_pos (hp₁_min hp) (by linarith [(hK_sub hp).1])
      have h2 : p₁.2.re ^ (-p.1.re) = (p₁.2.re⁻¹) ^ p.1.re := by
        rw [Real.rpow_neg hη_pos.le, Real.inv_rpow hη_pos.le]
      exact h1.trans (h2.symm ▸ (Real.rpow_le_rpow (by positivity) (le_max_right _ _)
        (by linarith [(hK_sub hp).1])).trans
        (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (hB_re' p hp)))
    · simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [(hK_sub hp).2])
        (by linarith [(hK_sub hp).1])).trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (neg_le_neg (hp₀_min hp)))

/-- Locally around any `(s₀, c₀)` with `1 < s₀.re` and `0 < c₀.re`, the `L¹((0, ∞))`
norms `∫ t in Ioi 0, ‖t ^ (p.1 - 1) * cexp (-((n + p.2) * t))‖` admit a uniform summable
majorant. -/
theorem exists_mem_nhds_summable_integral_norm_cpow_mul_exp_neg_natCast_add_le {s₀ c₀ : ℂ}
    (hs₀ : 1 < s₀.re) (hc₀ : 0 < c₀.re) :
    ∃ U ∈ 𝓝 (s₀, c₀), ∃ a : ℕ → ℝ, Summable a ∧ ∀ p ∈ U, ∀ n : ℕ,
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (p.1 - 1) * cexp (-((n + p.2) * t))‖ ≤ a n := by
  let r : ℝ := min ((s₀.re - 1) / 2) (c₀.re / 2)
  let B := Metric.closedBall (s₀, c₀) r
  have hK_sub : B ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ 0 < p.2.re} := fun p hp => by
    have hdist : dist p (s₀, c₀) ≤ r := Metric.mem_closedBall.mp hp
    have h1 : |p.1.re - s₀.re| ≤ r := (abs_re_le_norm (p.1 - s₀)).trans
      (by rw [← dist_eq]; exact (le_max_left (dist p.1 s₀) (dist p.2 c₀)).trans hdist)
    have h2 : |p.2.re - c₀.re| ≤ r := (abs_re_le_norm (p.2 - c₀)).trans
      (by rw [← dist_eq]; exact (le_max_right (dist p.1 s₀) (dist p.2 c₀)).trans hdist)
    exact ⟨by linarith [(abs_le.mp h1).1, min_le_left ((s₀.re - 1) / 2) (c₀.re / 2)],
      by linarith [(abs_le.mp h2).1, min_le_right ((s₀.re - 1) / 2) (c₀.re / 2)]⟩
  obtain ⟨a, ha_sum, ha_le⟩ :=
    exists_summable_integral_norm_cpow_mul_exp_neg_natCast_add_le
      (isCompact_closedBall (s₀, c₀) r) hK_sub
  exact ⟨B, Metric.closedBall_mem_nhds _ (lt_min (by linarith) (by linarith)), a, ha_sum, ha_le⟩

end TauCeti
