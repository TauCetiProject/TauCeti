/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Differentiated Stieltjes–Burgers time evolution of the Pastur semigroup

For a finite Borel measure `ν` on `ℝ`, the resolvent transform `m_t(z) = ∫ (x - z)⁻¹ d(ν.pastur t)`
of its Pastur evolution satisfies Pastur's self-consistent equation `m_t(z) = m_ν(z + t m_t(z))`
off the real axis. Differentiating with respect to `t` via the `dslope` linearization of the Pastur
equation and eliminating `m_ν'(z + t m_t(z))` against `∂_z m_t(z) = m_ν'(ζ) / (1 - t m_ν'(ζ))`
yields the **complex inviscid Burgers differential equation**

`∂_t m_t(z) = m_t(z) ∂_z m_t(z)`

at every `z` off the real axis (for an infinite measure `ν`, `ν.pastur t = 0` so both sides vanish).
The integrated Burgers flow `TauCeti.Probability.IsBurgersFlow` and uniqueness from the initial
measure are established in `TauCeti.Probability.DysonBrownianMotion.Pastur`.

Note the sign convention: Mathlib's `MeasureTheory.resolventTransform` uses `(x - z)⁻¹`. For the
opposite-sign Stieltjes transform `G_t(z) = ∫ (z - x)⁻¹ dμ_t(x) = -m_t(z)` used in Anderson,
Guionnet, and Zeitouni, Proposition 4.3.10, this same differential equation reads
`∂_t G_t = -G_t ∂_z G_t`.

## Main results

* `MeasureTheory.norm_resolventTransform_pastur_sub_le`: quantitative Lipschitz regularity in time
  of `t ↦ resolventTransform (ν.pastur t) z` off the real axis.
* `MeasureTheory.continuous_resolventTransform_pastur` and
  `MeasureTheory.continuous_deriv_resolventTransform_pastur`: continuity in `t : ℝ≥0` of `m_t(z)`
  and `∂_z m_t(z)` off the real axis.
* `MeasureTheory.hasDerivWithinAt_resolventTransform_pastur_Ici` and
  `MeasureTheory.hasDerivAt_resolventTransform_pastur_time`: time derivative
  `∂_t m_t(z) = m_t(z) ∂_z m_t(z)` on `[0, ∞)` and `(0, ∞)`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Proposition 4.3.10 and §4.3.2.
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993), 555–570.
* P. Biane, *On the free convolution with a semi-circular distribution*, Indiana Univ. Math. J.
  46 (1997), 705–718.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped NNReal Topology

namespace MeasureTheory

variable {ν : Measure ℝ}

/-- **Time-Lipschitz bound for the Pastur resolvent transform.** Off the real axis,
`‖m_{ν.pastur t}(z) - m_{ν.pastur s}(z)‖ ≤ |t - s| · |Im z|⁻³ · ν(ℝ)²`. -/
theorem norm_resolventTransform_pastur_sub_le (s t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform (ν.pastur t) z - resolventTransform (ν.pastur s) z‖ ≤
      |(t : ℝ) - s| * |z.im|⁻¹ ^ 3 * ν.real univ ^ 2 := by
  wlog hst : s ≤ t generalizing s t
  · rw [norm_sub_rev, abs_sub_comm]
    exact this t s (le_of_not_ge hst)
  let d : ℝ≥0 := t - s
  have hd_coe : (d : ℝ) = |(t : ℝ) - s| := by
    rw [NNReal.coe_sub hst, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))]
  have hpastur : ν.pastur t = (ν.pastur s).pastur d := by
    rw [Measure.pastur_pastur, add_tsub_cancel_of_le hst]
  rw [hpastur]
  let wt := resolventTransform ((ν.pastur s).pastur d) z
  have hwt_eq : wt = resolventTransform (ν.pastur s) (z + d * wt) :=
    resolventTransform_pastur_eq d hz
  have hζim_ge : |z.im| ≤ |(z + d * wt).im| :=
    abs_im_le_abs_im_add_mul_resolventTransform_pastur (ν := ν.pastur s) d z
  have hζ0 : (z + d * wt).im ≠ 0 :=
    im_add_mul_resolventTransform_pastur_ne_zero (ν := ν.pastur s) d hz
  have hwt_norm : ‖wt‖ ≤ |z.im|⁻¹ * ν.real univ := by
    simpa [wt] using norm_resolventTransform_le (μ := (ν.pastur s).pastur d) hz
  have hsub :
      ‖resolventTransform (ν.pastur s) (z + d * wt) - resolventTransform (ν.pastur s) z‖ ≤
        (d : ℝ) * ‖wt‖ / (|(z + d * wt).im| * |z.im|) * ν.real univ := by
    simpa [add_sub_cancel_left, norm_mul, norm_real, Real.norm_of_nonneg d.coe_nonneg,
      Measure.pastur_real_univ] using
      norm_resolventTransform_sub_le (μ := ν.pastur s) hζ0 hz
  calc ‖wt - resolventTransform (ν.pastur s) z‖
      = ‖resolventTransform (ν.pastur s) (z + d * wt) - resolventTransform (ν.pastur s) z‖ := by
        rw [← hwt_eq]
    _ ≤ (d : ℝ) * ‖wt‖ / (|(z + d * wt).im| * |z.im|) * ν.real univ := hsub
    _ ≤ (d : ℝ) * (|z.im|⁻¹ * ν.real univ) / (|z.im| * |z.im|) * ν.real univ := by
        have : 0 < |z.im| := abs_pos.2 hz
        gcongr
    _ = |(t : ℝ) - s| * |z.im|⁻¹ ^ 3 * ν.real univ ^ 2 := by
        rw [hd_coe]
        have hzpos : |z.im| ≠ 0 := abs_ne_zero.2 hz
        field_simp [hzpos]

/-- Off the real axis, `t ↦ resolventTransform (ν.pastur t) z` is continuous on `ℝ≥0`. -/
@[fun_prop]
theorem continuous_resolventTransform_pastur {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun t : ℝ≥0 ↦ resolventTransform (ν.pastur t) z :=
  (LipschitzWith.of_dist_le_mul
    (K := Real.toNNReal (|z.im|⁻¹ ^ 3 * ν.real univ ^ 2)) fun t s ↦ by
      rw [dist_eq_norm, NNReal.dist_eq, Real.coe_toNNReal _ (by positivity), mul_comm, ← mul_assoc]
      exact norm_resolventTransform_pastur_sub_le s t hz).continuous

/-- Algebraic `dslope` linearization of the Pastur equation in time: letting
`ζ(u) = z + u * m_{ν.pastur u}(z)` and `q = dslope (resolventTransform ν) (ζ t) (ζ s)`, we have
`(1 - t * q) * (m_s(z) - m_t(z)) = (s - t) * (m_s(z) * q)`. -/
private lemma one_sub_mul_dslope_mul_resolventTransform_pastur_sub [IsFiniteMeasure ν]
    {z : ℂ} (hz : z.im ≠ 0) (s t : ℝ≥0) :
    (1 - (t : ℂ) * dslope (resolventTransform ν)
        (z + t * resolventTransform (ν.pastur t) z)
        (z + s * resolventTransform (ν.pastur s) z)) *
      (resolventTransform (ν.pastur s) z - resolventTransform (ν.pastur t) z) =
    ((s : ℂ) - t) *
      (resolventTransform (ν.pastur s) z * dslope (resolventTransform ν)
        (z + t * resolventTransform (ν.pastur t) z)
        (z + s * resolventTransform (ν.pastur s) z)) := by
  set fs := resolventTransform (ν.pastur s) z
  set ft := resolventTransform (ν.pastur t) z
  have hfs : fs = resolventTransform ν (z + s * fs) := resolventTransform_pastur_eq s hz
  have hft : ft = resolventTransform ν (z + t * ft) := resolventTransform_pastur_eq t hz
  have hdiff : (z + s * fs) - (z + t * ft) = ((s : ℂ) - t) * fs + (t : ℂ) * (fs - ft) := by ring
  have h1 : fs - ft = (((s : ℂ) - t) * fs + (t : ℂ) * (fs - ft)) *
      dslope (resolventTransform ν) (z + t * ft) (z + s * fs) := by
    rw [← hdiff]
    nth_rw 1 [hfs, hft]
    simpa only [smul_eq_mul] using
      (sub_smul_dslope (resolventTransform ν) (z + t * ft) (z + s * fs)).symm
  linear_combination h1

/-- **Time-derivative of the Pastur resolvent transform on `[0, ∞)`.** For every measure `ν` on
`ℝ`, `z : ℂ` with `z.im ≠ 0`, and `t : ℝ` with `0 ≤ t`, the map
`s ↦ resolventTransform (ν.pastur s.toNNReal) z` has derivative `m_t(z) ∂_z m_t(z)` within `[0, ∞)`
at `t`. -/
theorem hasDerivWithinAt_resolventTransform_pastur_Ici {z : ℂ} (hz : z.im ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ ↦ resolventTransform (ν.pastur s.toNNReal) z)
      (resolventTransform (ν.pastur t.toNNReal) z *
        deriv (resolventTransform (ν.pastur t.toNNReal)) z) (Ici 0) t := by
  by_cases hν : IsFiniteMeasure ν
  · let f : ℝ → ℂ := fun s ↦ resolventTransform (ν.pastur s.toNNReal) z
    let ζ : ℝ → ℂ := fun s ↦ z + (s.toNNReal : ℂ) * f s
    let d : ℂ := deriv (resolventTransform ν) (ζ t)
    have hζ0 : (ζ t).im ≠ 0 := im_add_mul_resolventTransform_pastur_ne_zero t.toNNReal hz
    have hm_deriv : HasDerivAt (resolventTransform ν) d (ζ t) :=
      (hasDerivAt_resolventTransform_of_im_ne_zero (μ := ν) hζ0).differentiableAt.hasDerivAt
    have ht_coe_c : ((t.toNNReal : ℝ) : ℂ) = (t : ℂ) :=
      congrArg Complex.ofReal (Real.coe_toNNReal t ht)
    have hjac : 1 - (t : ℂ) * d ≠ 0 := by
      rw [← ht_coe_c]
      exact one_sub_mul_deriv_resolventTransform_add_mul_resolventTransform_pastur_ne_zero
        (ν := ν) t.toNNReal hz
    have hderiv_z : deriv (resolventTransform (ν.pastur t.toNNReal)) z = d / (1 - (t : ℂ) * d) := by
      rw [← ht_coe_c]
      exact (hasDerivAt_resolventTransform_pastur (ν := ν) t.toNNReal hz).deriv
    -- Limits of the numerator `f s * Q (ζ s)` and denominator `1 - t * Q (ζ s)` as `s → t`
    let Q : ℂ → ℂ := dslope (resolventTransform ν) (ζ t)
    have hQd : Q (ζ t) = d := dslope_same (resolventTransform ν) (ζ t)
    have hQ_cont : ContinuousAt Q (ζ t) := continuousAt_dslope_same.2 hm_deriv.differentiableAt
    have hf_cont : Continuous f :=
      (continuous_resolventTransform_pastur (ν := ν) hz).comp continuous_real_toNNReal
    have hζ_cont : Continuous ζ := continuous_const.add
      ((continuous_ofReal.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)).mul hf_cont)
    have hQζ_lim : Tendsto (fun s : ℝ ↦ Q (ζ s)) (𝓝[Ici 0 \ {t}] t) (𝓝 d) :=
      hQd ▸ (hQ_cont.comp hζ_cont.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have hnum_lim : Tendsto (fun s : ℝ ↦ f s * Q (ζ s)) (𝓝[Ici 0 \ {t}] t) (𝓝 (f t * d)) :=
      (hf_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hQζ_lim
    have hden_lim : Tendsto (fun s : ℝ ↦ 1 - (t : ℂ) * Q (ζ s)) (𝓝[Ici 0 \ {t}] t)
        (𝓝 (1 - (t : ℂ) * d)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hQζ_lim)
    -- Rewrite the slope `(s - t)⁻¹ • (f s - f t)` using the `dslope` linearization
    rw [hasDerivWithinAt_iff_tendsto_slope, hderiv_z, ← mul_div_assoc]
    refine (hnum_lim.div hden_lim hjac).congr' ?_
    filter_upwards [self_mem_nhdsWithin, hden_lim.eventually_ne hjac] with s ⟨hs0, hst⟩ hden
    have hs_coe_c : ((s.toNNReal : ℝ) : ℂ) = (s : ℂ) :=
      congrArg Complex.ofReal (Real.coe_toNNReal s hs0)
    have hlin : (1 - (t : ℂ) * Q (ζ s)) * (f s - f t) = (s - t : ℂ) * (f s * Q (ζ s)) := by
      simpa only [f, ζ, Q, hs_coe_c, ht_coe_c] using
        one_sub_mul_dslope_mul_resolventTransform_pastur_sub (ν := ν) hz s.toNNReal t.toNNReal
    have hst' : (s - t : ℂ) ≠ 0 := by rw [← ofReal_sub, ofReal_ne_zero]; exact sub_ne_zero.2 hst
    rw [Pi.div_apply, slope_def_module, real_smul, ofReal_inv, ofReal_sub, div_eq_iff hden]
    calc f s * Q (ζ s)
        = ((s : ℂ) - t)⁻¹ * ((s - t : ℂ) * (f s * Q (ζ s))) := by field_simp [hst']
      _ = ((s : ℂ) - t)⁻¹ * ((1 - (t : ℂ) * Q (ζ s)) * (f s - f t)) := by rw [← hlin]
      _ = ((s : ℂ) - t)⁻¹ * (f s - f t) * (1 - (t : ℂ) * Q (ζ s)) := by ring
  · simpa [Measure.pastur_of_not_isFiniteMeasure hν] using hasDerivWithinAt_const t (Ici 0) (0 : ℂ)

/-- **The Stieltjes–Burgers differential equation.** For `0 < t` and `z.im ≠ 0`, the map
`s ↦ resolventTransform (ν.pastur s.toNNReal) z` is differentiable at `t` with derivative
`m_t(z) ∂_z m_t(z)`. -/
theorem hasDerivAt_resolventTransform_pastur_time {z : ℂ} (hz : z.im ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ resolventTransform (ν.pastur s.toNNReal) z)
      (resolventTransform (ν.pastur t.toNNReal) z *
        deriv (resolventTransform (ν.pastur t.toNNReal)) z) t :=
  (hasDerivWithinAt_resolventTransform_pastur_Ici hz ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- Off the real axis, `t ↦ deriv (resolventTransform (ν.pastur t)) z` is continuous on `ℝ≥0`. -/
@[fun_prop]
theorem continuous_deriv_resolventTransform_pastur {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun t : ℝ≥0 ↦ deriv (resolventTransform (ν.pastur t)) z := by
  by_cases hν : IsFiniteMeasure ν
  · let ζ : ℝ≥0 → ℂ := fun t ↦ z + t * resolventTransform (ν.pastur t) z
    have hζ_cont : Continuous ζ :=
      continuous_const.add ((continuous_ofReal.comp NNReal.continuous_coe).mul
        (continuous_resolventTransform_pastur hz))
    have hd_cont : Continuous fun t : ℝ≥0 ↦ deriv (resolventTransform ν) (ζ t) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (analyticOnNhd_resolventTransform (ζ t)
        (im_add_mul_resolventTransform_pastur_ne_zero t hz)).deriv.continuousAt.comp
        hζ_cont.continuousAt
    have hden_cont : Continuous fun t : ℝ≥0 ↦
        1 - (t : ℂ) * deriv (resolventTransform ν) (ζ t) :=
      continuous_const.sub ((continuous_ofReal.comp NNReal.continuous_coe).mul hd_cont)
    have eq_fun : (fun t : ℝ≥0 ↦ deriv (resolventTransform (ν.pastur t)) z) =
        fun t : ℝ≥0 ↦ deriv (resolventTransform ν) (ζ t) /
          (1 - (t : ℂ) * deriv (resolventTransform ν) (ζ t)) := by
      ext t
      exact (hasDerivAt_resolventTransform_pastur t hz).deriv
    rw [eq_fun]
    exact hd_cont.div hden_cont fun t ↦
      one_sub_mul_deriv_resolventTransform_add_mul_resolventTransform_pastur_ne_zero t hz
  · simpa [Measure.pastur_of_not_isFiniteMeasure hν] using continuous_const

end MeasureTheory

end
