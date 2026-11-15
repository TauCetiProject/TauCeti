/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stieltjes–Burgers time evolution of the Pastur semigroup

For a finite Borel measure `ν` on `ℝ`, the resolvent transform `m_t(z) = ∫ (x - z)⁻¹ d(ν.pastur t)`
of its Pastur evolution satisfies Pastur's self-consistent equation `m_t(z) = m_ν(z + t m_t(z))`
off the real axis. Differentiating with respect to `t` and eliminating `m_ν'(z + t m_t(z))` against
`∂_z m_t(z) = m_ν'(ζ) / (1 - t m_ν'(ζ))` yields the **complex inviscid Burgers equation**

`∂_t m_t(z) = m_t(z) ∂_z m_t(z)`

and its integral form

`m_t(z) = m_ν(z) + ∫ s in 0..t, m_s(z) ∂_z m_s(z)`.

Note the sign convention: Mathlib's `MeasureTheory.resolventTransform` uses `(x - z)⁻¹`. For the
opposite-sign Stieltjes transform `G_t(z) = ∫ (z - x)⁻¹ dμ_t(x) = -m_t(z)` used in Anderson,
Guionnet, and Zeitouni, Proposition 4.3.10, this same identity reads `∂_t G_t = -G_t ∂_z G_t`, i.e.,
`G_t(z) = G_0(z) - ∫ s in 0..t, G_s(z) ∂_z G_s(z)`.

## Main results

* `MeasureTheory.norm_resolventTransform_pastur_sub_le`: quantitative Lipschitz regularity in time
  of `t ↦ resolventTransform (ν.pastur t) z` off the real axis.
* `MeasureTheory.continuous_resolventTransform_pastur` and
  `MeasureTheory.continuous_deriv_resolventTransform_pastur`: continuity in `t : ℝ≥0` of `m_t(z)`
  and `∂_z m_t(z)` off the real axis.
* `MeasureTheory.hasDerivWithinAt_resolventTransform_pastur_Ici` and
  `MeasureTheory.hasDerivAt_resolventTransform_pastur_time`: time derivative
  `∂_t m_t(z) = m_t(z) ∂_z m_t(z)` on `[0, ∞)` and `(0, ∞)`.
* `MeasureTheory.resolventTransform_pastur_eq_add_integral`: the Stieltjes–Burgers integral equation
  off the real axis for every finite measure `ν`.

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

variable {ν : Measure ℝ} [IsFiniteMeasure ν]

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
  let wt := resolventTransform (ν.pastur t) z
  have hwt_eq : wt = resolventTransform (ν.pastur s) (z + d * wt) := by
    dsimp only [wt]
    rw [← add_tsub_cancel_of_le hst, ← Measure.pastur_pastur]
    exact resolventTransform_pastur_eq d hz
  have him_prod : 0 ≤ z.im * wt.im := by
    dsimp only [wt]
    rw [im_resolventTransform, ← integral_const_mul]
    exact integral_nonneg fun x ↦ by
      have : z.im * (z.im / ((x - z.re) ^ 2 + z.im ^ 2)) =
          z.im ^ 2 / ((x - z.re) ^ 2 + z.im ^ 2) := by ring
      rw [this]; positivity
  have hζim_ge : |z.im| ≤ |(z + d * wt).im| := by
    have h1 : (z + d * wt).im = z.im + (d : ℝ) * wt.im := by simp
    rw [h1]
    rcases hz.lt_or_gt with hneg | hpos
    · have : wt.im ≤ 0 := nonpos_of_mul_nonneg_right him_prod hneg
      rw [abs_of_neg hneg, abs_of_neg (by nlinarith [d.coe_nonneg])]; nlinarith [d.coe_nonneg]
    · have : 0 ≤ wt.im := nonneg_of_mul_nonneg_right him_prod hpos
      rw [abs_of_pos hpos, abs_of_pos (by nlinarith [d.coe_nonneg])]; nlinarith [d.coe_nonneg]
  have hζ0 : (z + d * wt).im ≠ 0 := abs_pos.1 ((abs_pos.2 hz).trans_le hζim_ge)
  have hwt_norm : ‖wt‖ ≤ |z.im|⁻¹ * ν.real univ := by
    simpa [wt] using norm_resolventTransform_le (μ := ν.pastur t) hz
  have hsub := norm_resolventTransform_sub_le (μ := ν.pastur s) hζ0 hz
  rw [Measure.pastur_real_univ] at hsub
  calc ‖wt - resolventTransform (ν.pastur s) z‖
      = ‖resolventTransform (ν.pastur s) (z + d * wt) - resolventTransform (ν.pastur s) z‖ := by
        rw [← hwt_eq]
    _ ≤ ‖(z + d * wt) - z‖ / (|(z + d * wt).im| * |z.im|) * ν.real univ := hsub
    _ ≤ ((d : ℝ) * (|z.im|⁻¹ * ν.real univ)) / (|z.im| * |z.im|) * ν.real univ := by
        have hnum : ‖(z + d * wt) - z‖ ≤ (d : ℝ) * (|z.im|⁻¹ * ν.real univ) := by
          rw [add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_nonneg d.coe_nonneg]
          exact mul_le_mul_of_nonneg_left hwt_norm d.coe_nonneg
        have : 0 < |z.im| := abs_pos.2 hz
        gcongr
    _ = |(t : ℝ) - s| * |z.im|⁻¹ ^ 3 * ν.real univ ^ 2 := by
        rw [hd_coe]
        have hzpos : |z.im| ≠ 0 := abs_ne_zero.2 hz
        field_simp [hzpos]

/-- Off the real axis, `t ↦ resolventTransform (ν.pastur t) z` is continuous on `ℝ≥0`. -/
@[fun_prop]
theorem continuous_resolventTransform_pastur {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun t : ℝ≥0 ↦ resolventTransform (ν.pastur t) z := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let C : ℝ := |z.im|⁻¹ ^ 3 * ν.real univ ^ 2
  have hlim : Tendsto (fun s : ℝ≥0 ↦ |(s : ℝ) - t| * C) (𝓝 t) (𝓝 0) := by
    have hsub : Tendsto (fun s : ℝ≥0 ↦ (s : ℝ) - t) (𝓝 t) (𝓝 0) := by
      simpa using (NNReal.continuous_coe.tendsto t).sub (tendsto_const_nhds (x := (t : ℝ)))
    simpa using (continuous_abs.tendsto 0 |>.comp hsub).mul (tendsto_const_nhds (x := C))
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun s ↦ by simpa only [C, mul_assoc] using norm_resolventTransform_pastur_sub_le t s hz) hlim

/-- Continuous difference-quotient factorization for a complex-differentiable function `g` at `w`:
there exists `Q : ℂ → ℂ` continuous at `w` with `Q w = d` and `g u - g w = Q u * (u - w)`. -/
private lemma exists_continuousAt_sub_eq_mul_sub {g : ℂ → ℂ} {d w : ℂ}
    (hg : HasDerivAt g d w) :
    ∃ Q : ℂ → ℂ, Q w = d ∧ ContinuousAt Q w ∧ ∀ u : ℂ, g u - g w = Q u * (u - w) := by
  let Q : ℂ → ℂ := fun u ↦ if u = w then d else slope g w u
  refine ⟨Q, by simp [Q], ?_, fun u ↦ ?_⟩
  · rw [ContinuousAt, tendsto_def]
    intro V hV
    have hVd : V ∈ 𝓝 d := by simpa [Q] using hV
    have hev : ∀ᶠ u in 𝓝[≠] w, Q u ∈ V := by
      filter_upwards [(hasDerivAt_iff_tendsto_slope.1 hg).eventually hVd,
        self_mem_nhdsWithin] with u hu (hne : u ≠ w)
      simpa [Q, hne] using hu
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with u hu
    by_cases h : u = w
    · simpa [h] using mem_of_mem_nhds hV
    · exact hu h
  · by_cases h : u = w
    · simp [h]
    · simp [Q, h, slope_def_field, div_mul_cancel₀ _ (sub_ne_zero.2 h)]

/-- **Right time-derivative of the Pastur resolvent transform.** For every finite measure `ν` on
`ℝ`, `z : ℂ` with `z.im ≠ 0`, and `t : ℝ` with `0 ≤ t`, the map
`s ↦ resolventTransform (ν.pastur s.toNNReal) z` has derivative `m_t(z) ∂_z m_t(z)` within `[0, ∞)`
at `t`. -/
theorem hasDerivWithinAt_resolventTransform_pastur_Ici {z : ℂ} (hz : z.im ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ ↦ resolventTransform (ν.pastur s.toNNReal) z)
      (resolventTransform (ν.pastur t.toNNReal) z *
        deriv (resolventTransform (ν.pastur t.toNNReal)) z) (Ici 0) t := by
  let f : ℝ → ℂ := fun s ↦ resolventTransform (ν.pastur s.toNNReal) z
  let ζ : ℝ → ℂ := fun s ↦ z + (s.toNNReal : ℂ) * f s
  let d : ℂ := deriv (resolventTransform ν) (ζ t)
  have hpos := im_mul_im_add_mul_resolventTransform_pastur_pos (ν := ν) t.toNNReal hz
  have hsupp : ζ t ∉ algebraMap ℝ ℂ '' ν.support := by
    rintro ⟨x, -, hx⟩
    have h0 : (ζ t).im = 0 := by simpa using congrArg im hx.symm
    dsimp only [ζ, f] at h0; rw [h0, mul_zero] at hpos; exact lt_irrefl 0 hpos
  have hm_deriv : HasDerivAt (resolventTransform ν) d (ζ t) := by
    have h := hasDerivAt_resolventTransform (ζ t) hsupp; dsimp only [d]; rwa [h.deriv]
  have ht_coe_c : ((t.toNNReal : ℝ) : ℂ) = (t : ℂ) :=
    congrArg Complex.ofReal (Real.coe_toNNReal t ht)
  have hjac : 1 - (t : ℂ) * d ≠ 0 := by
    rw [← ht_coe_c]
    exact one_sub_mul_deriv_resolventTransform_pastur_ne_zero (ν := ν) t.toNNReal hz
  have hderiv_z : deriv (resolventTransform (ν.pastur t.toNNReal)) z = d / (1 - (t : ℂ) * d) := by
    rw [← ht_coe_c]; exact (hasDerivAt_resolventTransform_pastur (ν := ν) t.toNNReal hz).deriv
  obtain ⟨Q, hQd, hQ_cont, hQ_eq⟩ := exists_continuousAt_sub_eq_mul_sub hm_deriv
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
  rw [hasDerivWithinAt_iff_tendsto_slope, hderiv_z, ← mul_div_assoc]
  refine (hnum_lim.div hden_lim hjac).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hden_lim.eventually_ne hjac] with s ⟨hs0, hst⟩ hden
  have hs_coe_c : ((s.toNNReal : ℝ) : ℂ) = (s : ℂ) :=
    congrArg Complex.ofReal (Real.coe_toNNReal s hs0)
  have hdiff_ζ : ζ s - ζ t = (s - t : ℂ) * f s + (t : ℂ) * (f s - f t) := by
    dsimp only [ζ]; rw [hs_coe_c, ht_coe_c]; ring
  have hlin : (1 - (t : ℂ) * Q (ζ s)) * (f s - f t) = (s - t : ℂ) * (f s * Q (ζ s)) := by
    have h1 : f s - f t = Q (ζ s) * ((s - t : ℂ) * f s + (t : ℂ) * (f s - f t)) := by
      rw [← hdiff_ζ]; dsimp only [f]
      rw [resolventTransform_pastur_eq s.toNNReal hz, resolventTransform_pastur_eq t.toNNReal hz]
      exact hQ_eq (ζ s)
    linear_combination h1
  have hst' : (s - t : ℂ) ≠ 0 := by rw [← ofReal_sub, ofReal_ne_zero]; exact sub_ne_zero.2 hst
  rw [Pi.div_apply, slope_def_module, real_smul, ofReal_inv, ofReal_sub, div_eq_iff hden]
  calc f s * Q (ζ s)
      = ((s : ℂ) - t)⁻¹ * ((s - t : ℂ) * (f s * Q (ζ s))) := by field_simp [hst']
    _ = ((s : ℂ) - t)⁻¹ * ((1 - (t : ℂ) * Q (ζ s)) * (f s - f t)) := by rw [← hlin]
    _ = ((s : ℂ) - t)⁻¹ * (f s - f t) * (1 - (t : ℂ) * Q (ζ s)) := by ring

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
  let ζ : ℝ≥0 → ℂ := fun t ↦ z + t * resolventTransform (ν.pastur t) z
  have hζ_cont : Continuous ζ :=
    continuous_const.add ((continuous_ofReal.comp NNReal.continuous_coe).mul
      (continuous_resolventTransform_pastur hz))
  have hH_open : IsOpen {w : ℂ | w.im ≠ 0} := isOpen_compl_singleton.preimage continuous_im
  have hH_sub : {w : ℂ | w.im ≠ 0} ⊆ (algebraMap ℝ ℂ '' ν.support)ᶜ := by
    rintro w (hw : w.im ≠ 0) ⟨x, -, hx⟩
    exact hw (by simpa using congrArg im hx.symm)
  have han : AnalyticOnNhd ℂ (resolventTransform ν) {w : ℂ | w.im ≠ 0} :=
    hH_open.analyticOn_iff_analyticOnNhd.1 (analyticOn_resolventTransform.mono hH_sub)
  have hd_cont : Continuous fun t : ℝ≥0 ↦ deriv (resolventTransform ν) (ζ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hpos := im_mul_im_add_mul_resolventTransform_pastur_pos (ν := ν) t hz
    have hζ0 : (ζ t).im ≠ 0 := fun h ↦ by simp [ζ, h] at hpos
    exact (han (ζ t) hζ0).deriv.continuousAt.comp hζ_cont.continuousAt
  have hden_cont : Continuous fun t : ℝ≥0 ↦
      1 - (t : ℂ) * deriv (resolventTransform ν) (ζ t) :=
    continuous_const.sub ((continuous_ofReal.comp NNReal.continuous_coe).mul hd_cont)
  have eq_fun : (fun t : ℝ≥0 ↦ deriv (resolventTransform (ν.pastur t)) z) =
      fun t : ℝ≥0 ↦ deriv (resolventTransform ν) (ζ t) /
        (1 - (t : ℂ) * deriv (resolventTransform ν) (ζ t)) := by
    ext t
    exact (hasDerivAt_resolventTransform_pastur t hz).deriv
  rw [eq_fun]
  exact hd_cont.div hden_cont fun t ↦ one_sub_mul_deriv_resolventTransform_pastur_ne_zero t hz

/-- The Burgers nonlinearity `s ↦ m_s(z) ∂_z m_s(z)` is interval-integrable on `0..t` for every
`t : ℝ` and `z.im ≠ 0`. -/
theorem intervalIntegrable_resolventTransform_pastur_mul_deriv {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦
      resolventTransform (ν.pastur s.toNNReal) z *
        deriv (resolventTransform (ν.pastur s.toNNReal)) z) volume 0 t := by
  refine Continuous.intervalIntegrable ?_ 0 t
  exact ((continuous_resolventTransform_pastur hz).comp continuous_real_toNNReal).mul
    ((continuous_deriv_resolventTransform_pastur hz).comp continuous_real_toNNReal)

/-- **The Stieltjes–Burgers integral equation.** For every finite Borel measure `ν` on `ℝ`,
`t : ℝ≥0`, and `z : ℂ` with `z.im ≠ 0`,
`m_{ν.pastur t}(z) = m_ν(z) + ∫ s in 0..t, m_{ν.pastur s}(z) ∂_z m_{ν.pastur s}(z)`. -/
theorem resolventTransform_pastur_eq_add_integral (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    resolventTransform (ν.pastur t) z = resolventTransform ν z +
      ∫ s in (0 : ℝ)..t, resolventTransform (ν.pastur s.toNNReal) z *
        deriv (resolventTransform (ν.pastur s.toNNReal)) z := by
  let f : ℝ → ℂ := fun s ↦ resolventTransform (ν.pastur s.toNNReal) z
  let f' : ℝ → ℂ := fun s ↦
    resolventTransform (ν.pastur s.toNNReal) z *
      deriv (resolventTransform (ν.pastur s.toNNReal)) z
  have hcont : ContinuousOn f (Icc 0 t) :=
    ((continuous_resolventTransform_pastur hz).comp continuous_real_toNNReal).continuousOn
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivWithinAt f (f' s) (Ioi s) s :=
    fun s hs ↦ (hasDerivAt_resolventTransform_pastur_time hz hs.1).hasDerivWithinAt
  have hint : IntervalIntegrable f' volume 0 t :=
    intervalIntegrable_resolventTransform_pastur_mul_deriv hz t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg hcont hderiv
    hint
  have hf0 : f 0 = resolventTransform ν z := by simp [f]
  have hft : f t = resolventTransform (ν.pastur t) z := by simp [f]
  dsimp only [f'] at hftc
  rw [hftc, hf0, hft, add_sub_cancel]

end MeasureTheory

end
