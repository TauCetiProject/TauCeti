/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Monotone
public import TauCeti.Analysis.GradientFlow.EVI.Basic
public import TauCeti.Analysis.GradientFlow.MaximalSlope.Basic
import TauCeti.Analysis.ODE.Gronwall

/-!
# EVI solutions are curves of maximal slope

Let `φ : X → EReal` be a lower semicontinuous energy on a metric space and let `u` be an `EVI_λ`
solution for `φ` (`TauCeti.IsEVISolution`). This file shows that `u` is also a gradient flow of `φ`
in the energy-dissipation sense: on `(0, ∞)` it is a `2`-curve of maximal slope for `φ` with
respect to the descending slope `|∂φ|`, and the energy-dissipation inequality is an identity,

`φ (u s) = φ (u t) + (1/2) ∫_s^t |u'|² + (1/2) ∫_s^t |∂φ|²(u)` for `0 < s ≤ t`.

For a general curve of maximal slope this identity needs `|∂φ|` to be a strong upper gradient
(`TauCeti.IsCurveOfMaximalSlope.apply_eq_add_dissipation`); for `EVI_λ` solutions it holds with no
such hypothesis. The results are the regularity of `EVI_λ` solutions at positive times:

* `u` is locally Lipschitz on `(0, ∞)`. By `λ`-contraction, applied to `u` and its time translate
  `u (· + τ)`, the increments `d(u t, u (t + τ))` grow at most like `e^{-λ(t - s)}` in `t ≥ s`. At a
  time `s` where the nonincreasing energy is differentiable, the integrated evolution variational
  inequality tested at `u s` bounds `d(u s, u (s + τ))` by a multiple of `τ`.
* At every positive time the descending slope is at most the metric derivative,
  `|∂φ|(u t) ≤ |u'|(t)`, and in particular it is finite. Testing the evolution variational
  inequality at `y` and bounding the decrease of `d(u ·, y)²` by the speed of `u` gives
  `φ (u t) - φ y ≤ K d(u t, y) - (λ/2) d(u t, y)²` whenever `K` bounds the speed just after `t`.
* At almost every positive time, `|u'|(t) = |∂φ|(u t)` and `d/dt φ (u t) = -|∂φ|²(u t)`. At a time
  where the energy is differentiable and the metric derivative `m` exists, the chain
  `m² ≤ -d/dt φ (u t) ≤ |∂φ|(u t) m ≤ m²` closes up. The first inequality compares
  `d(u σ, u t)² / 2` for `σ` just after `t` with `(-d/dt φ (u t) + ε) (σ - t)² / 2` through the
  evolution variational inequality tested at `u t`; the second is the definition of the descending
  slope; the third is the previous item.

The energy identity follows by integrating the derivative of the energy, which is Lipschitz on
compact subintervals of `(0, ∞)`.

## Main results

* `TauCeti.IsEVISolution.locallyLipschitzOn`: an `EVI_λ` solution is locally Lipschitz on
  `(0, ∞)`.
* `TauCeti.IsEVISolution.descendingSlope_le_metricDerivative` and
  `TauCeti.IsEVISolution.descendingSlope_ne_top`: at positive times the descending slope is at most
  the speed, and finite.
* `TauCeti.IsEVISolution.ae_descendingSlope_eq_metricDerivative` and
  `TauCeti.IsEVISolution.ae_hasDerivAt_toReal`: almost everywhere the speed is the slope and the
  energy decreases at rate the squared slope.
* `TauCeti.IsEVISolution.apply_eq_add_dissipation`: the **energy identity**.
* `TauCeti.IsEVISolution.isCurveOfMaximalSlope`: an `EVI_λ` solution is a curve of maximal slope
  on `(0, ∞)`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapters 1 and 4.
* M. Muratori, G. Savaré, *Gradient flows and evolution variational inequalities in metric
  spaces. I: Structural properties*, J. Funct. Anal. 278 (2020), Section 3.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology Real
open scoped ENNReal NNReal Interval

namespace TauCeti

namespace IsEVISolution

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal} {u : ℝ → X} {s t : ℝ}

/-- The energy at positive times, as a real number. -/
private theorem coe_toReal (h : IsEVISolution lam φ u) (ht : 0 < t) :
    ((φ (u t)).toReal : EReal) = φ (u t) :=
  EReal.coe_toReal (h.apply_ne_top ht) (h.apply_ne_bot ht)

/-- The real energy `t ↦ (φ (u t)).toReal` is nonincreasing on `(0, ∞)`. -/
private theorem antitoneOn_toReal (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) :
    AntitoneOn (fun t ↦ (φ (u t)).toReal) (Ioi 0) := fun _ ha _ hb hab ↦
  EReal.toReal_le_toReal (h.antitoneOn hφ ha hb hab) (h.apply_ne_bot hb) (h.apply_ne_top ha)

/-- A step of length `τ` from a positive time `s` moves at most
`d(u (s + τ), u s)² ≤ 2 e^{2|λ|τ} τ (φ (u s) - φ (u (s + τ)))`. -/
private theorem dist_sq_le (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) (hs : 0 < s)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    dist (u (s + τ)) (u s) ^ 2 ≤
      2 * exp (2 * |lam| * τ) * τ * ((φ (u s)).toReal - (φ (u (s + τ))).toReal) := by
  set Δ := (φ (u s)).toReal - (φ (u (s + τ))).toReal
  have hΔ : 0 ≤ Δ := sub_nonneg.2 <| h.antitoneOn_toReal hφ hs
    (mem_Ioi.2 (add_pos_of_pos_of_nonneg hs hτ)) (le_add_of_nonneg_right hτ)
  have hint := h.exp_mul_dist_sq_sub_le hφ (y := u s) (h.apply_ne_top hs) hs.le
    (le_add_of_nonneg_right hτ) (c := Δ) (by
      rw [← h.coe_toReal hs, ← h.coe_toReal (add_pos_of_pos_of_nonneg hs hτ), ← EReal.coe_sub])
  rw [add_sub_cancel_left, dist_self, zero_pow two_ne_zero, zero_div, sub_zero] at hint
  have hE := integral_exp_mul_le lam hτ
  have hAB : 1 ≤ exp (lam * τ) * exp (|lam| * τ) := by
    rw [← exp_add]
    exact one_le_exp (by nlinarith [neg_abs_le lam])
  have hB2 : exp (2 * |lam| * τ) = exp (|lam| * τ) * exp (|lam| * τ) := by
    rw [← exp_add]
    ring_nf
  rw [hB2]
  nlinarith [mul_le_mul_of_nonneg_right hE hΔ, exp_pos (lam * τ), exp_pos (|lam| * τ),
    sq_nonneg (dist (u (s + τ)) (u s)), mul_nonneg (exp_pos (|lam| * τ)).le hτ]

/-- **Contraction of increments.** For `0 ≤ s ≤ t` and `τ ≥ 0`, the step of length `τ` from time
`t` is at most `e^{-λ(t-s)}` times the step of length `τ` from time `s`. -/
private theorem dist_add_le (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) (hs : 0 ≤ s)
    (hst : s ≤ t) {τ : ℝ} (hτ : 0 ≤ τ) :
    dist (u t) (u (t + τ)) ≤ exp (-(lam * (t - s))) * dist (u s) (u (s + τ)) := by
  have := (h.comp_add_const hs).dist_le (h.comp_add_const (add_nonneg hs hτ)) hφ
    (sub_nonneg.2 hst)
  rwa [sub_add_cancel, show t - s + (s + τ) = t + τ by ring, zero_add, zero_add] at this

/-- At a positive time where the energy is differentiable, the curve moves at most linearly in
time to the right. -/
private theorem exists_dist_le_of_hasDerivAt (h : IsEVISolution lam φ u)
    (hφ : LowerSemicontinuous φ) (hs : 0 < s) {f' : ℝ}
    (hf : HasDerivAt (fun t ↦ (φ (u t)).toReal) f' s) :
    ∃ K δ, 0 ≤ K ∧ 0 < δ ∧ ∀ τ ∈ Ioc 0 δ, dist (u s) (u (s + τ)) ≤ K * τ := by
  set F := fun t ↦ (φ (u t)).toReal
  have hev : ∀ᶠ σ in 𝓝[>] s, f' - 1 < slope F s σ :=
    ((hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsGT_le_nhdsNE s)).eventually
      (lt_mem_nhds (by linarith))
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  set δ := min (b - s) 1
  have hδ : 0 < δ := lt_min (sub_pos.2 hb) one_pos
  set C := 2 * exp (2 * |lam|) * |1 - f'|
  refine ⟨√C, δ, sqrt_nonneg C, hδ, fun τ hτ ↦ ?_⟩
  have hτb : s + τ ∈ Ioc s b := ⟨by linarith [hτ.1], by linarith [hτ.2, min_le_left (b - s) 1]⟩
  have hτ1 : τ ≤ 1 := hτ.2.trans (min_le_right _ _)
  have hsl : f' - 1 < slope F s (s + τ) := hbsub hτb
  rw [slope_def_field, add_sub_cancel_left, lt_div_iff₀ hτ.1] at hsl
  have hd := h.dist_sq_le hφ hs hτ.1.le
  have hexp : exp (2 * |lam| * τ) ≤ exp (2 * |lam|) :=
    exp_le_exp.2 (by nlinarith [abs_nonneg lam])
  -- `d² ≤ C τ²`.
  have hC : dist (u (s + τ)) (u s) ^ 2 ≤ C * τ ^ 2 := by
    refine hd.trans ?_
    have hΔ : F s - F (s + τ) ≤ |1 - f'| * τ := by
      nlinarith [le_abs_self (1 - f'), hτ.1]
    have hΔ0 : 0 ≤ F s - F (s + τ) := sub_nonneg.2 <| h.antitoneOn_toReal hφ hs
      (mem_Ioi.2 (by linarith [hτ.1])) (by linarith [hτ.1])
    have := mul_le_mul hexp hΔ hΔ0 (exp_pos _).le
    calc 2 * exp (2 * |lam| * τ) * τ * (F s - F (s + τ))
        ≤ 2 * exp (2 * |lam|) * τ * (|1 - f'| * τ) := by nlinarith [hτ.1]
      _ = C * τ ^ 2 := by ring
  rw [dist_comm]
  refine (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg (sqrt_nonneg _) hτ.1.le)
    two_ne_zero).1 ?_
  rwa [mul_pow, sq_sqrt (by positivity)]

/-- **EVI solutions are locally Lipschitz at positive times.** An `EVI_λ` solution of a lower
semicontinuous energy is locally Lipschitz on `(0, ∞)`. -/
theorem locallyLipschitzOn (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) :
    LocallyLipschitzOn (Ioi 0) u := by
  intro t₀ (ht₀ : 0 < t₀)
  -- Pick a time `s₀ ∈ (t₀ / 4, t₀ / 2)` at which the nonincreasing energy is differentiable.
  have hmono : MonotoneOn (fun t ↦ -(φ (u t)).toReal) (Ioo (t₀ / 4) (t₀ / 2)) :=
    fun a ha b hb hab ↦ neg_le_neg <| h.antitoneOn_toReal hφ
      (mem_Ioi.2 (lt_trans (by positivity) ha.1)) (mem_Ioi.2 (lt_trans (by positivity) hb.1)) hab
  have hne : (ae (volume.restrict (Ioo (t₀ / 4) (t₀ / 2)))).NeBot := ae_neBot.2 <| by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo]
    simp only [ENNReal.ofReal_eq_zero, not_le]
    linarith
  obtain ⟨s₀, hd, hs₀⟩ :=
    ((hmono.ae_differentiableWithinAt measurableSet_Ioo).and
      (ae_restrict_mem measurableSet_Ioo)).exists
  have hs₀0 : 0 < s₀ := lt_trans (by positivity) hs₀.1
  have hf : HasDerivAt (fun t ↦ (φ (u t)).toReal) (-deriv (fun t ↦ -(φ (u t)).toReal) s₀) s₀ := by
    convert ((hd.differentiableAt (Ioo_mem_nhds hs₀.1 hs₀.2)).hasDerivAt).neg using 1
    funext t
    simp
  obtain ⟨K₀, δ, hK₀, hδ, hstep⟩ := h.exists_dist_le_of_hasDerivAt hφ hs₀0 hf
  -- By contraction of increments, steps of length at most `δ` near `t₀` cost at most `K τ`.
  set ρ := min (δ / 2) (t₀ / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  set K := exp (|lam| * (2 * t₀)) * K₀
  have hK : ∀ x ∈ Ioo (t₀ - ρ) (t₀ + ρ), ∀ y ∈ Ioo (t₀ - ρ) (t₀ + ρ), x ≤ y →
      dist (u x) (u y) ≤ K * dist x y := by
    intro x hx y hy hxy
    have hρ₁ : ρ ≤ δ / 2 := min_le_left _ _
    have hρ₂ : ρ ≤ t₀ / 2 := min_le_right _ _
    rcases hxy.eq_or_lt with rfl | hxy
    · simp
    have hxs : s₀ ≤ x := by linarith [hs₀.2, hx.1]
    have hc := h.dist_add_le hφ hs₀0.le hxs (sub_nonneg.2 hxy.le)
    rw [add_sub_cancel] at hc
    have hτ : y - x ∈ Ioc 0 δ := ⟨sub_pos.2 hxy, by linarith [hx.1, hy.2]⟩
    have hexp : exp (-(lam * (x - s₀))) ≤ exp (|lam| * (2 * t₀)) := exp_le_exp.2 <| by
      nlinarith [neg_abs_le lam, abs_nonneg lam, hx.2, hs₀0]
    rw [Real.dist_eq, abs_of_neg (sub_neg.2 hxy), neg_sub]
    calc dist (u x) (u y) ≤ exp (-(lam * (x - s₀))) * dist (u s₀) (u (s₀ + (y - x))) := hc
      _ ≤ exp (|lam| * (2 * t₀)) * (K₀ * (y - x)) :=
          mul_le_mul hexp (hstep _ hτ) dist_nonneg (exp_pos _).le
      _ = K * (y - x) := by ring
  refine ⟨K.toNNReal, Ioo (t₀ - ρ) (t₀ + ρ),
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)]
  rcases le_total x y with hxy | hyx
  · exact hK x hx y hy hxy
  · rw [dist_comm, dist_comm x]
    exact hK y hy x hx hyx

/-- **The slope inequality.** If the curve moves at most `K (σ - t)` between a positive time `t`
and the times `σ` slightly after it, then the energy at `u t` exceeds that at any `y` by at most
`K d(u t, y) - (λ/2) d(u t, y)²`. -/
private theorem sub_le_of_eventually_dist_le (h : IsEVISolution lam φ u) (ht : 0 < t) {K : ℝ}
    (hK : ∀ᶠ σ in 𝓝[>] t, dist (u σ) (u t) ≤ K * (σ - t)) (y : X) :
    φ (u t) - φ y ≤ ((K * dist (u t) y - lam * (dist (u t) y ^ 2 / 2) : ℝ) : EReal) := by
  rcases eq_or_ne (φ y) ⊤ with hy | hy
  · rw [hy, EReal.sub_top]
    exact bot_le
  set D := dist (u t) y
  -- The difference quotients of `d(u ·, y)² / 2` at `t` are eventually at least `-K D`.
  have hL : ((-(K * D) : ℝ) : EReal) ≤
      limsup (fun σ ↦ ((slope (fun r ↦ dist (u r) y ^ 2 / 2) t σ : ℝ) : EReal)) (𝓝[>] t) := by
    refine le_limsup_of_frequently_le (Eventually.frequently ?_)
    filter_upwards [hK, self_mem_nhdsWithin] with σ hσ (hσt : t < σ)
    rw [EReal.coe_le_coe_iff, slope_def_field, le_div_iff₀ (sub_pos.2 hσt)]
    have h₁ : D ≤ dist (u σ) (u t) + dist (u σ) y := by
      have := dist_triangle (u t) (u σ) y
      rwa [dist_comm (u t) (u σ)] at this
    have hD : 0 ≤ D := dist_nonneg
    have hx : 0 ≤ dist (u σ) y := dist_nonneg
    have he : 0 ≤ dist (u σ) (u t) := dist_nonneg
    -- `d(u σ, y)² - D² ≥ -2 D d(u σ, u t)`.
    have hsq : D ^ 2 - 2 * D * dist (u σ) (u t) ≤ dist (u σ) y ^ 2 := by
      rcases le_total D (dist (u σ) (u t)) with hle | hle
      · nlinarith [mul_le_mul_of_nonneg_left hle hD]
      · have h₂ : D - dist (u σ) (u t) ≤ dist (u σ) y := by linarith
        nlinarith [mul_le_mul h₂ h₂ (sub_nonneg.2 hle) hx]
    nlinarith [mul_le_mul_of_nonneg_left hσ hD]
  have hEVI := (add_le_add hL le_rfl).trans (h.limsup_slope_add_le hy ht)
  rw [← h.coe_toReal ht] at hEVI ⊢
  induction hφy : φ y using EReal.rec with
  | bot =>
    rw [hφy, EReal.bot_sub, ← EReal.coe_add] at hEVI
    exact absurd hEVI (not_le.2 (EReal.bot_lt_coe _))
  | top => exact absurd hφy hy
  | coe q =>
    rw [hφy, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hEVI
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

end PseudoMetricSpace

section MetricSpace

variable {X : Type*} [MetricSpace X] {lam : ℝ} {φ : X → EReal} {u : ℝ → X} {s t : ℝ}

/-- **The descending slope is at most the speed.** At every positive time, the descending slope of
the energy at a point of an `EVI_λ` solution is at most the metric derivative of the curve. -/
theorem descendingSlope_le_metricDerivative (h : IsEVISolution lam φ u) (ht : 0 < t) :
    descendingSlope φ (u t) ≤ metricDerivative u t := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  rcases eq_or_ne c ⊤ with rfl | hctop
  · exact le_top
  obtain ⟨k, hk, hkc⟩ := exists_between hc
  have hktop : k ≠ ⊤ := ne_top_of_lt hkc
  set K := k.toReal
  -- Right after `t`, the curve moves at speed less than `K`.
  rw [metricDerivative_def] at hk
  have hK : ∀ᶠ σ in 𝓝[>] t, dist (u σ) (u t) ≤ K * (σ - t) := by
    filter_upwards [(eventually_lt_of_limsup_lt hk).filter_mono (nhdsGT_le_nhdsNE t),
      self_mem_nhdsWithin] with σ hσ (hσt : t < σ)
    rw [edist_dist, edist_dist, Real.dist_eq, abs_of_pos (sub_pos.2 hσt),
      ← ENNReal.ofReal_div_of_pos (sub_pos.2 hσt), ← ENNReal.ofReal_toReal hktop,
      ENNReal.ofReal_lt_ofReal_iff'] at hσ
    exact ((div_lt_iff₀ (sub_pos.2 hσt)).1 hσ.1).le
  -- Hence near `u t` the energy decreases at rate at most `K + ε < c`.
  have hKc : K < c.toReal := (ENNReal.toReal_lt_toReal hktop hctop).2 hkc
  set ε := c.toReal - K
  have hε : 0 < ε := sub_pos.2 hKc
  refine descendingSlope_le_of_eventually_le ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (u t)
    (div_pos hε (by positivity : (0 : ℝ) < |lam| + 1)))] with y hy
  rw [Metric.mem_ball, dist_comm, lt_div_iff₀ (by positivity)] at hy
  refine (EReal.toENNReal_le_toENNReal (h.sub_le_of_eventually_dist_le ht hK y)).trans ?_
  rw [EReal.real_coe_toENNReal, edist_dist, ← ENNReal.ofReal_toReal hctop,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have hD : 0 ≤ dist (u t) y := dist_nonneg
  have h₁ : |lam| * dist (u t) y ≤ ε := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h₁ hD,
    mul_le_mul_of_nonneg_right (neg_le_abs lam) (sq_nonneg (dist (u t) y))]

/-- The metric derivative of an `EVI_λ` solution of a lower semicontinuous energy is finite at
positive times. -/
private theorem metricDerivative_ne_top (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (ht : 0 < t) : metricDerivative u t ≠ ⊤ := by
  obtain ⟨K, V, hV, hK⟩ := h.locallyLipschitzOn hφ ht
  rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds ht)] at hV
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (hK.metricDerivative_le hV)

/-- **Finite slope at positive times.** Along an `EVI_λ` solution of a lower semicontinuous energy,
the descending slope of the energy is finite at every positive time. -/
theorem descendingSlope_ne_top (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (ht : 0 < t) : descendingSlope φ (u t) ≠ ⊤ :=
  ne_top_of_le_ne_top (h.metricDerivative_ne_top hφ ht) (h.descendingSlope_le_metricDerivative ht)

/-- **The speed is at most the dissipation rate.** At a positive time `s`, if the right difference
quotients of the curve tend to `m` and the rates of decrease of the energy tend to `D`, then
`m² ≤ D`: the evolution variational inequality tested at `u s` bounds `d(u σ, u s)² / 2` by
`(D + ε) (σ - s)² / 2` for `σ` just after `s`. -/
private theorem sq_le_of_tendsto (h : IsEVISolution lam φ u) (hs : 0 < s) {m D : ℝ}
    (hQ : Tendsto (fun σ ↦ dist (u σ) (u s) / (σ - s)) (𝓝[>] s) (𝓝 m))
    (hD : Tendsto (fun σ ↦ ((φ (u s)).toReal - (φ (u σ)).toReal) / (σ - s)) (𝓝[>] s) (𝓝 D)) :
    m ^ 2 ≤ D := by
  set F := fun t ↦ (φ (u t)).toReal
  have hm0 : 0 ≤ m := ge_of_tendsto hQ <| by
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : s < σ)
    exact div_nonneg dist_nonneg (sub_pos.2 hσ).le
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1
    ((hD.eventually (gt_mem_nhds (show D < D + ε / 2 by linarith))).and
      (hQ.eventually (gt_mem_nhds (show m < m + 1 by linarith))))
  set δ := min (b - s) (ε / ((|lam| + 1) * (m + 1) ^ 2))
  have hδ : 0 < δ := lt_min (sub_pos.2 hb) (by positivity)
  have hδε : (|lam| + 1) * (m + 1) ^ 2 * δ ≤ ε := by
    have := min_le_right (b - s) (ε / ((|lam| + 1) * (m + 1) ^ 2))
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  have hδb : δ ≤ b - s := min_le_left _ _
  have hbd : ∀ σ ∈ Ioc s (s + δ), F s - F σ ≤ (D + ε / 2) * (σ - s) ∧
      dist (u σ) (u s) ≤ (m + 1) * (σ - s) := by
    intro σ hσ
    obtain ⟨h₁, h₂⟩ := hbsub ⟨hσ.1, by linarith [hσ.2]⟩
    have hσs := sub_pos.2 hσ.1
    exact ⟨((div_lt_iff₀ hσs).1 h₁).le, ((div_lt_iff₀ hσs).1 h₂).le⟩
  have hcu : ContinuousOn u (Icc s (s + δ)) :=
    h.continuousOn.mono fun x hx ↦ mem_Ici.2 (hs.le.trans hx.1)
  have hcmp := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun σ ↦ dist (u σ) (u s) ^ 2 / 2) (a := s) (b := s + δ)
    (B := fun σ ↦ (D + ε) * (σ - s) ^ 2 / 2) (B' := fun σ ↦ (D + ε) * (σ - s))
    (fun x hx ↦ (((hcu x hx).dist (tendsto_const_nhds (x := u s))).pow 2).div_const 2) (by simp)
    (by fun_prop)
    (fun x _ ↦ by
      have hsq : HasDerivAt (fun σ ↦ (σ - s) ^ 2) (2 * (x - s)) x := by
        simpa using ((hasDerivAt_id x).sub_const s).fun_pow 2
      exact ((hsq.const_mul (D + ε)).div_const 2).congr_deriv (by ring) |>.hasDerivWithinAt) ?_
  · refine le_of_tendsto (hQ.pow 2) ?_
    filter_upwards [Ioo_mem_nhdsGT (show s < s + δ by linarith)] with σ hσ
    have hσs := sub_pos.2 hσ.1
    have := hcmp ⟨hσ.1.le, hσ.2.le⟩
    rw [div_pow, div_le_iff₀ (pow_pos hσs 2)]
    linarith
  · -- The evolution variational inequality at `x`, tested at `u s`.
    intro x hx r hr
    rcases eq_or_lt_of_le hx.1 with rfl | hsx
    · refine (h.eventually_slope_lt (y := u s) (h.apply_ne_top hs) hs (c := 0) ?_ ?_).frequently
      · rw [← h.coe_toReal hs, ← EReal.coe_sub, sub_self, EReal.coe_zero]
      · simpa using hr
    · have hx0 : 0 < x := hs.trans hsx
      obtain ⟨h₁, h₂⟩ := hbd x ⟨hsx, hx.2.le⟩
      refine (h.eventually_slope_lt (y := u s) (h.apply_ne_top hs) hx0 (c := F s - F x) ?_
        ?_).frequently
      · rw [← h.coe_toReal hs, ← h.coe_toReal hx0, ← EReal.coe_sub]
      · have hxs := sub_pos.2 hsx
        have hd2 : dist (u x) (u s) ^ 2 ≤ ((m + 1) * (x - s)) ^ 2 :=
          pow_le_pow_left₀ dist_nonneg h₂ 2
        have hxδ : x - s ≤ δ := by linarith [hx.2]
        have h₃ : |lam| * ((m + 1) ^ 2 * (x - s)) ≤ ε := by
          have := mul_le_mul_of_nonneg_left hxδ (by positivity : (0 : ℝ) ≤ (m + 1) ^ 2)
          nlinarith [abs_nonneg lam]
        have h₄ : -lam * (dist (u x) (u s) ^ 2 / 2) ≤ ε / 2 * (x - s) := by
          nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs lam) (sq_nonneg (dist (u x) (u s))),
            mul_le_mul_of_nonneg_left hd2 (abs_nonneg lam)]
        linarith

/-- **The dissipation rate is at most slope times speed.** At a positive time `s` with finite
descending slope, if the right difference quotients of the curve tend to `m` and the rates of
decrease of the energy tend to `D`, then `D ≤ |∂φ|(u s) m`. -/
private theorem le_toReal_mul_of_tendsto (h : IsEVISolution lam φ u) (hs : 0 < s)
    (hGtop : descendingSlope φ (u s) ≠ ⊤) {m D : ℝ}
    (hQ : Tendsto (fun σ ↦ dist (u σ) (u s) / (σ - s)) (𝓝[>] s) (𝓝 m))
    (hD : Tendsto (fun σ ↦ ((φ (u s)).toReal - (φ (u σ)).toReal) / (σ - s)) (𝓝[>] s) (𝓝 D)) :
    D ≤ (descendingSlope φ (u s)).toReal * m := by
  set G := (descendingSlope φ (u s)).toReal
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ m := ge_of_tendsto hQ <| by
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : s < σ)
    exact div_nonneg dist_nonneg (sub_pos.2 hσ).le
  have key : ∀ ε > 0, D ≤ (G + ε) * (m + ε) := by
    intro ε hε
    have hsl : ∀ᶠ y in 𝓝[≠] (u s),
        (φ (u s) - φ y).toENNReal / edist (u s) y < ENNReal.ofReal (G + ε) := by
      refine eventually_lt_of_limsup_lt ?_
      rw [← descendingSlope_def, ← ENNReal.ofReal_toReal hGtop]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    have hcont : Tendsto u (𝓝[>] s) (𝓝 (u s)) :=
      (h.continuousOn.continuousAt (Ici_mem_nhds hs)).tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hD ?_
    filter_upwards [hcont.eventually (eventually_nhdsWithin_iff.1 hsl),
      hQ.eventually (gt_mem_nhds (show m < m + ε by linarith)), self_mem_nhdsWithin]
      with σ h₁ h₂ (hσ : s < σ)
    have hσs := sub_pos.2 hσ
    have hσ0 : 0 < σ := hs.trans hσ
    have hd : dist (u s) (u σ) ≤ (m + ε) * (σ - s) := by
      rw [dist_comm]
      exact ((div_lt_iff₀ hσs).1 h₂).le
    rw [div_le_iff₀ hσs]
    by_cases hus : u σ = u s
    · simp only [hus, sub_self]
      positivity
    · have h₃ := h₁ hus
      rw [← h.coe_toReal hs, ← h.coe_toReal hσ0, ← EReal.coe_sub, EReal.real_coe_toENNReal,
        edist_dist, ENNReal.div_lt_iff (.inl (by simpa using Ne.symm hus))
          (.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul (by positivity)] at h₃
      have h₄ := (ENNReal.ofReal_lt_ofReal_iff'.1 h₃).1
      nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ G + ε)]
  have hT : Tendsto (fun ε ↦ (G + ε) * (m + ε)) (𝓝[>] 0) (𝓝 (G * m)) := by
    have : Continuous fun ε : ℝ ↦ (G + ε) * (m + ε) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε ↦ key ε hε)

/-- At a positive time `s` where the energy has derivative `f'` and the difference quotients of the
curve converge to a finite metric derivative `m`, the descending slope is `m` and `f' = -m²`. -/
private theorem descendingSlope_eq_and_eq_neg_sq (h : IsEVISolution lam φ u) (hs : 0 < s)
    {f' : ℝ} (hf : HasDerivAt (fun t ↦ (φ (u t)).toReal) f' s)
    (hm : Tendsto (fun σ ↦ edist (u σ) (u s) / edist σ s) (𝓝[≠] s) (𝓝 (metricDerivative u s)))
    (hmtop : metricDerivative u s ≠ ⊤) :
    descendingSlope φ (u s) = metricDerivative u s ∧ f' = -(metricDerivative u s).toReal ^ 2 := by
  set m := (metricDerivative u s).toReal
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hGm := h.descendingSlope_le_metricDerivative hs
  have hGtop : descendingSlope φ (u s) ≠ ⊤ := ne_top_of_le_ne_top hmtop hGm
  set G := (descendingSlope φ (u s)).toReal
  have hGm' : G ≤ m := ENNReal.toReal_mono hmtop hGm
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  -- The right difference quotients of the curve and of the energy.
  have hQ : Tendsto (fun σ ↦ dist (u σ) (u s) / (σ - s)) (𝓝[>] s) (𝓝 m) := by
    refine ((ENNReal.tendsto_toReal hmtop).comp (hm.mono_left (nhdsGT_le_nhdsNE s))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : s < σ)
    rw [Function.comp_apply, edist_dist, edist_dist, Real.dist_eq, abs_of_pos (sub_pos.2 hσ),
      ENNReal.toReal_div, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal (sub_pos.2 hσ).le]
  have hD : Tendsto (fun σ ↦ ((φ (u s)).toReal - (φ (u σ)).toReal) / (σ - s)) (𝓝[>] s)
      (𝓝 (-f')) := by
    refine ((hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsGT_le_nhdsNE s)).neg.congr' ?_
    filter_upwards with σ
    rw [slope_def_field, ← neg_div, neg_sub]
  have hi := h.sq_le_of_tendsto hs hQ hD
  have hii := h.le_toReal_mul_of_tendsto hs hGtop hQ hD
  -- Together with `G ≤ m`, the chain `m² ≤ -f' ≤ G m ≤ m²` forces `G = m` and `-f' = m²`.
  have hGeq : G = m := by
    rcases hm0.eq_or_lt with hm | hm
    · linarith
    · exact le_antisymm hGm' (le_of_mul_le_mul_right (by nlinarith) hm)
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_toReal hGtop, ← ENNReal.ofReal_toReal hmtop]
    exact congrArg ENNReal.ofReal hGeq
  · nlinarith

/-- Between two positive times `s ≤ t`, an `EVI_λ` solution of a lower semicontinuous energy and its
energy are absolutely continuous, and at almost every time the speed is finite, equals the
descending slope, and is the square root of the rate of decrease of the energy. -/
private theorem absolutelyContinuousOnInterval_and_ae (h : IsEVISolution lam φ u)
    (hφ : LowerSemicontinuous φ) (hs : 0 < s) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval u s t ∧
      AbsolutelyContinuousOnInterval (fun r ↦ (φ (u r)).toReal) s t ∧
      ∀ᵐ r, r ∈ uIcc s t → metricDerivative u r ≠ ⊤ ∧
        descendingSlope φ (u r) = metricDerivative u r ∧
        HasDerivAt (fun r ↦ (φ (u r)).toReal) (-(metricDerivative u r).toReal ^ 2) r := by
  set F := fun r ↦ (φ (u r)).toReal
  obtain ⟨K, hK⟩ := ((h.locallyLipschitzOn hφ).mono fun r (hr : r ∈ Icc s (t + 1)) ↦
    mem_Ioi.2 (hs.trans_le hr.1)).exists_lipschitzOnWith_of_compact isCompact_Icc
  have huAC : AbsolutelyContinuousOnInterval u s t :=
    LipschitzOnWith.absolutelyContinuousOnInterval
      (hK.mono (by rw [uIcc_of_le hst]; exact Icc_subset_Icc_right (by linarith)))
  -- Right after each time of `[s, t]` the curve moves at speed at most `K`.
  have hspeed : ∀ r ∈ Icc s t, ∀ᶠ σ in 𝓝[>] r, dist (u σ) (u r) ≤ K * (σ - r) := fun r hr ↦ by
    filter_upwards [Ioo_mem_nhdsGT (show r < t + 1 by linarith [hr.2])] with σ hσ
    have := hK.dist_le_mul σ ⟨by linarith [hr.1, hσ.1], hσ.2.le⟩ r ⟨hr.1, by linarith [hr.2]⟩
    rwa [Real.dist_eq, abs_of_pos (sub_pos.2 hσ.1)] at this
  -- Hence, by the slope inequality, the energy is Lipschitz on `[s, t]`.
  set L := (K : ℝ) ^ 2 * (1 + |lam| * (t - s) / 2) with hL
  have hFL : ∀ x ∈ Icc s t, ∀ y ∈ Icc s t, x ≤ y → dist (F x) (F y) ≤ L * dist x y := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hs.trans_le hx.1
    have hy0 : 0 < y := hs.trans_le hy.1
    have h₁ := h.sub_le_of_eventually_dist_le hx0 (hspeed x hx) (u y)
    rw [← h.coe_toReal hx0, ← h.coe_toReal hy0, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h₁
    have h₂ : F y ≤ F x := h.antitoneOn_toReal hφ hx0 hy0 hxy
    have hd : dist (u x) (u y) ≤ K * (y - x) := by
      have := hK.dist_le_mul x ⟨hx.1, by linarith [hx.2]⟩ y ⟨hy.1, by linarith [hy.2]⟩
      rwa [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxy), neg_sub] at this
    have hK0 : (0 : ℝ) ≤ K := K.2
    have hyx : y - x ≤ t - s := by linarith [hx.1, hy.2]
    have hd2 : dist (u x) (u y) ^ 2 ≤ (K * (y - x)) ^ 2 := pow_le_pow_left₀ dist_nonneg hd 2
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 h₂),
      abs_of_nonpos (sub_nonpos.2 hxy), neg_sub]
    calc F x - F y ≤ K * dist (u x) (u y) - lam * (dist (u x) (u y) ^ 2 / 2) := h₁
      _ ≤ K * (K * (y - x)) + |lam| * ((K * (y - x)) ^ 2 / 2) := by
          linarith [mul_le_mul_of_nonneg_left hd hK0,
            mul_le_mul_of_nonneg_left hd2 (abs_nonneg lam),
            mul_le_mul_of_nonneg_right (neg_le_abs lam) (sq_nonneg (dist (u x) (u y)))]
      _ ≤ L * (y - x) := by
          have := mul_le_mul_of_nonneg_left hyx
            (by positivity : (0 : ℝ) ≤ K ^ 2 * |lam| * (y - x) / 2)
          rw [hL]
          linarith
  have hFAC : AbsolutelyContinuousOnInterval F s t := by
    refine LipschitzOnWith.absolutelyContinuousOnInterval (K := L.toNNReal) ?_
    rw [uIcc_of_le hst]
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    rcases le_total x y with hxy | hyx
    · exact hFL x hx y hy hxy
    · rw [dist_comm, dist_comm x]
      exact hFL y hy x hx hyx
  refine ⟨huAC, hFAC, ?_⟩
  filter_upwards [hFAC.ae_differentiableAt, huAC.ae_tendsto_metricDerivative] with r h₁ h₂ hr
  have hr0 : 0 < r := hs.trans_le (by rw [uIcc_of_le hst] at hr; exact hr.1)
  have hmtop := h.metricDerivative_ne_top hφ hr0
  obtain ⟨h₃, h₄⟩ := h.descendingSlope_eq_and_eq_neg_sq hr0 (h₁ hr).hasDerivAt (h₂ hr) hmtop
  exact ⟨hmtop, h₃, h₄ ▸ (h₁ hr).hasDerivAt⟩

/-- **The energy identity for `EVI_λ` solutions.** Along an `EVI_λ` solution `u` of a lower
semicontinuous energy, between positive times `s ≤ t` the energy drops by exactly the quadratic
dissipation `(1/2) ∫_s^t |u'|² + (1/2) ∫_s^t |∂φ|²(u)`:

`φ (u s) = φ (u t) + dissipation 2 2 (descendingSlope φ) u s t`.

No strong upper gradient hypothesis is needed: the identity is forced by the evolution variational
inequality itself. -/
theorem apply_eq_add_dissipation (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (hs : 0 < s) (hst : s ≤ t) :
    φ (u s) = φ (u t) + dissipation 2 2 (descendingSlope φ) u s t := by
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨huAC, hFAC, hae⟩ := h.absolutelyContinuousOnInterval_and_ae hφ hs hst
  set F := fun r ↦ (φ (u r)).toReal
  have hderiv : ∀ᵐ r, r ∈ uIcc s t → deriv F r = -(metricDerivative u r).toReal ^ 2 := by
    filter_upwards [hae] with r hr hrI using (hr hrI).2.2.deriv
  -- The dissipation is the integral of the rate of decrease of the energy.
  have hdiss : dissipation 2 2 (descendingSlope φ) u s t = ENNReal.ofReal (F s - F t) := by
    have hFTC : F s - F t = ∫ r in s..t, -deriv F r := by
      rw [intervalIntegral.integral_neg, hFAC.integral_deriv_eq_sub]
      ring
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc s t)] fun r ↦ -deriv F r := by
      rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hderiv] with r hr hrI
      rw [Pi.zero_apply, hr (by rw [uIcc_of_le hst]; exact Ioc_subset_Icc_self hrI), neg_neg]
      positivity
    rw [huAC.dissipation_eq_lintegral Real.HolderConjugate.two_two, hFTC,
      intervalIntegral.integral_of_le hst,
      ofReal_integral_eq_lintegral_ofReal (f := fun r ↦ -deriv F r)
        hFAC.intervalIntegrable_deriv.neg.1 hnonneg,
      ← uIoc_of_le hst]
    refine setLIntegral_congr_fun_ae measurableSet_uIoc ?_
    filter_upwards [hae] with r hr hrI
    obtain ⟨hmtop, hsl, hder⟩ := hr (uIoc_subset_uIcc hrI)
    rw [hsl, Real.HolderConjugate.two_two.div_add_div_ennreal, hder.deriv, neg_neg,
      ← ENNReal.ofReal_toReal hmtop,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg zero_le_two,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    norm_cast
  rw [hdiss, ← h.coe_toReal hs, ← h.coe_toReal ht, EReal.coe_ennreal_ofReal,
    max_eq_left (sub_nonneg.2 (h.antitoneOn_toReal hφ hs ht hst)), ← EReal.coe_add, add_sub_cancel]

/-- **`EVI_λ` solutions are curves of maximal slope.** An `EVI_λ` solution of a lower
semicontinuous energy is, on `(0, ∞)`, a `2`-curve of maximal slope for the energy with respect to
its descending slope. -/
theorem isCurveOfMaximalSlope (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) :
    IsCurveOfMaximalSlope 2 2 φ (descendingSlope φ) u (Ioi 0) :=
  isCurveOfMaximalSlope_iff.2 ⟨fun _ hs ↦ ⟨h.apply_ne_top hs, h.apply_ne_bot hs⟩, fun _ hs _ _ hst ↦
    ⟨(h.absolutelyContinuousOnInterval_and_ae hφ hs hst).1,
      (h.apply_eq_add_dissipation hφ hs hst).ge⟩⟩

/-- At almost every positive time, the speed of an `EVI_λ` solution equals the descending slope
and the energy decreases at rate the squared slope. -/
private theorem ae_descendingSlope_eq_and_hasDerivAt (h : IsEVISolution lam φ u)
    (hφ : LowerSemicontinuous φ) :
    ∀ᵐ t, 0 < t → descendingSlope φ (u t) = metricDerivative u t ∧
      HasDerivAt (fun t ↦ (φ (u t)).toReal) (-(descendingSlope φ (u t)).toReal ^ 2) t := by
  have hn : ∀ n : ℕ, ∀ᵐ t, t ∈ Icc ((n : ℝ) + 1)⁻¹ (n + 1) →
      descendingSlope φ (u t) = metricDerivative u t ∧
        HasDerivAt (fun t ↦ (φ (u t)).toReal) (-(descendingSlope φ (u t)).toReal ^ 2) t := by
    intro n
    have hle : ((n : ℝ) + 1)⁻¹ ≤ n + 1 :=
      (inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])).trans
        (by linarith [n.cast_nonneg (α := ℝ)])
    filter_upwards [(h.absolutelyContinuousOnInterval_and_ae hφ (by positivity) hle).2.2]
      with t ht htI
    obtain ⟨-, h₁, h₂⟩ := ht (by rwa [uIcc_of_le hle])
    exact ⟨h₁, h₁ ▸ h₂⟩
  filter_upwards [ae_all_iff.2 hn] with t ht ht0
  obtain ⟨n, hn⟩ := exists_nat_ge (max t t⁻¹)
  refine ht n ⟨inv_le_of_inv_le₀ ht0 ?_, ?_⟩ <;> linarith [le_max_left t t⁻¹, le_max_right t t⁻¹]

/-- **Speed equals slope.** At almost every positive time, the metric derivative of an `EVI_λ`
solution of a lower semicontinuous energy equals the descending slope of the energy. -/
theorem ae_descendingSlope_eq_metricDerivative (h : IsEVISolution lam φ u)
    (hφ : LowerSemicontinuous φ) :
    ∀ᵐ t, 0 < t → descendingSlope φ (u t) = metricDerivative u t := by
  filter_upwards [h.ae_descendingSlope_eq_and_hasDerivAt hφ] with t ht ht0 using (ht ht0).1

/-- **The energy identity in differential form.** At almost every positive time, the energy along
an `EVI_λ` solution of a lower semicontinuous energy is differentiable with derivative minus the
squared descending slope: `d/dt φ (u t) = -|∂φ|²(u t)`. -/
theorem ae_hasDerivAt_toReal (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) :
    ∀ᵐ t, 0 < t →
      HasDerivAt (fun t ↦ (φ (u t)).toReal) (-(descendingSlope φ (u t)).toReal ^ 2) t := by
  filter_upwards [h.ae_descendingSlope_eq_and_hasDerivAt hφ] with t ht ht0 using (ht ht0).2

end MetricSpace

end IsEVISolution

end TauCeti
