/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `Lᵖ` seminorms on all balls of one radius

For an additive Haar measure `μ` on a proper normed additive group, the balls `B(y, r)` of a fixed
radius cover every point equally often when `y` runs over the whole space: by Tonelli's theorem,

`∫⁻ y, ∫⁻ x in B(y, r), G x ∂μ ∂μ = μ (B(0, r)) * ∫⁻ x, G x ∂μ`.

Applied to `G = ‖g‖ₑ ^ p`, the `p`-th powers of the `Lᵖ` seminorms of `g` on the balls of radius `r`
integrate to `μ (B(0, r))` times the `p`-th power of its `Lᵖ` seminorm. Consequently a local
estimate `‖g‖_{Lᵖ(B(y, r))} ≤ ‖h‖_{Lᵖ(B(y, R))}` holding at (almost) every centre `y` becomes the
global estimate

`‖g‖_{Lᵖ} ≤ (μ (B(0, R)) / μ (B(0, r))) ^ (1 / p) ‖h‖_{Lᵖ}`.

On a finite-dimensional real normed space of dimension `d` the volume ratio for `R = 2 r` is
`2 ^ d`. In this setting, local estimates of the form
`‖g‖_{Lᵖ(B(y, r))} ≤ c₁ ‖f₁‖_{Lᵖ(B(y, 2r))} + c₂ ‖f₂‖_{Lᵖ(B(y, 2r))}` at almost every centre give
`‖g‖_{Lᵖ} ≤ 2 ^ (d + 1) (c₁ ‖f₁‖_{Lᵖ} + c₂ ‖f₂‖_{Lᵖ})`, with a constant independent of `r`.

This is how interior estimates on balls with constants independent of the centre, such as the
Calderón–Zygmund estimates for elliptic equations, pass to estimates on the whole space. It
replaces a covering of the space by balls with bounded overlap: averaging over all centres is an
exact form of the bounded-overlap count.

## Main declarations

* `TauCeti.lintegral_setLIntegral_ball`: the Tonelli identity above.
* `TauCeti.lintegral_eLpNorm_restrict_ball_rpow`: its form for `Lᵖ` seminorms.
* `TauCeti.eLpNorm_le_of_ae_eLpNorm_restrict_ball_le`: local estimates on balls of one radius give
  a global estimate.
* `TauCeti.lpNorm_le_of_ae_lpNorm_restrict_ball_le_add`: the same for local estimates by two
  functions on concentric balls of radii `r` and `2 r`, with the explicit constant `2 ^ (d + 1)`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Integrating the integrals of `G` over the balls `B(y, r)` against `μ (dy)` gives
`μ (B(0, r))` times the integral of `G`: every point lies in the balls whose centres form a ball of
the same radius around it. -/
theorem lintegral_setLIntegral_ball {G : E → ℝ≥0∞} (hG : AEMeasurable G μ) (r : ℝ) :
    ∫⁻ y, ∫⁻ x in ball y r, G x ∂μ ∂μ = μ (ball (0 : E) r) * ∫⁻ x, G x ∂μ := by
  have hS : MeasurableSet {z : E × E | dist z.2 z.1 < r} :=
    measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const
  have hjoint : AEMeasurable (Function.uncurry fun y x => (ball y r).indicator G x)
      (μ.prod μ) := by
    have : (Function.uncurry fun y x => (ball y r).indicator G x) =
        {z : E × E | dist z.2 z.1 < r}.indicator fun z => G z.2 := by
      ext ⟨y, x⟩
      simp only [Function.uncurry_apply_pair, Set.indicator, mem_ball, Set.mem_ofPred_eq]
    rw [this]
    exact (hG.comp_snd (μ := μ)).indicator hS
  calc ∫⁻ y, ∫⁻ x in ball y r, G x ∂μ ∂μ
      = ∫⁻ y, ∫⁻ x, (ball y r).indicator G x ∂μ ∂μ := by
        simp_rw [lintegral_indicator measurableSet_ball]
    _ = ∫⁻ x, ∫⁻ y, (ball y r).indicator G x ∂μ ∂μ := lintegral_lintegral_swap hjoint
    _ = ∫⁻ x, μ (ball (0 : E) r) * G x ∂μ := by
        refine lintegral_congr fun x => ?_
        have : (fun y => (ball y r).indicator G x) = (ball x r).indicator fun _ => G x := by
          ext y
          by_cases hxy : x ∈ ball y r
          · rw [Set.indicator_of_mem hxy, Set.indicator_of_mem (mem_ball_comm.1 hxy)]
          · rw [Set.indicator_of_notMem hxy,
              Set.indicator_of_notMem fun h => hxy (mem_ball_comm.1 h)]
        rw [this, lintegral_indicator_const measurableSet_ball, Measure.addHaar_ball_center,
          mul_comm]
    _ = μ (ball (0 : E) r) * ∫⁻ x, G x ∂μ :=
        lintegral_const_mul' _ _ measure_ball_lt_top.ne

variable {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- The `p`-th powers of the `Lᵖ` seminorms of `g` on the balls `B(y, r)` integrate, against
`μ (dy)`, to `μ (B(0, r))` times the `p`-th power of the `Lᵖ` seminorm of `g`. -/
theorem lintegral_eLpNorm_restrict_ball_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : E → F}
    (hg : AEStronglyMeasurable g μ) (r : ℝ) :
    ∫⁻ y, eLpNorm g p (μ.restrict (ball y r)) ^ p.toReal ∂μ =
      μ (ball (0 : E) r) * eLpNorm g p μ ^ p.toReal := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hpow : ∀ ν : Measure E, AEStronglyMeasurable g ν →
      eLpNorm g p ν ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂ν := fun ν hν => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hν, ← ENNReal.rpow_mul,
      one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  simp_rw [hpow _ hg.restrict, hpow μ hg]
  exact lintegral_setLIntegral_ball (hg.enorm.pow_const _) r

/-- **Global estimates from local ones on balls of one radius.** If `0 < r` and, for almost every
centre `y`, the `Lᵖ` seminorm of `g` on `B(y, r)` is at most that of `h` on `B(y, R)`, then

`‖g‖_{Lᵖ} ≤ (μ (B(0, R)) / μ (B(0, r))) ^ (1 / p) ‖h‖_{Lᵖ}`. -/
theorem eLpNorm_le_of_ae_eLpNorm_restrict_ball_le (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {G : Type*} [NormedAddCommGroup G] {g : E → F} {h : E → G} (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) {r R : ℝ} (hr : 0 < r)
    (hle : ∀ᵐ y ∂μ, eLpNorm g p (μ.restrict (ball y r)) ≤ eLpNorm h p (μ.restrict (ball y R))) :
    eLpNorm g p μ ≤ (μ (ball (0 : E) R) / μ (ball (0 : E) r)) ^ p.toReal⁻¹ * eLpNorm h p μ := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hr0 : μ (ball (0 : E) r) ≠ 0 := (measure_ball_pos μ 0 hr).ne'
  have hrtop : μ (ball (0 : E) r) ≠ ∞ := measure_ball_lt_top.ne
  -- Integrate the `p`-th power of the local estimate over all centres.
  have hint : μ (ball (0 : E) r) * eLpNorm g p μ ^ p.toReal ≤
      μ (ball (0 : E) R) * eLpNorm h p μ ^ p.toReal := by
    rw [← lintegral_eLpNorm_restrict_ball_rpow hp0 hp hg,
      ← lintegral_eLpNorm_restrict_ball_rpow hp0 hp hh]
    exact lintegral_mono_ae (hle.mono fun y hy => ENNReal.rpow_le_rpow hy hq.le)
  have hdiv : eLpNorm g p μ ^ p.toReal ≤
      μ (ball (0 : E) R) / μ (ball (0 : E) r) * eLpNorm h p μ ^ p.toReal := by
    calc eLpNorm g p μ ^ p.toReal
        = (μ (ball (0 : E) r))⁻¹ * (μ (ball (0 : E) r) * eLpNorm g p μ ^ p.toReal) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hr0 hrtop, one_mul]
      _ ≤ (μ (ball (0 : E) r))⁻¹ * (μ (ball (0 : E) R) * eLpNorm h p μ ^ p.toReal) := by
          gcongr
      _ = _ := by rw [ENNReal.div_eq_inv_mul, mul_assoc]
  calc eLpNorm g p μ = (eLpNorm g p μ ^ p.toReal) ^ p.toReal⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]
    _ ≤ (μ (ball (0 : E) R) / μ (ball (0 : E) r) * eLpNorm h p μ ^ p.toReal) ^ p.toReal⁻¹ :=
        ENNReal.rpow_le_rpow hdiv (inv_nonneg.2 hq.le)
    _ = (μ (ball (0 : E) R) / μ (ball (0 : E) r)) ^ p.toReal⁻¹ * eLpNorm h p μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq.le), ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]

section FiniteDimensional

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G₁ G₂ : Type*} [NormedAddCommGroup G₁]
  [NormedAddCommGroup G₂]

/-- **Global estimates from local ones on concentric balls.** Let `μ` be an additive Haar measure
on a finite-dimensional real normed space `E`, let `1 ≤ p < ∞`, and let `g`, `f₁`, `f₂` be in
`Lᵖ(μ)`. If `0 < r`, `0 ≤ c₁`, `0 ≤ c₂` and, at almost every centre `y`,

`‖g‖_{Lᵖ(B(y, r))} ≤ c₁ ‖f₁‖_{Lᵖ(B(y, 2r))} + c₂ ‖f₂‖_{Lᵖ(B(y, 2r))}`,

then `‖g‖_{Lᵖ} ≤ 2 ^ (dim E + 1) (c₁ ‖f₁‖_{Lᵖ} + c₂ ‖f₂‖_{Lᵖ})`. The constant does not depend
on `r`. -/
theorem lpNorm_le_of_ae_lpNorm_restrict_ball_le_add (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g : E → F}
    {f₁ : E → G₁} {f₂ : E → G₂} (hg : MemLp g p μ) (hf₁ : MemLp f₁ p μ) (hf₂ : MemLp f₂ p μ)
    {c₁ c₂ r : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hr : 0 < r)
    (hle : ∀ᵐ y ∂μ, lpNorm g p (μ.restrict (ball y r)) ≤
      c₁ * lpNorm f₁ p (μ.restrict (ball y (2 * r))) +
        c₂ * lpNorm f₂ p (μ.restrict (ball y (2 * r)))) :
    lpNorm g p μ ≤ 2 ^ (finrank ℝ E + 1) * (c₁ * lpNorm f₁ p μ + c₂ * lpNorm f₂ p μ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  -- Both terms of each local bound are dominated by the local norm of one function `h`.
  set h : E → ℝ := fun x => c₁ * ‖f₁ x‖ + c₂ * ‖f₂ x‖ with h_def
  have hh : MemLp h p μ := (hf₁.norm.const_mul c₁).add (hf₂.norm.const_mul c₂)
  have hsmul : ∀ (ν : Measure E) {c : ℝ}, 0 ≤ c → ∀ k : E → ℝ, (∀ x, c * |k x| ≤ h x) →
      MemLp h p ν → c * lpNorm k p ν ≤ lpNorm h p ν := fun ν c hc k hk hhν => by
    have e := lpNorm_const_smul c k ν (p := p)
    rw [coe_nnnorm, Real.norm_of_nonneg hc] at e
    rw [← e]
    refine lpNorm_mono_real hhν fun x => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hc, Real.norm_eq_abs]
    exact hk x
  have hlocal : ∀ᵐ y ∂μ, eLpNorm g p (μ.restrict (ball y r)) ≤
      eLpNorm ((2 : ℝ) • h) p (μ.restrict (ball y (2 * r))) := hle.mono fun y hy => by
    have hhy := hh.restrict (ball y (2 * r))
    rw [← ofReal_lpNorm (hg.restrict _), ← ofReal_lpNorm ((hh.const_smul 2).restrict _),
      lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg zero_le_two]
    refine ENNReal.ofReal_le_ofReal (hy.trans ?_)
    have h₁ := hsmul _ hc₁ (fun x => ‖f₁ x‖) (fun x => by
      rw [h_def, abs_norm]; exact le_add_of_nonneg_right (by positivity)) hhy
    have h₂ := hsmul _ hc₂ (fun x => ‖f₂ x‖) (fun x => by
      rw [h_def, abs_norm]; exact le_add_of_nonneg_left (by positivity)) hhy
    rw [lpNorm_norm (hf₁.restrict _).aestronglyMeasurable] at h₁
    rw [lpNorm_norm (hf₂.restrict _).aestronglyMeasurable] at h₂
    linarith
  -- Average the local estimates; the volume ratio of the two balls is `2 ^ dim E`.
  have hglobal := eLpNorm_le_of_ae_eLpNorm_restrict_ball_le hp0 hp hg.aestronglyMeasurable
    (hh.const_smul 2).aestronglyMeasurable hr hlocal
  rw [Measure.addHaar_ball_mul_of_pos μ 0 two_pos r,
    ENNReal.mul_div_cancel_right (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne] at hglobal
  have hpow : ((2 : ℝ) ^ finrank ℝ E) ^ p.toReal⁻¹ ≤ 2 ^ finrank ℝ E := by
    refine (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ one_le_two)
      (inv_le_one_of_one_le₀ ?_)).trans_eq (Real.rpow_one _)
    simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).2 hp1
  have hnorm : lpNorm h p μ ≤ c₁ * lpNorm f₁ p μ + c₂ * lpNorm f₂ p μ := by
    refine (lpNorm_add_le (hf₁.norm.const_mul c₁) hp1).trans_eq ?_
    have e₁ := lpNorm_const_smul c₁ (fun x => ‖f₁ x‖) μ (p := p)
    have e₂ := lpNorm_const_smul c₂ (fun x => ‖f₂ x‖) μ (p := p)
    rw [coe_nnnorm, Real.norm_of_nonneg hc₁, lpNorm_norm hf₁.aestronglyMeasurable] at e₁
    rw [coe_nnnorm, Real.norm_of_nonneg hc₂, lpNorm_norm hf₂.aestronglyMeasurable] at e₂
    rw [← e₁, ← e₂]
    rfl
  rw [← toReal_eLpNorm]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness)
    (hh.const_smul 2).eLpNorm_ne_top) hglobal).trans ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity),
    toReal_eLpNorm, lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg zero_le_two, pow_succ]
  calc ((2 : ℝ) ^ finrank ℝ E) ^ p.toReal⁻¹ * (2 * lpNorm h p μ)
      ≤ 2 ^ finrank ℝ E * (2 * (c₁ * lpNorm f₁ p μ + c₂ * lpNorm f₂ p μ)) :=
        mul_le_mul hpow (by gcongr) (mul_nonneg zero_le_two lpNorm_nonneg) (by positivity)
    _ = _ := by ring

end FiniteDimensional

end TauCeti
