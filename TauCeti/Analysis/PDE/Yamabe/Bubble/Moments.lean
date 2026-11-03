/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Moments of the Euclidean Yamabe bubbles

Let `U = U_{t,b}` be a Yamabe bubble on an `n`-dimensional real inner product space.  This file
computes the radial moments `∫ ‖x - b‖ ^ p …` of order `p ≥ 0` of its critical density `U ^ pₙ`
and of its Dirichlet-energy density `|dU|²`.  For `t > 0`,

* the moment of order `p` of `U ^ pₙ` is finite when `n ≠ 2` and `p < n`, and scales as
  `t ^ p`;
* the moment of order `p` of `|dU|²` is finite when `p < n - 2`, and also scales as `t ^ p`.

The exact values hold for every additive Haar measure and retain the beta integral and the
measure of the unit ball.  This form makes both the scale and the loss of integrability at the
critical moment transparent.  In particular, the fourth energy moment is covered in dimensions
at least seven.  The integrability and the value of `∫ U ^ pₙ` in
`TauCeti.Analysis.PDE.Yamabe.Bubble.Energy` are the moments of order `0`.

At the endpoint orders `p = n` for `U ^ pₙ` (in dimension `n ≠ 2` with `n > 0`), and `p = n - 2`
for `|dU|²` and `p = n - 4` for `U²` (both in dimension `n > 2`), the moments diverge
logarithmically.  For these the file computes the moments truncated to a ball `B(b, R)` exactly,
in the same dimensions.  Each is a constant times `t ^ q (log (1 + (R / t)²) - S_j)`, where `q` is
`n` for `U ^ pₙ` and `n - 2` for the other two densities, and `S_j` is the partial logarithmic
series `∑_{k < j} w ^ (k + 1) / (k + 1)` in `w = R² / (t² + R²) ∈ [0, 1)`, with `j = n - 1` for
`U ^ pₙ` and `|dU|²` and `j = n - 3` for `U²`.  Hence the truncated moment is the logarithmic term
up to an error of at most the same constant times `t ^ q H_j`, with `H_j` the `j`-th harmonic
number.  In dimension six these are the fourth moment of `|dU|²`
and the second moment of `U²`, which grow like `t⁴ log (1 / t)` as `t → 0`.

## Main declarations

* `TauCeti.Yamabe.integrable_norm_sub_rpow_mul_bubble_rpow_criticalExponent` and
  `TauCeti.Yamabe.integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent`: moments of the
  critical density.
* `TauCeti.Yamabe.integrable_norm_sub_rpow_mul_norm_fderiv_bubble_sq` and
  `TauCeti.Yamabe.integral_norm_sub_rpow_mul_norm_fderiv_bubble_sq`: moments of the energy
  density.
* `TauCeti.Yamabe.tendsto_integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent` and
  `TauCeti.Yamabe.tendsto_integral_norm_sub_rpow_mul_norm_fderiv_bubble_sq`: every integrable
  positive-order moment tends to zero with the bubble scale.
* `TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_bubble_rpow_criticalExponent`,
  `TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_norm_fderiv_bubble_sq` and
  `TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_bubble_sq`, with their `abs_…_sub_mul_log_le`
  companions: the truncated logarithmic moments of `U ^ pₙ`, `|dU|²` and `U²`.  They specialize
  the truncated moments of the powers of the bubble profile,
  `TauCeti.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow` and
  `TauCeti.abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3 and
  §6.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11
  (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open Filter InnerProductSpace MeasureTheory Metric Module ProbabilityTheory Real Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma criticalMoment_profile (hn : finrank ℝ E ≠ 2) (p : ℝ) {t : ℝ} (ht : 0 < t)
    (b x : E) :
    ‖x - b‖ ^ p * bubble t b x ^ criticalExponent (finrank ℝ E) =
      ((2 / t) ^ finrank ℝ E * t ^ p) *
        (‖t⁻¹ • (x - b)‖ ^ p * (1 + ‖t⁻¹ • (x - b)‖ ^ 2) ^ (-(2 * (finrank ℝ E : ℝ)) / 2)) := by
  have hnorm : ‖x - b‖ ^ p = t ^ p * ‖t⁻¹ • (x - b)‖ ^ p := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le,
      Real.mul_rpow (inv_nonneg.2 ht.le) (norm_nonneg _), ← mul_assoc,
      ← Real.mul_rpow ht.le (inv_nonneg.2 ht.le), mul_inv_cancel₀ ht.ne', Real.one_rpow, one_mul]
  have hexp : -(2 * (finrank ℝ E : ℝ)) / 2 = -(finrank ℝ E : ℝ) := by ring
  rw [bubble_rpow_criticalExponent_eq_mul_rpow_neg_one_add_norm_sq hn ht, hexp, hnorm]
  ring

private lemma energyMoment_eq (hn : finrank ℝ E ≠ 2) {p : ℝ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 < t)
    (b x : E) :
    ‖x - b‖ ^ p * ‖fderiv ℝ (bubble t b) x‖ ^ 2 =
      (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 *
        (‖x - b‖ ^ (p + 2) * bubble t b x ^ criticalExponent (finrank ℝ E)) := by
  rw [norm_fderiv_bubble_sq ht, bubble_rpow_criticalExponent hn ht,
    Real.rpow_add' (norm_nonneg _) (by linarith : 0 < p + 2).ne', Real.rpow_two]
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In dimension `n ≠ 2`, the moment of order `0 ≤ p < n` about the centre of the critical bubble
density is integrable for every additive Haar measure. -/
theorem integrable_norm_sub_rpow_mul_bubble_rpow_criticalExponent
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : finrank ℝ E ≠ 2) {p : ℝ} (hp : 0 ≤ p)
    (hpn : p < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    Integrable (fun x ↦ ‖x - b‖ ^ p * bubble t b x ^ criticalExponent (finrank ℝ E)) μ := by
  have hJ := integrable_norm_rpow_mul_rpow_neg_one_add_norm_sq μ hp
    (r := 2 * (finrank ℝ E : ℝ)) (by linarith)
  have hscaled := (hJ.comp_smul (inv_ne_zero ht.ne')).const_mul ((2 / t) ^ finrank ℝ E * t ^ p)
  exact (hscaled.comp_sub_right b).congr
    (.of_forall fun x ↦ (criticalMoment_profile hn p ht b x).symm)

/-- The moment of order `0 ≤ p < n` about the centre of the critical bubble density, in dimension
`n ≠ 2`, for an additive Haar measure `μ`.  Its dependence on the scale is exactly `t ^ p`. -/
theorem integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : finrank ℝ E ≠ 2) {p : ℝ} (hp : 0 ≤ p)
    (hpn : p < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    ∫ x, ‖x - b‖ ^ p * bubble t b x ^ criticalExponent (finrank ℝ E) ∂μ =
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 1) * t ^ p *
          beta (((finrank ℝ E : ℝ) + p) / 2) (((finrank ℝ E : ℝ) - p) / 2)) := by
  let J : E → ℝ := fun z ↦ ‖z‖ ^ p * (1 + ‖z‖ ^ 2) ^ (-(2 * (finrank ℝ E : ℝ)) / 2)
  have hpoint (x : E) :
      ‖x - b‖ ^ p * bubble t b x ^ criticalExponent (finrank ℝ E) =
        ((2 / t) ^ finrank ℝ E * t ^ p) * J (t⁻¹ • (x - b)) :=
    criticalMoment_profile hn p ht b x
  have hn₀ : 0 < finrank ℝ E := by exact_mod_cast hp.trans_lt hpn
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn₀
  have hexp : 2 * (finrank ℝ E : ℝ) - finrank ℝ E - p = finrank ℝ E - p := by ring
  rw [integral_congr_ae (.of_forall hpoint), integral_const_mul,
    integral_sub_right_eq_self (fun y ↦ J (t⁻¹ • y)) b,
    Measure.integral_comp_inv_smul_of_nonneg μ J ht.le,
    integral_norm_rpow_mul_rpow_neg_one_add_norm_sq μ hp (by linarith), smul_eq_mul, hexp]
  have hscale : (2 / t) ^ finrank ℝ E * t ^ finrank ℝ E = 2 ^ finrank ℝ E := by
    rw [← mul_pow, div_mul_cancel₀ 2 ht.ne']
  have htwo_pow : (2 : ℝ) ^ finrank ℝ E = 2 * 2 ^ (finrank ℝ E - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn₀]
  linear_combination (t ^ p * ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
    beta (((finrank ℝ E : ℝ) + p) / 2) (((finrank ℝ E : ℝ) - p) / 2)) / 2) *
      (hscale + htwo_pow)

/-- Every positive critical-mass moment of order less than the dimension tends to zero as the
bubble scale tends to zero from above, for any additive Haar measure. -/
theorem tendsto_integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : finrank ℝ E ≠ 2) {p : ℝ} (hp : 0 < p)
    (hpn : p < finrank ℝ E) (b : E) :
    Tendsto (fun t : ℝ ↦ ∫ x, ‖x - b‖ ^ p *
      bubble t b x ^ criticalExponent (finrank ℝ E) ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ ↦ t ^ p) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).continuousWithinAt.tendsto (s := Ioi 0)
  have hlim := ((ht.const_mul ((2 : ℝ) ^ (finrank ℝ E - 1))).mul_const
    (beta (((finrank ℝ E : ℝ) + p) / 2) (((finrank ℝ E : ℝ) - p) / 2))).const_mul
      ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))
  simp only [mul_zero, zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent μ hn hp.le hpn ht b]

/-- In dimension `n > 2`, the moment of order `0 ≤ p < n - 2` about the centre of the
Dirichlet-energy density of a bubble is integrable for every additive Haar measure. -/
theorem integrable_norm_sub_rpow_mul_norm_fderiv_bubble_sq
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 0 ≤ p)
    (hpn : p < (finrank ℝ E : ℝ) - 2) {t : ℝ} (ht : 0 < t) (b : E) :
    Integrable (fun x ↦ ‖x - b‖ ^ p * ‖fderiv ℝ (bubble t b) x‖ ^ 2) μ := by
  have hn : 2 < finrank ℝ E := by exact_mod_cast (show (2 : ℝ) < finrank ℝ E by linarith)
  have h := (integrable_norm_sub_rpow_mul_bubble_rpow_criticalExponent μ hn.ne' (p := p + 2)
    (by linarith) (by linarith) ht b).const_mul ((((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2)
  exact h.congr (.of_forall fun x ↦ (energyMoment_eq hn.ne' hp ht b x).symm)

/-- The moment of order `0 ≤ p < n - 2` about the centre of the Dirichlet-energy density of a
bubble, for an additive Haar measure `μ`.  It scales as `t ^ p`; the excluded endpoint
`p = n - 2` is the logarithmic case. -/
theorem integral_norm_sub_rpow_mul_norm_fderiv_bubble_sq
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 0 ≤ p)
    (hpn : p < (finrank ℝ E : ℝ) - 2) {t : ℝ} (ht : 0 < t) (b : E) :
    ∫ x, ‖x - b‖ ^ p * ‖fderiv ℝ (bubble t b) x‖ ^ 2 ∂μ =
      ((finrank ℝ E : ℝ) - 2) ^ 2 * (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) * t ^ p *
          beta (((finrank ℝ E : ℝ) + p + 2) / 2) (((finrank ℝ E : ℝ) - p - 2) / 2)) := by
  have hn : 2 < finrank ℝ E := by exact_mod_cast (show (2 : ℝ) < finrank ℝ E by linarith)
  have hadd : (finrank ℝ E : ℝ) + (p + 2) = finrank ℝ E + p + 2 := by ring
  have hsub : (finrank ℝ E : ℝ) - (p + 2) = finrank ℝ E - p - 2 := by ring
  rw [integral_congr_ae (.of_forall (energyMoment_eq hn.ne' hp ht b)), integral_const_mul,
    integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent μ hn.ne' (p := p + 2)
      (by linarith) (by linarith) ht b, hadd, hsub, Real.rpow_add ht, Real.rpow_two]
  have htwo_pow : (2 : ℝ) ^ (finrank ℝ E - 1) = 2 ^ (finrank ℝ E - 3) * 2 ^ 2 := by
    rw [← pow_add, show finrank ℝ E - 3 + 2 = finrank ℝ E - 1 by omega]
  have hC : (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * (2 ^ 2 * t ^ 2) =
      ((finrank ℝ E : ℝ) - 2) ^ 2 := by
    field_simp
  linear_combination ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * t ^ p *
    beta (((finrank ℝ E : ℝ) + p + 2) / 2) (((finrank ℝ E : ℝ) - p - 2) / 2)) *
      (2 ^ (finrank ℝ E - 3) * hC + (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * t ^ 2 * htwo_pow)

/-- Every positive Dirichlet-energy moment of order less than `n - 2` tends to zero as the
bubble scale tends to zero from above, for any additive Haar measure. -/
theorem tendsto_integral_norm_sub_rpow_mul_norm_fderiv_bubble_sq
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 0 < p)
    (hpn : p < (finrank ℝ E : ℝ) - 2) (b : E) :
    Tendsto (fun t : ℝ ↦ ∫ x, ‖x - b‖ ^ p * ‖fderiv ℝ (bubble t b) x‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ ↦ t ^ p) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).continuousWithinAt.tendsto (s := Ioi 0)
  have hlim := ((ht.const_mul ((2 : ℝ) ^ (finrank ℝ E - 3))).mul_const
    (beta (((finrank ℝ E : ℝ) + p + 2) / 2)
      (((finrank ℝ E : ℝ) - p - 2) / 2))).const_mul
        (((finrank ℝ E : ℝ) - 2) ^ 2 * (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))
  simp only [mul_zero, zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [integral_norm_sub_rpow_mul_norm_fderiv_bubble_sq μ hp.le hpn ht b]

/-! ### Truncated moments at the logarithmic endpoint

The moments of order `n` of `U ^ pₙ` (in dimension `n ≠ 2` with `n > 0`), of order `n - 2` of
`|dU|²` and of order `n - 4` of `U²` (both in dimension `n > 2`) diverge logarithmically, and the
moments truncated to a ball are computed instead.  Each density is a power of the bubble profile
`2 t / (t² + ‖x - b‖²)`, so these are specializations of
`TauCeti.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow`. -/

/-- The truncated moment of order `n` of the critical bubble density, in dimension `n ≠ 2`, over
the ball `B(b, R)`. It grows like `n |B(0, 1)| 2 ^ (n - 1) t ^ n log (1 + (R / t)²)`, and the
correction is the partial logarithmic series in `w = R² / (t² + R²)`. -/
theorem setIntegral_ball_norm_sub_rpow_mul_bubble_rpow_criticalExponent
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn₀ : 0 < finrank ℝ E) (hn : finrank ℝ E ≠ 2) {t : ℝ}
    (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) (b : E) :
    ∫ x in ball b R, ‖x - b‖ ^ (finrank ℝ E : ℝ) *
        bubble t b x ^ criticalExponent (finrank ℝ E) ∂μ =
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * (2 ^ (finrank ℝ E - 1) * t ^ finrank ℝ E *
        (log (1 + (R / t) ^ 2) - ∑ k ∈ Finset.range (finrank ℝ E - 1),
          (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1))) := by
  simp_rw [bubble_rpow_criticalExponent hn ht b]
  exact setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow μ hn₀.ne' (by ring) ht.ne' hR b

/-- The truncated moment of order `n` of the critical bubble density, in dimension `n ≠ 2`,
differs from `n |B(0, 1)| 2 ^ (n - 1) t ^ n log (1 + (R / t)²)` by at most
`n |B(0, 1)| 2 ^ (n - 1) t ^ n H_{n - 1}`. -/
theorem abs_setIntegral_ball_norm_sub_rpow_mul_bubble_rpow_criticalExponent_sub_mul_log_le
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn₀ : 0 < finrank ℝ E) (hn : finrank ℝ E ≠ 2) {t : ℝ}
    (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) (b : E) :
    |∫ x in ball b R, ‖x - b‖ ^ (finrank ℝ E : ℝ) *
          bubble t b x ^ criticalExponent (finrank ℝ E) ∂μ -
        (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * (2 ^ (finrank ℝ E - 1) *
          t ^ finrank ℝ E * log (1 + (R / t) ^ 2))| ≤
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 1) * t ^ finrank ℝ E * harmonic (finrank ℝ E - 1)) := by
  simp_rw [bubble_rpow_criticalExponent hn ht b]
  exact abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le μ hn₀.ne'
    (by ring) ht hR b

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- In dimension `n > 2`, the truncated energy moment of order `n - 2` is `((n - 2) / (2 t))²`
times the truncated critical moment of order `n`. -/
private lemma setIntegral_ball_energyMoment_eq (μ : Measure E) (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (R : ℝ) (b : E) :
    ∫ x in ball b R, ‖x - b‖ ^ ((finrank ℝ E : ℝ) - 2) * ‖fderiv ℝ (bubble t b) x‖ ^ 2 ∂μ =
      (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * ∫ x in ball b R, ‖x - b‖ ^ (finrank ℝ E : ℝ) *
        bubble t b x ^ criticalExponent (finrank ℝ E) ∂μ := by
  have hp : (0 : ℝ) ≤ (finrank ℝ E : ℝ) - 2 := by
    have : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
    linarith
  simp_rw [energyMoment_eq hn.ne' hp ht b, sub_add_cancel]
  exact integral_const_mul _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The constant of the truncated energy moment: in dimension `n > 2`,
`((n - 2) / (2 t))² 2 ^ (n - 1) t ^ n = (n - 2)² 2 ^ (n - 3) t ^ (n - 2)`. -/
private lemma energyMoment_const (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (a y : ℝ) :
    (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * ((finrank ℝ E : ℝ) * a *
        (2 ^ (finrank ℝ E - 1) * t ^ finrank ℝ E * y)) =
      ((finrank ℝ E : ℝ) - 2) ^ 2 * (finrank ℝ E : ℝ) * a *
        (2 ^ (finrank ℝ E - 3) * t ^ (finrank ℝ E - 2) * y) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have h1 : finrank ℝ E - 1 = k + 2 := by omega
  have h2 : finrank ℝ E - 2 = k + 1 := by omega
  have h3 : finrank ℝ E - 3 = k := by omega
  rw [h1, h2, h3, hk]
  field_simp
  ring

/-- The truncated moment of order `n - 2` of the Dirichlet-energy density of a bubble, in
dimension `n > 2`, over the ball `B(b, R)`. It grows like
`(n - 2)² n |B(0, 1)| 2 ^ (n - 3) t ^ (n - 2) log (1 + (R / t)²)`; in dimension `6` this is the
fourth energy moment. -/
theorem setIntegral_ball_norm_sub_rpow_mul_norm_fderiv_bubble_sq
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) {R : ℝ}
    (hR : 0 ≤ R) (b : E) :
    ∫ x in ball b R, ‖x - b‖ ^ ((finrank ℝ E : ℝ) - 2) * ‖fderiv ℝ (bubble t b) x‖ ^ 2 ∂μ =
      ((finrank ℝ E : ℝ) - 2) ^ 2 * (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) * t ^ (finrank ℝ E - 2) *
          (log (1 + (R / t) ^ 2) - ∑ k ∈ Finset.range (finrank ℝ E - 1),
            (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1))) := by
  rw [setIntegral_ball_energyMoment_eq μ hn ht R b,
    setIntegral_ball_norm_sub_rpow_mul_bubble_rpow_criticalExponent μ (by omega) hn.ne' ht hR b,
    energyMoment_const hn ht]

/-- The truncated moment of order `n - 2` of the Dirichlet-energy density of a bubble, in
dimension `n > 2`, differs from `(n - 2)² n |B(0, 1)| 2 ^ (n - 3) t ^ (n - 2) log (1 + (R / t)²)`
by at most `(n - 2)² n |B(0, 1)| 2 ^ (n - 3) t ^ (n - 2) H_{n - 1}`. -/
theorem abs_setIntegral_ball_norm_sub_rpow_mul_norm_fderiv_bubble_sq_sub_mul_log_le
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) {R : ℝ}
    (hR : 0 ≤ R) (b : E) :
    |∫ x in ball b R, ‖x - b‖ ^ ((finrank ℝ E : ℝ) - 2) * ‖fderiv ℝ (bubble t b) x‖ ^ 2 ∂μ -
        ((finrank ℝ E : ℝ) - 2) ^ 2 * (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
          (2 ^ (finrank ℝ E - 3) * t ^ (finrank ℝ E - 2) * log (1 + (R / t) ^ 2))| ≤
      ((finrank ℝ E : ℝ) - 2) ^ 2 * (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) * t ^ (finrank ℝ E - 2) * harmonic (finrank ℝ E - 1)) := by
  have h := abs_setIntegral_ball_norm_sub_rpow_mul_bubble_rpow_criticalExponent_sub_mul_log_le μ
    (by omega) hn.ne' ht hR b
  rw [setIntegral_ball_energyMoment_eq μ hn ht R b, ← energyMoment_const hn ht,
    ← energyMoment_const hn ht, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The truncated moment of order `n - 4` of the square of a bubble, in dimension `n > 2`, over
the ball `B(b, R)`. It grows like `n |B(0, 1)| 2 ^ (n - 3) t ^ (n - 2) log (1 + (R / t)²)`; in
dimension `6` this is the second moment of `U²`. -/
theorem setIntegral_ball_norm_sub_rpow_mul_bubble_sq
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) {R : ℝ}
    (hR : 0 ≤ R) (b : E) :
    ∫ x in ball b R, ‖x - b‖ ^ ((finrank ℝ E : ℝ) - 4) * bubble t b x ^ 2 ∂μ =
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) * t ^ (finrank ℝ E - 2) *
          (log (1 + (R / t) ^ 2) - ∑ k ∈ Finset.range (finrank ℝ E - 3),
            (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1))) := by
  simp_rw [bubble_sq hn.le ht.le b]
  rw [setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow μ (by omega)
    (by push_cast [Nat.cast_sub hn.le]; ring) ht.ne' hR b, Nat.sub_sub]

/-- The truncated moment of order `n - 4` of the square of a bubble, in dimension `n > 2`,
differs from `n |B(0, 1)| 2 ^ (n - 3) t ^ (n - 2) log (1 + (R / t)²)` by at most
`n |B(0, 1)| 2 ^ (n - 3) t ^ (n - 2) H_{n - 3}`. -/
theorem abs_setIntegral_ball_norm_sub_rpow_mul_bubble_sq_sub_mul_log_le
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) {R : ℝ}
    (hR : 0 ≤ R) (b : E) :
    |∫ x in ball b R, ‖x - b‖ ^ ((finrank ℝ E : ℝ) - 4) * bubble t b x ^ 2 ∂μ -
        (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
          (2 ^ (finrank ℝ E - 3) * t ^ (finrank ℝ E - 2) * log (1 + (R / t) ^ 2))| ≤
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) * t ^ (finrank ℝ E - 2) * harmonic (finrank ℝ E - 3)) := by
  simp_rw [bubble_sq hn.le ht.le b]
  have h := abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le μ
    (m := finrank ℝ E - 2) (p := (finrank ℝ E : ℝ) - 4) (by omega)
    (by push_cast [Nat.cast_sub hn.le]; ring) ht hR b
  simpa only [Nat.sub_sub, Nat.reduceAdd] using h

end TauCeti.Yamabe
