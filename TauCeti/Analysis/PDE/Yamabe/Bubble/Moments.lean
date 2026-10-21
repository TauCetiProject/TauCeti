/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Group.Integral

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

At the endpoint orders `p = n` for `U ^ pₙ`, `p = n - 2` for `|dU|²` and `p = n - 4` for `U²`, the
moments diverge logarithmically.  For these the file computes the moments truncated to a ball
`B(b, R)` exactly.  Each is a constant times `t ^ q (log (1 + (R / t)²) - S_j)`, where `q` is
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
* `TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow` and
  `TauCeti.Yamabe.abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le`:
  the truncated logarithmic moments of the powers of the bubble profile, exactly and up to a
  bounded error.
* `TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_bubble_rpow_criticalExponent`,
  `TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_norm_fderiv_bubble_sq` and
  `TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_bubble_sq`, with their `abs_…_sub_mul_log_le`
  companions: the truncated logarithmic moments of `U ^ pₙ`, `|dU|²` and `U²`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3 and
  §6.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11
  (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open InnerProductSpace MeasureTheory Metric Module ProbabilityTheory Real Set

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

variable [FiniteDimensional ℝ E]

private lemma energyMoment_eq (hn : finrank ℝ E ≠ 2) {p : ℝ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 < t)
    (b x : E) :
    ‖x - b‖ ^ p * ‖fderiv ℝ (bubble t b) x‖ ^ 2 =
      (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 *
        (‖x - b‖ ^ (p + 2) * bubble t b x ^ criticalExponent (finrank ℝ E)) := by
  rw [norm_fderiv_bubble_sq ht, bubble_rpow_criticalExponent hn ht,
    Real.rpow_add' (norm_nonneg _) (by linarith : 0 < p + 2).ne', Real.rpow_two]
  ring

variable [MeasurableSpace E] [BorelSpace E]

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

/-! ### Truncated moments at the logarithmic endpoint

At the endpoint orders the moments above diverge logarithmically, and the moments truncated to a
ball are computed instead.  In polar coordinates about the centre, the integrand of the profile
moment is `r ^ (2 m - 1) (2 t / (t² + r²)) ^ m`.  With `w = r² / (t² + r²)`, its antiderivative is
`(2 t) ^ m / 2 (log (t² + r²) - ∑_{k < m - 1} w ^ (k + 1) / (k + 1))`: the derivative of the
partial logarithmic series is a geometric sum in `w`. -/

/-- The radial integral of the truncated profile moments:
`∫_0^R r ^ (2 m + 1) (2 t / (t² + r²)) ^ (m + 1) dr =
2 ^ m t ^ (m + 1) (log (1 + (R / t)²) - ∑_{k < m} w ^ (k + 1) / (k + 1))`, with
`w = R² / (t² + R²)`. -/
theorem integral_pow_mul_div_add_sq_pow {t : ℝ} (ht : t ≠ 0) (m : ℕ) (R : ℝ) :
    ∫ r in (0)..R, r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) =
      2 ^ m * t ^ (m + 1) * (log (1 + (R / t) ^ 2) -
        ∑ k ∈ Finset.range m, (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1)) := by
  set G : ℝ → ℝ := fun r ↦ r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hG
  set Φ : ℝ → ℝ := fun r ↦ (2 * t) ^ (m + 1) / 2 * (log (t ^ 2 + r ^ 2) -
      ∑ k ∈ Finset.range m, (r ^ 2 / (t ^ 2 + r ^ 2)) ^ (k + 1) / (k + 1)) with hΦ
  have hderiv (r : ℝ) : HasDerivAt Φ (G r) r := by
    have hpos : 0 < t ^ 2 + r ^ 2 := by positivity
    have hq : HasDerivAt (fun r : ℝ ↦ t ^ 2 + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add (t ^ 2)
    have hw : HasDerivAt (fun r : ℝ ↦ r ^ 2 / (t ^ 2 + r ^ 2))
        (2 * r / (t ^ 2 + r ^ 2) * (1 - r ^ 2 / (t ^ 2 + r ^ 2))) r := by
      convert (hasDerivAt_pow 2 r).div hq hpos.ne' using 1
      field_simp
      ring
    have hsum := HasDerivAt.fun_sum (u := Finset.range m) (fun k _ ↦ (hw.pow (k + 1)).div_const
      ((k : ℝ) + 1))
    convert ((hq.log hpos.ne').sub hsum).const_mul ((2 * t) ^ (m + 1) / 2) using 1
    set w := r ^ 2 / (t ^ 2 + r ^ 2) with hw_def
    -- The derivative of the partial logarithmic series telescopes to a geometric sum.
    have hgeom : ∑ k ∈ Finset.range m, (↑(k + 1) : ℝ) * w ^ (k + 1 - 1) *
        (2 * r / (t ^ 2 + r ^ 2) * (1 - w)) / ((k : ℝ) + 1) =
        2 * r / (t ^ 2 + r ^ 2) * (1 - w ^ m) := by
      rw [← geom_sum_mul_neg, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      field_simp
    rw [hgeom, hw_def]
    simp only [hG, div_pow, ← pow_mul]
    field_simp
    ring
  have hcont : Continuous G := by
    rw [hG]
    exact (continuous_pow _).mul ((continuous_const.div (continuous_const.add (continuous_pow 2))
      fun r ↦ (by positivity : (0 : ℝ) < t ^ 2 + r ^ 2).ne').pow _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hderiv r)
    (hcont.intervalIntegrable _ _)]
  have hlog : log (t ^ 2 + R ^ 2) - log (t ^ 2 + 0 ^ 2) = log (1 + (R / t) ^ 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have h0 : ∑ k ∈ Finset.range m, ((0 : ℝ) ^ 2 / (t ^ 2 + 0 ^ 2)) ^ (k + 1) / (k + 1) = 0 :=
    Finset.sum_eq_zero fun k _ ↦ by simp
  simp only [hΦ, h0]
  rw [← hlog]
  ring

/-- **Truncated moments at the logarithmic endpoint.** For an additive Haar measure on a space of
dimension `n`, a natural number `m ≠ 0` and an order `p` with `p + n = 2 m`, the moment of order `p`
of the `m`-th power of the bubble profile `y ↦ 2 t / (t² + ‖y - b‖²)` over the ball `B(b, R)` is
`n |B(0, 1)| 2 ^ (m - 1) t ^ m (log (1 + (R / t)²) - ∑_{k < m - 1} w ^ (k + 1) / (k + 1))`,
with `w = R² / (t² + R²)`. The integral over the whole space diverges logarithmically. -/
theorem setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow
    (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p + finrank ℝ E = 2 * m) {t : ℝ} (ht : t ≠ 0) {R : ℝ} (hR : 0 ≤ R) (b : E) :
    ∫ x in ball b R, ‖x - b‖ ^ p * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ m ∂μ =
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * (2 ^ (m - 1) * t ^ m *
        (log (1 + (R / t) ^ 2) -
          ∑ k ∈ Finset.range (m - 1), (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  simp only [Nat.add_sub_cancel]
  set F : ℝ → ℝ := fun r ↦ r ^ p * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hF
  -- Translate the centre to the origin and pass to polar coordinates.
  have hind : (ball (0 : E) R).indicator (fun y ↦ F ‖y‖) = fun y ↦ (Iio R).indicator F ‖y‖ := by
    ext y
    by_cases hy : ‖y‖ < R
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hy), indicator_of_mem (mem_Iio.2 hy)]
    · rw [indicator_of_notMem (mt mem_ball_zero_iff.1 hy), indicator_of_notMem (mt mem_Iio.1 hy)]
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hn | hn
  · -- On the zero space the weight `‖x - b‖ ^ p` vanishes identically.
    have : Subsingleton E := finrank_zero_iff.1 hn
    have hp0 : p ≠ 0 := by rw [hn] at hp; push_cast at hp; linarith
    simp [Subsingleton.elim _ (0 : E), Real.zero_rpow hp0, hn]
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add]
  simp only [add_sub_cancel_right]
  rw [← integral_indicator measurableSet_ball, hind,
    integral_fun_norm_addHaar μ ((Iio R).indicator F)]
  -- The radial integral is an integral over `(0, R)` of an explicit rational function.
  set G : ℝ → ℝ := fun r ↦ r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hG
  have hrad : ∫ r in Ioi (0 : ℝ), r ^ (finrank ℝ E - 1) • (Iio R).indicator F r =
      ∫ r in (0)..R, G r := by
    have heq : EqOn (fun r ↦ r ^ (finrank ℝ E - 1) • (Iio R).indicator F r)
        ((Ioo 0 R).indicator G) (Ioi 0) := by
      intro r (hr : 0 < r)
      dsimp only
      by_cases hrR : r < R
      · rw [indicator_of_mem (mem_Iio.2 hrR),
          indicator_of_mem (show r ∈ Ioo 0 R from ⟨hr, hrR⟩), smul_eq_mul, hF, hG]
        simp only
        rw [← mul_assoc, ← Real.rpow_natCast r (finrank ℝ E - 1), ← Real.rpow_add hr,
          ← Real.rpow_natCast r (2 * m + 1)]
        congr 3
        push_cast [Nat.cast_sub hn] at hp ⊢
        linarith
      · rw [indicator_of_notMem (mt mem_Iio.1 hrR),
          indicator_of_notMem (show r ∉ Ioo 0 R from fun h ↦ hrR h.2), smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, intervalIntegral.integral_of_le hR,
      integral_Ioc_eq_integral_Ioo]
  rw [hrad, hG, integral_pow_mul_div_add_sq_pow ht]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Truncated moments at the logarithmic endpoint, with remainder bound.** In the setting of
`TauCeti.Yamabe.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow`, the truncated moment
differs from `n |B(0, 1)| 2 ^ (m - 1) t ^ m log (1 + (R / t)²)` by at most
`n |B(0, 1)| 2 ^ (m - 1) t ^ m H_{m - 1}`, where `H_j` is the `j`-th harmonic number. -/
theorem abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le
    (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p + finrank ℝ E = 2 * m) {t : ℝ} (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) (b : E) :
    |∫ x in ball b R, ‖x - b‖ ^ p * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ m ∂μ -
        (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * (2 ^ (m - 1) * t ^ m *
          log (1 + (R / t) ^ 2))| ≤
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * (2 ^ (m - 1) * t ^ m * harmonic (m - 1)) := by
  rw [setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow μ hm hp ht.ne' hR b]
  set w := R ^ 2 / (t ^ 2 + R ^ 2)
  have hw₀ : 0 ≤ w := by positivity
  have hw₁ : w ≤ 1 := div_le_one_of_le₀ (by nlinarith) (by positivity)
  set S := ∑ k ∈ Finset.range (m - 1), w ^ (k + 1) / ((k : ℝ) + 1)
  have hS₀ : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ by positivity
  have hSH : S ≤ harmonic (m - 1) := by
    rw [harmonic, Rat.cast_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [div_eq_mul_inv]
    push_cast
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hw₀ hw₁)
  set K := (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) * (2 ^ (m - 1) * t ^ m)
  have hK : 0 ≤ K := by positivity
  calc _ = |-(K * S)| := by congr 1; ring
    _ = K * S := by rw [abs_neg, abs_of_nonneg (mul_nonneg hK hS₀)]
    _ ≤ K * harmonic (m - 1) := mul_le_mul_of_nonneg_left hSH hK
    _ = _ := by ring

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

omit [BorelSpace E] in
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
