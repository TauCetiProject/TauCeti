/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.SmallJump.Basic
public import TauCeti.Probability.Distributions.CompoundPoisson.Moments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Probability.ConditionalProbability
import TauCeti.Probability.Distributions.CompoundPoisson.Intensity
import TauCeti.Probability.Distributions.Affine

/-!
# Finite small-jump remainders for scalar stable laws

The compensated compound-Poisson approximation to a scalar stable law splits at two positive
cutoffs.  This file names the factor made from jumps in the band `ε < |x| ≤ r` and controls its
first two moments.  Its mean is the integral of `x - sin x` over that band, while its variance is
the band integral of `x²`.

The sine compensation is third order at the origin.  Consequently both the mean and variance of
the band factor are bounded by quantities that vanish with the outer cutoff `r`, uniformly in the
inner cutoff `ε`.  This is the quantitative small-jump input for passing finite-cutoff support
decompositions to stable laws.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Topology

namespace TauCeti.Probability

/-- The compensated compound-Poisson law of stable jumps in the band `ε < |x| ≤ r`.

Its useful parameter range is `0 < α < 2`, `|β| ≤ 1`, and `0 < ε ≤ r`. -/
def stableSmallJumpRemainderMeasure (α β ε r : ℝ) : Measure ℝ :=
  let ν := stableLevyMeasure α β
  let band := {x : ℝ | ε < |x| ∧ |x| ≤ r}
  (compoundPoissonMeasure (ν band).toNNReal (cond ν band)).map
    (fun x ↦ x - ∫ y in band, sin y ∂ν)

/-- The defining formula for the compensated small-jump remainder. -/
theorem stableSmallJumpRemainderMeasure_def (α β ε r : ℝ) :
    stableSmallJumpRemainderMeasure α β ε r =
      (compoundPoissonMeasure
        ((stableLevyMeasure α β) {x : ℝ | ε < |x| ∧ |x| ≤ r}).toNNReal
        (cond (stableLevyMeasure α β) {x : ℝ | ε < |x| ∧ |x| ≤ r})).map
        (fun x ↦ x - ∫ y in {y : ℝ | ε < |y| ∧ |y| ≤ r}, sin y
          ∂stableLevyMeasure α β) := (rfl)

private lemma smallJumpBand_self (r : ℝ) :
    {x : ℝ | r < |x| ∧ |x| ≤ r} = ∅ := by
  rw [Set.ext_iff]
  intro x
  rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact fun hx ↦ (not_lt_of_ge hx.2) hx.1

/-- With coincident cutoffs, the stable small-jump remainder is the point mass at zero. -/
@[simp]
theorem stableSmallJumpRemainderMeasure_self (α β r : ℝ) :
    stableSmallJumpRemainderMeasure α β r r = Measure.dirac 0 := by
  rw [stableSmallJumpRemainderMeasure_def, smallJumpBand_self]
  simp

/-- The compensated small-jump remainder is a probability measure for every positive lower
cutoff `ε`. -/
theorem isProbabilityMeasure_stableSmallJumpRemainderMeasure {α β ε r : ℝ} (hε : 0 < ε) :
    IsProbabilityMeasure (stableSmallJumpRemainderMeasure α β ε r) := by
  let ν := stableLevyMeasure α β
  let band : Set ℝ := {x | ε < |x| ∧ |x| ≤ r}
  have : IsFiniteMeasure (ν.restrict band) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (stableLevyMeasure_abs_gt_ne_top (α := α) (β := β) hε) (measure_mono fun _ hx ↦ hx.1))
  have hprob := isProbabilityMeasure_compoundPoissonMeasure_cond (ν.restrict band)
  let _ : IsProbabilityMeasure (compoundPoissonMeasure (ν band).toNNReal (cond ν band)) := by
    simpa only [Measure.restrict_apply_univ, ProbabilityTheory.cond,
      Measure.restrict_univ] using hprob
  rw [stableSmallJumpRemainderMeasure_def]
  infer_instance

/-- The identity has a finite second moment under a valid compensated small-jump remainder. -/
theorem memLp_two_id_stableSmallJumpRemainderMeasure {α β ε r : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hεr : ε ≤ r) :
    MemLp id 2 (stableSmallJumpRemainderMeasure α β ε r) := by
  rcases hεr.eq_or_lt with rfl | hεr
  · simp
  let ν := stableLevyMeasure α β
  let band : Set ℝ := {x | ε < |x| ∧ |x| ≤ r}
  let _ := isProbabilityMeasure_cond_stableLevyMeasure_smallJumpBand hα hβ hε hεr
  have hjump : MemLp id 2 (cond ν band) :=
    memLp_two_id_cond_stableLevyMeasure_smallJumpBand
  have hsum := memLp_two_id_compoundPoissonMeasure hjump (ν band).toNNReal
  rw [stableSmallJumpRemainderMeasure_def]
  simpa only [one_mul, sub_eq_add_neg, add_comm] using
    (memLp_id_map_affine_iff (a := -(∫ y in band, sin y ∂ν))
      (b := 1) one_ne_zero).2 hsum

/-- The mean of the compensated small-jump remainder is the band integral of `x - sin x`. -/
theorem integral_id_stableSmallJumpRemainderMeasure {α β ε r : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hεr : ε ≤ r) :
    ∫ x, x ∂stableSmallJumpRemainderMeasure α β ε r =
      ∫ x in {x : ℝ | ε < |x| ∧ |x| ≤ r}, x - sin x ∂stableLevyMeasure α β := by
  rcases hεr.eq_or_lt with rfl | hεr
  · simp [smallJumpBand_self]
  let ν := stableLevyMeasure α β
  let band : Set ℝ := {x | ε < |x| ∧ |x| ≤ r}
  have hband : MeasurableSet band := by measurability
  have htop : ν band ≠ ∞ := ne_top_of_le_ne_top (stableLevyMeasure_abs_gt_ne_top hε)
    (measure_mono fun _ hx ↦ hx.1)
  let _ := isProbabilityMeasure_cond_stableLevyMeasure_smallJumpBand hα hβ hε hεr
  let _ := isProbabilityMeasure_stableSmallJumpRemainderMeasure (α := α) (β := β) (r := r) hε
  have hjump : MemLp id 2 (cond ν band) :=
    memLp_two_id_cond_stableLevyMeasure_smallJumpBand
  have hjump_one : Integrable id (cond ν band) := hjump.integrable (by norm_num)
  have hsum : Integrable id (compoundPoissonMeasure (ν band).toNNReal (cond ν band)) :=
    integrable_id_compoundPoissonMeasure hjump_one _
  have hmean := integral_id_map_affine (a := -(∫ y in band, sin y ∂ν)) (b := 1) hsum
  simp only [one_mul, add_comm] at hmean
  have hmean_exact :
      ∫ x, x ∂stableSmallJumpRemainderMeasure α β ε r =
        -(∫ y in band, sin y ∂ν) +
          ∫ x, x ∂compoundPoissonMeasure (ν band).toNNReal (cond ν band) := by
    rw [stableSmallJumpRemainderMeasure_def]
    simpa only [ν, band, sub_eq_add_neg] using hmean
  rw [hmean_exact, integral_id_compoundPoissonMeasure hjump_one]
  have hid := ν.toNNReal_smul_integral_cond_eq_setIntegral band id htop
  simp only [id_eq, NNReal.smul_def, smul_eq_mul] at hid
  simp only [smul_eq_mul]
  rw [hid]
  have hfinite : IsFiniteMeasure (ν.restrict band) :=
    isFiniteMeasure_restrict.mpr htop
  let _ := hfinite
  have hid_int : IntegrableOn id band ν :=
    Integrable.of_bound aestronglyMeasurable_id r
      ((ae_restrict_mem hband).mono fun x hx ↦ by
        simpa only [id_eq, Real.norm_eq_abs] using hx.2)
  have hsin_int : IntegrableOn sin band ν :=
    Integrable.of_bound (Real.continuous_sin.aestronglyMeasurable) 1
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using abs_sin_le_one x)
  calc
    _ = ∫ x in band, id x - sin x ∂ν := by
      rw [integral_sub hid_int hsin_int]
      simp only [id_eq]
      ring
    _ = _ := by simp only [ν, band, id_eq]

/-- The variance of the compensated small-jump remainder is the band second moment of the
stable Lévy measure. -/
theorem variance_id_stableSmallJumpRemainderMeasure {α β ε r : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hεr : ε ≤ r) :
    Var[id; stableSmallJumpRemainderMeasure α β ε r] =
      ∫ x in {x : ℝ | ε < |x| ∧ |x| ≤ r}, x ^ 2 ∂stableLevyMeasure α β := by
  rcases hεr.eq_or_lt with rfl | hεr
  · simp [smallJumpBand_self]
  let ν := stableLevyMeasure α β
  let band : Set ℝ := {x | ε < |x| ∧ |x| ≤ r}
  have htop : ν band ≠ ∞ := ne_top_of_le_ne_top (stableLevyMeasure_abs_gt_ne_top hε)
    (measure_mono fun _ hx ↦ hx.1)
  let _ := isProbabilityMeasure_cond_stableLevyMeasure_smallJumpBand hα hβ hε hεr
  have hjump : MemLp id 2 (cond ν band) :=
    memLp_two_id_cond_stableLevyMeasure_smallJumpBand
  have hvariance := variance_id_map_affine
    (μ := compoundPoissonMeasure (ν band).toNNReal (cond ν band))
    (a := -(∫ y in band, sin y ∂ν)) (b := 1)
  simp only [one_pow, one_mul] at hvariance
  have hvariance_exact :
      Var[id; stableSmallJumpRemainderMeasure α β ε r] =
        Var[id; compoundPoissonMeasure (ν band).toNNReal (cond ν band)] := by
    rw [stableSmallJumpRemainderMeasure_def]
    simpa only [ν, band, sub_eq_add_neg, add_comm] using hvariance
  rw [hvariance_exact, variance_id_compoundPoissonMeasure hjump]
  have hsecond :=
    ν.toNNReal_smul_integral_cond_eq_setIntegral band (fun x : ℝ ↦ x ^ 2) htop
  simpa only [ν, band, NNReal.smul_def, smul_eq_mul] using hsecond

/-- The variance of a valid band remainder is bounded by the full stable second moment below
its outer cutoff. -/
theorem variance_id_stableSmallJumpRemainderMeasure_le {α β ε r : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hεr : ε ≤ r) :
    Var[id; stableSmallJumpRemainderMeasure α β ε r] ≤
      ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β := by
  let ν := stableLevyMeasure α β
  let band : Set ℝ := {x | ε < |x| ∧ |x| ≤ r}
  have hsphere : ν (Metric.sphere (0 : ℝ) r) = 0 := by
    simpa only [ν, stableLevyMeasure_def] using
      (withDensity_absolutelyContinuous volume
      (fun x ↦ ENNReal.ofReal (stableLevyDensity α β x)))
        (Measure.addHaar_sphere volume 0 r)
  have hsubset : band \ Metric.ball (0 : ℝ) r ⊆ Metric.sphere 0 r := by
    intro x hx
    have hnot : ¬|x| < r := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx.2
    have heq : |x| = r := le_antisymm hx.1.2 (le_of_not_gt hnot)
    simpa only [Metric.mem_sphere, Real.dist_eq, sub_zero] using heq
  have hae : band ≤ᵐ[ν] Metric.ball (0 : ℝ) r := by
    rw [ae_le_set]
    exact measure_mono_null hsubset hsphere
  rw [variance_id_stableSmallJumpRemainderMeasure hα hβ hε hεr]
  exact setIntegral_mono_set (integrableOn_sq_stableLevyMeasure α β r)
    (ae_of_all _ fun x ↦ sq_nonneg x) hae

/-- Sine compensation makes the mean third order: it is at most `r / 6` times the
variance. -/
theorem abs_integral_id_stableSmallJumpRemainderMeasure_le {α β ε r : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hεr : ε ≤ r) :
    |∫ x, x ∂stableSmallJumpRemainderMeasure α β ε r| ≤
      r / 6 * Var[id; stableSmallJumpRemainderMeasure α β ε r] := by
  let ν := stableLevyMeasure α β
  let band : Set ℝ := {x | ε < |x| ∧ |x| ≤ r}
  have hband : MeasurableSet band := by measurability
  have htop : ν band ≠ ∞ := ne_top_of_le_ne_top (stableLevyMeasure_abs_gt_ne_top hε)
    (measure_mono fun _ hx ↦ hx.1)
  have hfinite : IsFiniteMeasure (ν.restrict band) := isFiniteMeasure_restrict.mpr htop
  let _ := hfinite
  have hsq : IntegrableOn (fun x : ℝ ↦ x ^ 2) band ν :=
    Integrable.of_bound (by fun_prop) (r ^ 2)
      ((ae_restrict_mem hband).mono fun x hx ↦ by
        simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
          (sq_le_sq₀ (abs_nonneg x) (hε.trans_le hεr).le).2 hx.2)
  have hdom : ∀ᵐ x ∂ν.restrict band, ‖x - sin x‖ ≤ r / 6 * x ^ 2 := by
    filter_upwards [ae_restrict_mem hband] with x hx
    calc
      ‖x - sin x‖ = |x - sin x| := Real.norm_eq_abs _
      _ ≤ |x| ^ 3 / 6 := Real.abs_sub_sin_le x
      _ ≤ r * |x| ^ 2 / 6 := div_le_div_of_nonneg_right
        (by
          simpa only [pow_succ, mul_comm] using
            mul_le_mul_of_nonneg_right hx.2 (sq_nonneg |x|)) (by norm_num)
      _ = r / 6 * x ^ 2 := by rw [sq_abs]; ring
  have hbound := norm_integral_le_of_norm_le (hsq.const_mul (r / 6)) hdom
  rw [integral_id_stableSmallJumpRemainderMeasure hα hβ hε hεr,
    variance_id_stableSmallJumpRemainderMeasure hα hβ hε hεr]
  simpa only [Real.norm_eq_abs, integral_const_mul] using hbound

/-- The raw second moment of a valid band remainder is its variance plus the square of its
mean. -/
theorem integral_sq_stableSmallJumpRemainderMeasure {α β ε r : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hεr : ε ≤ r) :
    ∫ x, x ^ 2 ∂stableSmallJumpRemainderMeasure α β ε r =
      Var[id; stableSmallJumpRemainderMeasure α β ε r] +
        (∫ x, x ∂stableSmallJumpRemainderMeasure α β ε r) ^ 2 := by
  let _ := isProbabilityMeasure_stableSmallJumpRemainderMeasure (α := α) (β := β) (r := r) hε
  have hvariance := variance_eq_sub
    (memLp_two_id_stableSmallJumpRemainderMeasure hα hβ hε hεr)
  simp only [id_eq, Pi.pow_apply] at hvariance
  linarith

/-- Uniformly over a shrinking positive inner cutoff, the variance of the stable band
remainder tends to zero with its outer cutoff. -/
theorem tendsto_variance_stableSmallJumpRemainderMeasure_zero {α β : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) {ε : ℝ → ℝ}
    (hε : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ε r ∧ ε r ≤ r) :
    Tendsto (fun r ↦ Var[id; stableSmallJumpRemainderMeasure α β (ε r) r])
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have houter := (tendsto_integral_sq_stableLevyMeasure_ball_zero hα hβ).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  apply squeeze_zero' (Eventually.of_forall fun r ↦ variance_nonneg id
    (stableSmallJumpRemainderMeasure α β (ε r) r))
  · filter_upwards [hε] with r hr
    exact variance_id_stableSmallJumpRemainderMeasure_le hα hβ hr.1 hr.2
  · exact houter

/-- Uniformly over a shrinking positive inner cutoff, the mean of the stable band remainder
tends to zero with its outer cutoff. -/
theorem tendsto_integral_id_stableSmallJumpRemainderMeasure_zero {α β : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) {ε : ℝ → ℝ}
    (hε : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ε r ∧ ε r ≤ r) :
    Tendsto (fun r ↦ ∫ x, x ∂stableSmallJumpRemainderMeasure α β (ε r) r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have houter := (tendsto_integral_sq_stableLevyMeasure_ball_zero hα hβ).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hr : Tendsto (fun r : ℝ ↦ r / 6) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := inf_le_left
    convert (continuousAt_id.tendsto.div_const 6).mono_left hle using 1 <;> norm_num
  have hproduct : Tendsto (fun r ↦ r / 6 *
      ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hr.mul houter
  apply squeeze_zero' (Eventually.of_forall fun r ↦ norm_nonneg
    (∫ x, x ∂stableSmallJumpRemainderMeasure α β (ε r) r))
  · filter_upwards [hε] with r hcut
    have hr_nonneg : 0 ≤ r / 6 := div_nonneg (hcut.1.trans_le hcut.2).le (by norm_num)
    simpa only [Real.norm_eq_abs] using
      (abs_integral_id_stableSmallJumpRemainderMeasure_le hα hβ hcut.1 hcut.2).trans
        (mul_le_mul_of_nonneg_left
          (variance_id_stableSmallJumpRemainderMeasure_le hα hβ hcut.1 hcut.2) hr_nonneg)
  · exact hproduct

/-- Uniformly over a shrinking positive inner cutoff, the band remainder converges to zero
in second moment. -/
theorem tendsto_integral_sq_stableSmallJumpRemainderMeasure_zero {α β : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) {ε : ℝ → ℝ}
    (hε : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < ε r ∧ ε r ≤ r) :
    Tendsto (fun r ↦ ∫ x, x ^ 2 ∂stableSmallJumpRemainderMeasure α β (ε r) r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hvariance := tendsto_variance_stableSmallJumpRemainderMeasure_zero hα hβ hε
  have hmean := tendsto_integral_id_stableSmallJumpRemainderMeasure_zero hα hβ hε
  have hsum := hvariance.add (hmean.pow 2)
  norm_num at hsum
  apply hsum.congr'
  filter_upwards [hε] with r hr
  exact (integral_sq_stableSmallJumpRemainderMeasure hα hβ hr.1 hr.2).symm

end TauCeti.Probability
