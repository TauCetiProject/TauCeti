/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
public import TauCeti.Probability.Distributions.Stable.Cutoff
import TauCeti.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Large-jump and small-jump factors of stable laws

At every positive cutoff, a standardized non-Gaussian stable law is the convolution of
its compensated compound-Poisson large jumps and a unique small-jump probability law.
The latter has characteristic exponent equal to the compensated Lévy integral over
`{x | |x| ≤ r}`. Thus the finite-cutoff splitting persists after removing the lower cutoff.

`existsUnique_conv_stableCompensatedPoissonMeasure_eq` gives existence and uniqueness of the
small-jump probability factor, extending `stableCompensatedPoissonMeasure_split` to the limit.
`charFun_of_conv_stableCompensatedPoissonMeasure_eq` identifies the characteristic function
of any such factor without choosing a representative. This decomposition separates the
finite-intensity jumps from the remaining small jumps for support and tail arguments.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Topology

namespace TauCeti.Probability

variable {α β r : ℝ}

/-- For positive `ε ≤ r`, the compensated compound-Poisson law of the jumps of size at most `ε`
splits off the large jumps in `(ε, r]`: it is the convolution of a probability measure, the
compensated compound-Poisson law of the finite band `ε < |x| ≤ r`, with the law of the jumps of
size at most `r`. -/
theorem exists_probabilityMeasure_conv_stableCompensatedPoissonMeasure_eq {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ r) :
    ∃ μ : ProbabilityMeasure ℝ,
      (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r =
        stableCompensatedPoissonMeasure α β ε := by
  let ν := stableLevyMeasure α β
  let band := {x : ℝ | ε < |x| ∧ |x| ≤ r}
  have hfinite : IsFiniteMeasure (ν.restrict band) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (stableLevyMeasure_abs_gt_ne_top (α := α) (β := β) hε)
      (measure_mono fun _ hx ↦ hx.1))
  have := hfinite
  refine ⟨⟨(compoundPoissonMeasure (ν band).toNNReal (cond ν band)).map
      (fun x ↦ x - ∫ y in band, sin y ∂ν), ?_⟩, ?_⟩
  · have hprob := isProbabilityMeasure_compoundPoissonMeasure_cond (ν.restrict band)
    let _ : IsProbabilityMeasure (compoundPoissonMeasure (ν band).toNNReal (cond ν band)) := by
      simpa only [Measure.restrict_apply_univ, ProbabilityTheory.cond,
        Measure.restrict_univ] using hprob
    infer_instance
  · have h := (stableCompensatedPoissonMeasure_split α β hε hεr).symm
    rwa [stableSmallJumpRemainderMeasure_def] at h

/-- At a positive cutoff, the standardized stable law has a unique small-jump probability
factor complementary to its compensated compound-Poisson large jumps. This includes both
fully skewed laws and shape one. -/
theorem existsUnique_conv_stableCompensatedPoissonMeasure_eq
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hr : 0 < r) :
    ∃! μ : ProbabilityMeasure ℝ,
      (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0 := by
  -- Keep every lower cutoff below `r`, so even the initial finite-band laws are probabilities.
  let ε (n : ℕ) := min r ((2 : ℝ)⁻¹ ^ n)
  have hε (n : ℕ) : 0 < ε n := lt_min hr (by positivity)
  choose μ hsplit using fun n ↦
    exists_probabilityMeasure_conv_stableCompensatedPoissonMeasure_eq (α := α) (β := β)
      (hε n) (min_le_left r _)
  let large := stableCompensatedPoissonMeasure α β r
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ hr
  have hlarge (t : ℝ) : charFun large t ≠ 0 := by
    rw [charFun_stableCompensatedPoissonMeasure hα hβ hr]
    exact Complex.exp_ne_zero _
  -- Divide the finite splitting identity by the nonvanishing large-jump characteristic function.
  have hεlim : Tendsto ε atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [min_eq_right hr.le] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ r) atTop (𝓝 r)).min
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
            (by norm_num : (2 : ℝ)⁻¹ < 1)))
    · exact .of_forall hε
  have hchar (t : ℝ) :
      Tendsto (fun n ↦ charFun (μ n) t) atTop
        (𝓝 (Complex.exp (stableCharacteristicExponent α β t) / charFun large t)) := by
    have hlim := ((tendsto_charFun_stableCompensatedPoissonMeasure hα hβ t).comp hεlim).div_const
      (charFun large t)
    convert hlim using 1
    funext n
    rw [Function.comp_apply, ← hsplit n, charFun_conv, mul_div_cancel_right₀ _ (hlarge t)]
  -- Lévy's theorem constructs the small-jump limit; characteristic uniqueness gives the split.
  obtain ⟨ρ, hρ, -⟩ := exists_probabilityMeasure_of_tendsto_charFun
    ((Complex.continuous_exp.continuousAt.comp
      (continuousAt_stableCharacteristicExponent_zero hα.1 β)).div
      (continuous_charFun (μ := large)).continuousAt (hlarge 0)) hchar
  have hconv : (ρ : Measure ℝ) ∗ large = stableMeasure α β 1 0 := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_conv, congrFun hρ.1 t, Pi.div_apply, Function.comp_apply,
      div_mul_cancel₀ _ (hlarge t),
      charFun_stableMeasure ⟨hα.1, hα.2.le⟩ hβ]
    simp
  refine ⟨ρ, hconv, fun σ hσ ↦ ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  apply mul_right_cancel₀ (hlarge t)
  rw [← charFun_conv, ← charFun_conv, hσ, hconv]

/-- The small-jump factor has the compensated Lévy exponent restricted to jumps of size at
most the cutoff. The statement applies to any probability law satisfying the decomposition,
without choosing a particular representative of the unique factor. -/
theorem charFun_of_conv_stableCompensatedPoissonMeasure_eq
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hr : 0 < r)
    {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0)
    (t : ℝ) :
    charFun μ t = Complex.exp (∫ x in {x : ℝ | |x| ≤ r},
      Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
        (t * sin x : ℝ) * Complex.I ∂stableLevyMeasure α β) := by
  let ν := stableLevyMeasure α β
  let f := fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
    (t * sin x : ℝ) * Complex.I
  have hf : Integrable f ν := integrable_exp_sub_one_sub_sin_stableLevyMeasure α β t
  have hset : MeasurableSet {x : ℝ | |x| ≤ r} := by measurability
  have hsum : (∫ x in {x : ℝ | |x| ≤ r}, f x ∂ν) +
      (∫ x in {x : ℝ | r < |x|}, f x ∂ν) = stableCharacteristicExponent α β t := by
    have h := integral_add_compl hset hf
    simp only [compl_ofPred, not_le] at h
    exact h.trans (integral_exp_sub_one_sub_sin_stableLevyMeasure hα hβ t)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ hr
  have heq := congrArg (fun η : Measure ℝ ↦ charFun η t) hμ
  rw [charFun_conv, charFun_stableCompensatedPoissonMeasure hα hβ hr,
    charFun_stableMeasure ⟨hα.1, hα.2.le⟩ hβ] at heq
  simp only [NNReal.coe_one, one_mul, zero_mul, Complex.ofReal_zero, zero_add] at heq
  apply mul_right_cancel₀ (Complex.exp_ne_zero (∫ x in {x : ℝ | r < |x|}, f x ∂ν))
  rw [heq, ← Complex.exp_add, hsum]

end TauCeti.Probability
