/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Approximation
public import TauCeti.Probability.Distributions.CompoundPoisson.Intensity

/-!
# Splitting compensated stable approximations at a jump cutoff

For `0 < ε ≤ r`, the stable Lévy jumps larger than `ε` split into the band
`ε < |x| ≤ r` and the jumps larger than `r`. Superposition of the restricted finite
intensities gives independent compound Poisson factors. The sine compensation is additive
over these regions, so the compensated approximation at `ε` is the convolution of the
compensated band law and the compensated approximation at `r`.

This finite-cutoff identity separates the large jumps from the small jumps before passing
to a limit. It includes coincident cutoffs, where the band law is the point mass at zero,
and invalid stable parameters, where the underlying Lévy measure is zero.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

/-- Splitting the retained jumps at a second cutoff gives independent compensated
compound Poisson factors. No shape assumptions are needed because invalid parameters have
zero Lévy intensity. -/
theorem stableCompensatedPoissonMeasure_split (α β : ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hεr : ε ≤ r) :
    stableCompensatedPoissonMeasure α β ε =
      (compoundPoissonMeasure
        ((stableLevyMeasure α β) {x : ℝ | ε < |x| ∧ |x| ≤ r}).toNNReal
        (cond (stableLevyMeasure α β) {x : ℝ | ε < |x| ∧ |x| ≤ r})).map
        (fun x ↦ x - ∫ y in {y : ℝ | ε < |y| ∧ |y| ≤ r}, sin y
          ∂stableLevyMeasure α β) ∗
        stableCompensatedPoissonMeasure α β r := by
  let ν := stableLevyMeasure α β
  let band : Set ℝ := {x | ε < |x| ∧ |x| ≤ r}
  let large : Set ℝ := {x | r < |x|}
  have hlarge : MeasurableSet large := by measurability
  have hdisj : Disjoint band large := by
    rw [Set.disjoint_left]
    exact fun _ hx hy ↦ hx.2.not_gt hy
  have hunion : band ∪ large = {x : ℝ | ε < |x|} := by
    ext x
    simp only [mem_union, mem_ofPred_eq, band, large]
    grind
  have hband_top : ν band ≠ ∞ := ne_top_of_le_ne_top
    (stableLevyMeasure_abs_gt_ne_top (α := α) (β := β) hε)
    (measure_mono fun _ hx ↦ hx.1)
  let _ : IsFiniteMeasure (ν.restrict band) := isFiniteMeasure_restrict.mpr hband_top
  let _ := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (α := α) (β := β)
    (hε.trans_le hεr)
  have hsplit : ν.restrict {x : ℝ | ε < |x|} = ν.restrict band + ν.restrict large := by
    rw [← hunion, Measure.restrict_union hdisj hlarge]
  have hcp : compoundPoissonMeasure (ν {x : ℝ | ε < |x|}).toNNReal
      (cond ν {x : ℝ | ε < |x|}) =
      compoundPoissonMeasure (ν band).toNNReal (cond ν band) ∗
        compoundPoissonMeasure (ν large).toNNReal (cond ν large) := by
    have h := compoundPoissonMeasure_add_intensity (ν.restrict band) (ν.restrict large)
    rw [← hsplit] at h
    simpa only [Measure.restrict_apply_univ, ProbabilityTheory.cond,
      Measure.restrict_univ] using h
  have hsin (s : Set ℝ) [IsFiniteMeasure (ν.restrict s)] :
      IntegrableOn sin s ν :=
    Integrable.of_bound (by fun_prop) 1
      (.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using abs_sin_le_one x)
  have hcenter : (∫ x in {x : ℝ | ε < |x|}, sin x ∂ν) =
      (∫ x in band, sin x ∂ν) + ∫ x in large, sin x ∂ν := by
    rw [← hunion, setIntegral_union hdisj hlarge (hsin band) (hsin large)]
  -- Translations become convolutions with Dirac measures. Associativity and commutativity
  -- then split the single compensating translation between the two jump factors.
  simp only [stableCompensatedPoissonMeasure_def, sub_eq_add_neg]
  rw [← Measure.conv_dirac, hcp, hcenter, neg_add, ← Measure.dirac_conv_dirac]
  simp only [← Measure.conv_dirac, ← Measure.conv_assoc]
  congr 1
  rw [Measure.conv_assoc, Measure.conv_comm _ (Measure.dirac _), ← Measure.conv_assoc]

end TauCeti.Probability
