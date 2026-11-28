/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.GaussianSum.Basic
public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic

import TauCeti.Analysis.Normed.Module.RademacherSum.Contraction
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Probability.Distributions.Gaussian.CoordinateTails
import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Truncated Gaussian sums and Rademacher comparison

Splitting each standard Gaussian coordinate `gᵢ` at a threshold `t` decomposes a Gaussian sum
into a coordinatewise truncation `EuclideanSpace.truncVec t g` and a tail
`EuclideanSpace.tailVec t g`. Without any cotype assumption on the target normed space `Y`, the
`L²` Minkowski inequality gives `G₂(y) ≤ ‖trunc‖₂ + ‖tail‖₂`, and sign-flip invariance together
with Rademacher contraction bounds the truncated term by `t * R₂(y)` whenever `0 ≤ t`.

## Main declarations

* `TauCeti.integral_norm_sq_truncVec_le`: `𝔼[‖∑ i, truncVec t g i • y i‖²] ≤ (t * R₂(y))²`
  for `0 ≤ t`.
* `TauCeti.gaussianSecondMoment_le_truncVec_add_tailVec`: splits `G₂(y)` into its truncated and tail
  `L²` norms.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace TauCeti

variable {ι Y : Type*} [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Sign-flip invariance and Rademacher contraction bound the truncated Gaussian sum by
`t * R₂(y)`. -/
theorem integral_norm_sq_truncVec_le [DecidableEq ι] (y : ι → Y) {t : ℝ} (ht : 0 ≤ t) :
    ∫ g, ‖∑ i, EuclideanSpace.truncVec t g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      (t * rademacherSecondMoment y) ^ 2 := by
  have hint : Integrable (fun g : EuclideanSpace ℝ ι ↦
        ‖∑ i, EuclideanSpace.truncVec t g i • y i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [gaussianSumCLM_apply] using
      ((gaussianSumCLM y).memLp_comp_truncVec t (by simp)).integrable_norm_pow two_ne_zero
  rw [Probability.integral_eq_integral_expect_signFlip hint]
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ Finset.expect_nonneg fun _ _ ↦
    sq_nonneg _) (integrable_const ((t * rademacherSecondMoment y) ^ 2))
    (ae_of_all _ fun g ↦ ?_)).trans_eq (by simp)
  have h := pow_le_pow_left₀ (rademacherSecondMoment_nonneg _)
    (rademacherSecondMoment_smul_le (EuclideanSpace.abs_truncVec_apply_le ht g) y) 2
  rw [rademacherSecondMoment_sq] at h
  refine h.trans_eq' (Finset.expect_congr rfl fun ε _ ↦ ?_)
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Probability.truncVec_signFlip, smul_assoc]

/-- The `L²` Minkowski triangle inequality splits `G₂(y)` into its truncated and tail parts. -/
theorem gaussianSecondMoment_le_truncVec_add_tailVec (y : ι → Y) (t : ℝ) :
    gaussianSecondMoment y ≤
      √(∫ g, ‖∑ i, EuclideanSpace.truncVec t g i • y i‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)) +
        √(∫ g, ‖∑ i, EuclideanSpace.tailVec t g i • y i‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)) := by
  have hsplit (g : EuclideanSpace ℝ ι) : ∑ i, g i • y i =
      ((fun g ↦ gaussianSumCLM y (EuclideanSpace.truncVec t g)) +
        (fun g ↦ gaussianSumCLM y (EuclideanSpace.tailVec t g))) g := by
    rw [Pi.add_apply, ← (gaussianSumCLM y).map_add, EuclideanSpace.truncVec_add_tailVec,
      gaussianSumCLM_apply]
  simp_rw [← gaussianSumCLM_apply y]
  rw [gaussianSecondMoment_def]
  simp_rw [hsplit]
  exact ((gaussianSumCLM y).memLp_comp_truncVec t (by simp)).sqrt_integral_norm_add_sq_le
    ((gaussianSumCLM y).memLp_comp_tailVec t (by simp))

end TauCeti
