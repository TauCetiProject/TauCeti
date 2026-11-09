/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
import TauCeti.Probability.Distributions.Stable.LargeJumps
import TauCeti.Probability.Distributions.Stable.SmallJump.Limit
import TauCeti.Probability.Distributions.Stable.Operations
import TauCeti.Probability.Distributions.Affine
import TauCeti.MeasureTheory.Group.Convolution.Integrable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Means of scalar stable laws

A positive-scale stable law has a finite first moment exactly when its shape exceeds one.
In that range its mean is `stableS1Location`, which includes the location correction required
by Nolan's `S₀` convention. Zero-scale laws have mean equal to their location at every valid
shape.

The first-moment criterion follows from the independent large-jump/small-jump decomposition:
the large-jump factor has the sharp Pareto moment threshold, and the small-jump factor has a
finite second moment. The mean is identified by the derivative at zero of the characteristic
function, using Mathlib's `iteratedDeriv_charFun_zero`.

## Main results

* `TauCeti.Probability.integrable_id_stableMeasure_iff` gives the exact first-moment criterion.
* `TauCeti.Probability.integral_id_stableMeasure` identifies the mean for shape greater than one.
* `TauCeti.Probability.integral_of_hasLaw_stableMeasure` gives the random-variable form.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Topology

namespace TauCeti.Probability

variable {α β : ℝ}

private theorem integrable_id_stableMeasure_one_zero_iff (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) : Integrable id (stableMeasure α β 1 0) ↔ 1 < α := by
  obtain ⟨ρ, hρ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure α β 1
  have hsmall : Integrable id (ρ : Measure ℝ) :=
    (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq hα hβ (by norm_num) hρ).integrable
      (by norm_num)
  have hlarge : Integrable id (stableCompensatedPoissonMeasure α β 1) ↔ 1 < α := by
    rw [← integrable_norm_iff aestronglyMeasurable_id]
    simpa only [Real.rpow_one, Real.norm_eq_abs, id_eq] using
      integrable_abs_rpow_stableCompensatedPoissonMeasure_iff hα hβ
        (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  rw [← hρ, Measure.integrable_id_conv_iff _ _ (IsProbabilityMeasure.ne_zero _)
    (IsProbabilityMeasure.ne_zero _), and_iff_right hsmall, hlarge]

/-- A valid scalar stable law has a finite first moment exactly when its scale is zero or
its shape is greater than one. This includes Gaussian and Dirac laws. -/
@[simp]
theorem integrable_id_stableMeasure_iff (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m : ℝ) :
    Integrable id (stableMeasure α β s m) ↔ s = 0 ∨ 1 < α := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [stableMeasure_zero_scale hα hβ]
    simp only [true_or, iff_true]
    exact integrable_dirac (by simp)
  rcases hα.2.eq_or_lt with rfl | hα2
  · rw [stableMeasure_two hβ]
    simp only [show (1 : ℝ) < 2 by norm_num, or_true, iff_true]
    exact (memLp_id_gaussianReal 1).integrable (by norm_num)
  have hmap : (stableMeasure α β 1 0).map (fun x ↦ m + (s : ℝ) * x) =
      stableMeasure α β s m := by
    simpa [Real.sign_of_pos (NNReal.coe_pos.mpr hs), Real.nnnorm_of_nonneg s.2] using
      (stableMeasure_map_affine (α := α) (β := β) (s := 1) (m := 0) (a := m)
        (b := (s : ℝ)) (Or.inl (NNReal.coe_ne_zero.mpr hs.ne')))
  rw [← hmap, ← memLp_one_iff_integrable,
    memLp_id_map_affine_iff (NNReal.coe_ne_zero.mpr hs.ne'), memLp_one_iff_integrable,
    integrable_id_stableMeasure_one_zero_iff ⟨hα.1, hα2⟩ hβ]
  simp [hs.ne']

private theorem hasDerivWithinAt_charFun_stableMeasure_zero (hα : 1 < α)
    (hα2 : α ≤ 2) (hβ : |β| ≤ 1) (s : ℝ≥0) (m : ℝ) :
    HasDerivWithinAt (charFun (stableMeasure α β s m))
      ((stableS1Location α β s m : ℂ) * Complex.I) (Ioi 0) 0 := by
  have hp : HasDerivAt (fun t : ℝ ↦ ((s : ℝ) * t) ^ α) 0 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul (s : ℝ)).rpow_const
      (Or.inr hα.le) using 1 <;> simp [Real.zero_rpow (sub_pos.mpr hα).ne']
  have hg : HasDerivAt (fun t : ℝ ↦ Complex.exp
      ((-((s : ℝ) * t) ^ α : ℝ) +
        ((stableS1Location α β s m * t +
          β * ((s : ℝ) * t) ^ α * tan (π * α / 2) : ℝ) : ℂ) * Complex.I))
      ((stableS1Location α β s m : ℂ) * Complex.I) 0 := by
    simpa [Real.zero_rpow (by linarith : α ≠ 0)] using
      (((hp.neg.ofReal_comp).add
        ((((hasDerivAt_id (0 : ℝ)).const_mul (stableS1Location α β s m)).add
          ((hp.const_mul β).mul_const (tan (π * α / 2)))).ofReal_comp.mul_const
            Complex.I)).cexp)
  apply hg.hasDerivWithinAt.congr
  · intro t ht
    rw [charFun_stableMeasure ⟨by linarith, hα2⟩ hβ,
      stableCharacteristicExponent_add_location_eq_s1_of_ne_one hα.ne'
        (by linarith) β s m t]
    simp [abs_mul, abs_of_pos ht, Real.sign_of_pos ht]
  · simp [charFun_stableMeasure ⟨by linarith, hα2⟩ hβ,
      Real.zero_rpow (by linarith : α ≠ 0)]

/-- For shape greater than one, the mean of a stable law is its `S₁` location. The correction
from its `S₀` location is retained, including at zero scale and Gaussian shape. -/
theorem integral_id_stableMeasure (hα : α ∈ Ioc 1 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m : ℝ) :
    ∫ x, x ∂stableMeasure α β s m = stableS1Location α β s m := by
  have hvalid : α ∈ Ioc 0 2 := ⟨by linarith [hα.1], hα.2⟩
  have hint := (integrable_id_stableMeasure_iff hvalid hβ s m).2 (Or.inr hα.1)
  have hmem : MemLp id 1 (stableMeasure α β s m) := memLp_one_iff_integrable.2 hint
  have hd := ((contDiff_charFun (μ := stableMeasure α β s m) (n := 1)
    (by simpa using hmem)).differentiable (by norm_num) 0).hasDerivAt
  have heq := ((hasDerivWithinAt_charFun_stableMeasure_zero hα.1 hα.2 hβ s m).derivWithin
    (uniqueDiffWithinAt_Ioi 0)).symm.trans
      (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0))
  have hmoment := iteratedDeriv_charFun_zero (μ := stableMeasure α β s m) (n := 1)
    (by simpa using hmem)
  simp only [iteratedDeriv_one, pow_one] at hmoment
  rw [hmoment] at heq
  have him := congrArg Complex.im heq
  simpa using him.symm

/-- A random variable with a stable law of shape greater than one has mean equal to the
law's corrected `S₁` location. -/
theorem integral_of_hasLaw_stableMeasure (hα : α ∈ Ioc 1 2) (hβ : |β| ≤ 1)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {s : ℝ≥0} {m : ℝ} (hX : HasLaw X (stableMeasure α β s m) P) :
    ∫ ω, X ω ∂P = stableS1Location α β s m :=
  hX.integral_eq.trans (integral_id_stableMeasure hα hβ s m)

end TauCeti.Probability
