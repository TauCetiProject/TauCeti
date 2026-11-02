/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
public import TauCeti.Probability.Distributions.Chi.Basic
import TauCeti.Probability.Distributions.Chi.Gaussian
import TauCeti.Probability.Distributions.Folding
import TauCeti.Probability.HasLaw

/-!
# Half-normal laws as one-sided truncated Gaussians

A centered Gaussian conditioned to be nonnegative has the half-normal law, represented by
`chiMeasure 1 (Real.sqrt v)`. More generally, conditioning a Gaussian with mean `m` to be at
least `m` gives this half-normal law translated by `m`. The same identifications hold with
strict inequalities.

The closed-half-line identity requires positive variance: at variance zero the closed half-line
retains the Dirac mass at the mean, whereas the open half-line gives the zero measure. The strict
identity also holds at zero variance, since the chi family has zero measure at scale zero. The
Dirac case is already described by `truncatedNormalMeasure_zero_var`.

The measure identities connect the density, moments and quantiles of the chi family to
one-sided truncation. The random-variable forms condition the original probability space
on the corresponding event.

The centered identity specializes `map_abs_eq_cond_Ici` and `gaussianReal_map_abs`.

## Reference

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  second edition, Wiley, 1994, chapter 13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {v : ℝ≥0}

private theorem truncatedNormalMeasure_zero_Ici (hv : v ≠ 0) :
    truncatedNormalMeasure 0 v (Ici 0) = chiMeasure 1 (Real.sqrt v) := by
  have : (gaussianReal 0 v).IsNegInvariant :=
    ⟨by simpa only [Measure.neg_def, neg_zero] using
      (gaussianReal_map_neg (μ := 0) (v := v))⟩
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  rw [truncatedNormalMeasure_def, ← map_abs_eq_cond_Ici (by simp), gaussianReal_map_abs hv]

/-- A Gaussian truncated below at its mean is a translated half-normal law. At mean zero,
this is the one-degree chi law with scale equal to the standard deviation. -/
@[simp]
theorem truncatedNormalMeasure_Ici_mean (m : ℝ) (hv : v ≠ 0) :
    truncatedNormalMeasure m v (Ici m) =
      (chiMeasure 1 (Real.sqrt v)).map (fun x ↦ m + x) := by
  have h : HasLaw (fun x : ℝ ↦ m + x) (gaussianReal m v) (gaussianReal 0 v) :=
    ⟨by fun_prop, by simpa using (gaussianReal_map_const_add (μ := 0) (v := v) m)⟩
  have hcond := (h.cond (s := Ici m) measurableSet_Ici).map_eq
  have hpre : (fun x : ℝ ↦ m + x) ⁻¹' Ici m = Ici 0 := by
    ext x
    simp
  rw [hpre, ← truncatedNormalMeasure_def, truncatedNormalMeasure_zero_Ici hv,
    ← truncatedNormalMeasure_def] at hcond
  exact hcond.symm

/-- Truncating a Gaussian strictly above its mean gives a translated half-normal law.
At variance zero both sides vanish. -/
@[simp]
theorem truncatedNormalMeasure_Ioi_mean (m : ℝ) (v : ℝ≥0) :
    truncatedNormalMeasure m v (Ioi m) =
      (chiMeasure 1 (Real.sqrt v)).map (fun x ↦ m + x) := by
  by_cases hv : v = 0
  · simp [hv, chiMeasure_of_scale_nonpos]
  have := nullSingletonClass_gaussianReal (μ := m) hv
  rw [truncatedNormalMeasure_def, cond_congr_ae (Ioi_ae_eq_Ici (a := m)),
    ← truncatedNormalMeasure_def, truncatedNormalMeasure_Ici_mean m hv]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
  {m : ℝ} {v : ℝ≥0}

/-- Conditioning a Gaussian variable to be at least its mean gives a translated half-normal
law on the conditioned probability space. -/
theorem HasLaw.cond_ge_mean_gaussianReal (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) :
    HasLaw X ((chiMeasure 1 (Real.sqrt v)).map (fun x ↦ m + x))
      (cond P {ω | m ≤ X ω}) := by
  have h := hX.cond (s := Ici m) measurableSet_Ici
  rwa [← truncatedNormalMeasure_def, truncatedNormalMeasure_Ici_mean m hv] at h

/-- Conditioning a Gaussian variable to be greater than its mean gives a translated half-normal
law. At zero variance the conditioning event is null and both laws vanish. -/
theorem HasLaw.cond_gt_mean_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    HasLaw X ((chiMeasure 1 (Real.sqrt v)).map (fun x ↦ m + x))
      (cond P {ω | m < X ω}) := by
  have h := hX.cond (s := Ioi m) measurableSet_Ioi
  rwa [← truncatedNormalMeasure_def, truncatedNormalMeasure_Ioi_mean m v] at h

end ProbabilityTheory
