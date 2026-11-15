/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
public import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Support of interval-truncated normal laws

At positive variance, the topological support of an interval-truncated normal law is the
closed interval between its extended bounds. This includes both finite endpoints even when
the truncation excludes them, as well as one-sided and unbounded intervals.

At zero variance the support is the singleton containing the Gaussian location if the
truncation retains it, and empty otherwise. Endpoint conventions therefore matter at this
boundary. The theorem covers all four interval conventions through inclusions between the
open and closed intervals.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

open Classical in
/-- The support of a normal law truncated between extended bounds `l < r`. At positive
variance it is the closed interval, independently of endpoint conventions. At zero variance
it is `{m}` or empty according to whether the truncation retains the location. -/
theorem support_truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) {s : Set ℝ} {l r : EReal}
    (hlr : l < r) (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s)
    (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    (truncatedNormalMeasure m v s).support =
      if v = 0 then if m ∈ s then {m} else ∅ else Real.toEReal ⁻¹' Icc l r := by
  by_cases hv : v = 0
  · subst v
    by_cases hm : m ∈ s <;> simp [hm, Measure.support_dirac]
  rw [ite_eq_right hv]
  have := nullSingletonClass_gaussianReal (μ := m) hv
  have := (gaussianReal_absolutelyContinuous' m hv).isOpenPosMeasure
  have hsame : s =ᵐ[gaussianReal m v] Real.toEReal ⁻¹' Ioo l r :=
    ((gaussianReal m v).ae_eq_preimage_Ioc hs₁ hs₂).trans
      ((gaussianReal m v).ae_eq_preimage_Ioc subset_rfl
        (preimage_mono Ioo_subset_Icc_self)).symm
  rw [truncatedNormalMeasure_def, cond_congr_ae hsame, ProbabilityTheory.cond,
    Measure.support_smul_measure _ _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)),
    Measure.support_restrict_of_isOpen _ (isOpen_Ioo.preimage continuous_coe_real_ereal)]
  rw [← EReal.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_coe_real_ereal, closure_Ioo hlr.ne]

end TauCeti.Probability
