/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# The unit uniform law as a beta law

The beta law with both shapes equal to one is uniform on the unit interval. This measure
identity lets constructions from beta variables specialize to uniform variables, including
the normalized ratio of two independent exponentials.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The beta law with shapes one and one is the unit interval uniform law. The open and
half-open endpoint conventions agree because the endpoints have zero Lebesgue measure. -/
@[simp]
theorem betaMeasure_one_one : betaMeasure 1 1 = uniformMeasure 0 1 := by
  rw [betaMeasure_eq_withDensity_restrict_Ioo, uniformMeasure_eq_smul]
  simp only [sub_zero, ENNReal.ofReal_one, inv_one, one_smul]
  calc
    (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (betaPDF 1 1) =
        (volume.restrict (Ioo (0 : ℝ) 1)).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp [betaPDF_of_pos_lt_one hx.1 hx.2, beta_one_right one_pos]
    _ = volume.restrict (Ioc (0 : ℝ) 1) := by
      rw [withDensity_one]
      exact Measure.restrict_congr_set Ioo_ae_eq_Ioc

end TauCeti.Probability
