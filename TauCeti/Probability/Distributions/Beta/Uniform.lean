/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Relations

/-!
# The unit uniform law and its finite extrema as beta laws

The beta law with both shapes equal to one is uniform on the unit interval, and the coordinatewise
minimum and maximum of `d = Fintype.card ι` independent unit uniforms have beta laws with shapes
`(1, d)` and `(d, 1)`. These measure identities let constructions from beta variables specialize to
uniform variables and their finite extrema.
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

/-- The coordinatewise minimum of a nonempty finite product of unit uniform laws has law
`betaMeasure 1 (Fintype.card ι)`. -/
theorem map_min_pi_uniformMeasure {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι ↦ uniformMeasure 0 1).map
      (fun x ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) =
      betaMeasure 1 (Fintype.card ι) := by
  have _ : IsProbabilityMeasure (uniformMeasure 0 1) :=
    isProbabilityMeasure_uniformMeasure zero_lt_one
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have _ : IsProbabilityMeasure (betaMeasure 1 (Fintype.card ι)) :=
    isProbabilityMeasureBeta one_pos hd
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_map_min_pi_const, cdf_betaMeasure_eq one_pos hd, cdf_uniformMeasure zero_lt_one]
  split_ifs with h0 h1
  · rw [regularizedIncompleteBeta_eq_zero_of_nonpos one_pos.ne' _ h0]
    simp
  · rw [regularizedIncompleteBeta_eq_one_of_one_le zero_le_one hd h1, sub_self,
      zero_pow Fintype.card_ne_zero, sub_zero]
  · push Not at h0 h1
    simp only [sub_zero, div_one]
    rw [regularizedIncompleteBeta_one_left hd h0.le h1.le, Real.rpow_natCast]

/-- The coordinatewise maximum of a nonempty finite product of unit uniform laws has law
`betaMeasure (Fintype.card ι) 1`. -/
theorem map_max_pi_uniformMeasure {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι ↦ uniformMeasure 0 1).map
      (fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) =
      betaMeasure (Fintype.card ι) 1 := by
  have _ : IsProbabilityMeasure (uniformMeasure 0 1) :=
    isProbabilityMeasure_uniformMeasure zero_lt_one
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have _ : IsProbabilityMeasure (betaMeasure (Fintype.card ι) 1) :=
    isProbabilityMeasureBeta hd one_pos
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_map_max_pi_const, cdf_betaMeasure_eq hd one_pos, cdf_uniformMeasure zero_lt_one]
  split_ifs with h0 h1
  · rw [regularizedIncompleteBeta_eq_zero_of_nonpos hd.ne' _ h0, zero_pow Fintype.card_ne_zero]
  · rw [regularizedIncompleteBeta_eq_one_of_one_le hd.le one_pos h1, one_pow]
  · push Not at h0 h1
    simp only [sub_zero, div_one]
    rw [regularizedIncompleteBeta_one_right hd h0.le h1.le, Real.rpow_natCast]

end TauCeti.Probability
