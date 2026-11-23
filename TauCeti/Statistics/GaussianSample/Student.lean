/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Statistics.GaussianSample.Basic
public import TauCeti.Probability.Distributions.StudentT.Quantile

/-!
# Exact size of the two-sided Student test

The Student law of the studentized mean calibrates a two-sided test of the mean of a
Gaussian sample with unknown positive variance. The upper tail of the absolute statistic
at the Student quantile of level `1 - α / 2` has probability `α`.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., §5.3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → (ι → ℝ)} {m : ℝ} {v : ℝ≥0}

/-- With the sample centered at its true mean, the two-sided Student rejection event using
the `1 - α / 2` quantile has probability exactly `α`. -/
theorem HasLaw.measureReal_abs_studentizedMean_gt_quantile
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) (hv : 0 < v)
    (hι : 2 ≤ Fintype.card ι) {α : ℝ} (hα : α ∈ Ioc 0 1) :
    let T := studentTMeasure (Fintype.card ι - 1 : ℕ)
    P.real {ω | T.quantile (1 - α / 2) < |studentizedMean m (X ω)|} = α := by
  let ν : ℝ := (Fintype.card ι - 1 : ℕ)
  let T := studentTMeasure ν
  let q := T.quantile (1 - α / 2)
  have hν : 0 < ν := Nat.cast_pos.mpr (by omega)
  have hT : IsProbabilityMeasure T := isProbabilityMeasure_studentTMeasure hν
  have hlev : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hquant : cdf T q = 1 - α / 2 :=
    T.cdf_quantile (continuous_cdf_studentTMeasure hν) hlev.1 hlev.2
  have hq : 0 ≤ q := by
    have hl : (2⁻¹ : ℝ) ≤ 1 - α / 2 := by linarith [hα.2]
    simpa only [T, q, quantile_studentTMeasure_half] using
      T.monotoneOn_quantile (by norm_num : (2⁻¹ : ℝ) ∈ Ioo 0 1) hlev hl
  have habs := (hasLaw_map (X := fun x : ℝ ↦ |x|) (by fun_prop)).fun_comp
    (hX.studentizedMean_gaussianSample hv hι)
  calc
    P.real {ω | q < |studentizedMean m (X ω)|} = (T.map (|·|)).real (Ioi q) :=
      habs.measureReal_eq (p := fun z ↦ q < z) measurableSet_Ioi
    _ = 1 - cdf (T.map (|·|)) q := by
      rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]
    _ = α := by
      rw [T.cdf_map_abs_of_isNegInvariant hq, hquant]
      ring

end ProbabilityTheory
