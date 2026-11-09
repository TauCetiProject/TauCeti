/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Stieltjes
public import TauCeti.Probability.Renewal.Measure
import Mathlib.MeasureTheory.Measure.Sub

/-!
# The Stieltjes measure of the renewal function

The renewal function on the half-line extends by zero to negative real times. For a probability
law `μ` with `μ {0} < 1`, this extension is a real-valued Stieltjes function. Its measure is the
pushforward of `μ ∗ μ.renewalMeasure`, or equivalently of `μ.renewalMeasure - dirac 0`, to the
real line. Pulling it back along the inclusion of the half-line recovers precisely that measure.

The extension is made on `ℝ`, not directly on `ℝ≥0`: a Stieltjes measure on an order with a
least element assigns zero mass to that element. Extending to the real line retains the genuine
arrivals at zero. In particular the atom at zero has mass `μ.renewalFunction 0`, which need not
vanish. This identifies the renewal function with the cumulative measure used in renewal
integrals, including both endpoints of `[0, t]`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (hμ : μ {0} < 1)

include hμ in
private theorem conv_renewalMeasure_map_coe_Iic_ne_top (t : ℝ) :
    ((μ ∗ μ.renewalMeasure).map ((↑) : ℝ≥0 → ℝ)) (Iic t) ≠ ∞ := by
  rw [map_apply measurable_coe_nnreal_real measurableSet_Iic]
  have hfinite := (μ.renewalFunction_lt_top hμ t.toNNReal).ne
  rw [renewalFunction_def] at hfinite
  refine ne_top_of_le_ne_top hfinite (measure_mono ?_)
  intro x hx
  exact NNReal.coe_le_coe.mp (hx.trans (Real.le_coe_toNNReal t))

/-- The real-valued renewal function, extended by zero to negative times and bundled as a
Stieltjes function. The value at zero includes genuine arrivals at zero. -/
def renewalStieltjes : StieltjesFunction ℝ :=
  ((μ ∗ μ.renewalMeasure).map ((↑) : ℝ≥0 → ℝ)).cumulativeStieltjes
    (conv_renewalMeasure_map_coe_Iic_ne_top μ hμ)

/-- On the half-line the Stieltjes function is the real-valued renewal function. -/
@[simp]
theorem renewalStieltjes_coe (t : ℝ≥0) :
    μ.renewalStieltjes hμ t = (μ.renewalFunction t).toReal := by
  have hpreimage : ((↑) : ℝ≥0 → ℝ) ⁻¹' Iic (t : ℝ) = Iic t := by
    ext x
    simp
  rw [renewalStieltjes, cumulativeStieltjes_apply, measureReal_def,
    map_apply measurable_coe_nnreal_real measurableSet_Iic, renewalFunction_def, hpreimage]

/-- The extension vanishes at every negative time. -/
@[simp]
theorem renewalStieltjes_of_neg {t : ℝ} (ht : t < 0) : μ.renewalStieltjes hμ t = 0 := by
  have hempty : ((↑) : ℝ≥0 → ℝ) ⁻¹' Iic t = ∅ := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
    exact not_le.mpr (ht.trans_le x.coe_nonneg)
  simp [renewalStieltjes, measureReal_def,
    map_apply measurable_coe_nnreal_real measurableSet_Iic, hempty]

/-- The Stieltjes measure counts all genuine arrivals, omitting only the artificial arrival
at time zero. This is an equality on the entire real line, with zero mass at negative times. -/
theorem measure_renewalStieltjes :
    (μ.renewalStieltjes hμ).measure =
      (μ ∗ μ.renewalMeasure).map ((↑) : ℝ≥0 → ℝ) := by
  rw [renewalStieltjes, measure_cumulativeStieltjes]

/-- Pulling the Stieltjes measure back to the half-line gives the renewal measure minus its
artificial initial point mass. Genuine arrivals at zero are retained. -/
theorem comap_measure_renewalStieltjes :
    (μ.renewalStieltjes hμ).measure.comap ((↑) : ℝ≥0 → ℝ) =
      μ.renewalMeasure - dirac 0 := by
  rw [measure_renewalStieltjes,
    NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_map]
  conv_rhs => rw [renewalMeasure_eq_dirac_add_conv, add_comm, Measure.add_sub_cancel]

/-- The atom at zero is the renewal function at zero, not necessarily zero. -/
theorem measure_renewalStieltjes_singleton_zero :
    (μ.renewalStieltjes hμ).measure {0} = μ.renewalFunction 0 := by
  rw [measure_renewalStieltjes,
    map_apply measurable_coe_nnreal_real (measurableSet_singleton 0), renewalFunction_def]
  congr 1
  ext x
  simp

end MeasureTheory.Measure
