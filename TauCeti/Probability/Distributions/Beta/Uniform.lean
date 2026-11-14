/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Order.Lattice
import TauCeti.Probability.Distributions.OrderStatistic.Basic

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
  have : IsProbabilityMeasure (uniformMeasure 0 1) :=
    isProbabilityMeasure_uniformMeasure zero_lt_one
  have : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  rw [← Measure.pi_map_piCongrLeft e (fun _ : ι ↦ uniformMeasure 0 1),
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _),
    ← map_orderStatistic_zero_pi_uniformMeasure, map_orderStatistic_zero]
  refine Measure.map_congr (.of_forall fun x ↦ eq_of_forall_le_iff fun c ↦ ?_)
  simp only [Function.comp_apply, Finset.le_inf'_iff, Finset.mem_univ, forall_true_left,
    MeasurableEquiv.coe_piCongrLeft, ← e.forall_congr_right, Equiv.piCongrLeft_apply_apply]

/-- The coordinatewise maximum of a nonempty finite product of unit uniform laws has law
`betaMeasure (Fintype.card ι) 1`. -/
theorem map_max_pi_uniformMeasure {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι ↦ uniformMeasure 0 1).map
      (fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) =
      betaMeasure (Fintype.card ι) 1 := by
  have : IsProbabilityMeasure (uniformMeasure 0 1) :=
    isProbabilityMeasure_uniformMeasure zero_lt_one
  have hn : Fintype.card ι - 1 + 1 = Fintype.card ι := Nat.sub_add_cancel Fintype.card_pos
  let e : Fin (Fintype.card ι - 1 + 1) ≃ ι := (finCongr hn).trans (Fintype.equivFin ι).symm
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) + 1 = Fintype.card ι := by exact_mod_cast hn
  rw [← hcast, ← map_orderStatistic_last_pi_uniformMeasure, map_orderStatistic_last,
    ← Measure.pi_map_piCongrLeft e (fun _ : ι ↦ uniformMeasure 0 1),
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  refine Measure.map_congr (.of_forall fun x ↦ eq_of_forall_ge_iff fun c ↦ ?_)
  simp only [Function.comp_apply, Finset.sup'_le_iff, Finset.mem_univ, forall_true_left,
    MeasurableEquiv.coe_piCongrLeft, ← e.forall_congr_right, Equiv.piCongrLeft_apply_apply]

end TauCeti.Probability
