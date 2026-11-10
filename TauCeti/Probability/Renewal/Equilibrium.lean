/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.LayerCake
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The equilibrium excess-life distribution

For an interarrival law `F` on the half-line with finite positive extended mean `μ`,
the equilibrium excess-life distribution has density `F((t, ∞)) / μ` for `t > 0`
and zero density for `t ≤ 0`. This file constructs that measure on `ℝ`, proves
normalization, and computes its distribution function. The layer-cake identity
identifies the integral of the tail with the extended mean. The survival function is the
normalized expected truncated gap. Equivalently it is the normalized integral of the shifted
interarrival tail, the forcing term in the renewal equation for the excess tail.

This is the candidate limiting distribution of the residual waiting time in an
ordinary renewal process. Its construction does not require a nonlattice law;
no convergence assertion is made here. Taking the inverse in `ℝ≥0∞` also makes
the infinite-mean case explicit: the resulting measure is zero, not a probability.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*,
  vol. II, second edition, Wiley, 1971, Chapter XI, on the limiting excess life.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- The equilibrium excess-life measure of an interarrival measure `F` on `ℝ≥0`.
It is a probability measure when the extended mean is finite and positive.
The measure lives on `ℝ` and is concentrated on the positive half-line. -/
def equilibriumExcessLaw (F : Measure ℝ≥0) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t =>
    (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ * F {u | t < (u : ℝ)}

/-- The density defining the equilibrium excess-life measure, relative to
Lebesgue measure restricted to the positive half-line. -/
theorem equilibriumExcessLaw_def (F : Measure ℝ≥0) :
    equilibriumExcessLaw F = (volume.restrict (Ioi 0)).withDensity (fun t =>
      (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ * F {u | t < (u : ℝ)}) := (rfl)

/-- Evaluation on a measurable set is the normalized integral of the interarrival tail. -/
theorem equilibriumExcessLaw_apply (F : Measure ℝ≥0) {s : Set ℝ} (hs : MeasurableSet s) :
    equilibriumExcessLaw F s = (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ *
      ∫⁻ t in s ∩ Ioi 0, F {u | t < (u : ℝ)} := by
  have ht : Measurable fun t : ℝ => F {u | t < (u : ℝ)} :=
    Antitone.measurable fun _ _ h => measure_mono fun _ hu => h.trans_lt hu
  rw [equilibriumExcessLaw_def, withDensity_apply _ hs,
    Measure.restrict_restrict hs, lintegral_const_mul _ ht]

/-- The total mass is the inverse extended mean times the extended mean, including
zero and infinite means. -/
@[simp] theorem equilibriumExcessLaw_univ (F : Measure ℝ≥0) :
    equilibriumExcessLaw F univ =
      (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ * (∫⁻ u, (u : ℝ≥0∞) ∂F) := by
  rw [equilibriumExcessLaw_apply F MeasurableSet.univ, univ_inter]
  congr 1
  simpa using (lintegral_eq_lintegral_meas_lt F
    (ae_of_all _ fun u => u.coe_nonneg) measurable_coe_nnreal_real.aemeasurable).symm

/-- Normalization holds precisely for a finite, nonzero extended mean. In particular,
an infinite-mean interarrival law does not give a probability distribution by this formula. -/
theorem isProbabilityMeasure_equilibriumExcessLaw_iff (F : Measure ℝ≥0) :
    IsProbabilityMeasure (equilibriumExcessLaw F) ↔
      (∫⁻ u, (u : ℝ≥0∞) ∂F) ≠ 0 ∧ (∫⁻ u, (u : ℝ≥0∞) ∂F) ≠ ∞ := by
  rw [isProbabilityMeasure_iff, equilibriumExcessLaw_univ]
  constructor
  · intro h
    constructor <;> intro heq <;> simp [heq] at h
  · rintro ⟨hzero, hfin⟩
    exact ENNReal.inv_mul_cancel hzero hfin

/-- With infinite mean the candidate excess-life measure is zero. -/
@[simp] theorem equilibriumExcessLaw_eq_zero_of_mean_eq_top (F : Measure ℝ≥0)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) : equilibriumExcessLaw F = 0 := by
  rw [← Measure.measure_univ_eq_zero, equilibriumExcessLaw_univ, hmean]
  simp

/-- The equilibrium excess-life measure is absolutely continuous with respect to
Lebesgue measure, even if the interarrival law has atoms. -/
theorem equilibriumExcessLaw_absolutelyContinuous (F : Measure ℝ≥0) :
    equilibriumExcessLaw F ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

/-- The equilibrium excess-life measure has no atoms. In particular it has no mass at zero,
even when zero is a genuine possible interarrival time. -/
instance (F : Measure ℝ≥0) : NullSingletonClass (equilibriumExcessLaw F) := by
  rw [equilibriumExcessLaw_def]
  infer_instance

/-- The distribution function in extended nonnegative form. -/
theorem equilibriumExcessLaw_Iic (F : Measure ℝ≥0) (x : ℝ) :
    equilibriumExcessLaw F (Iic x) = (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ *
      ∫⁻ t in Ioc 0 x, F {u | t < (u : ℝ)} := by
  rw [equilibriumExcessLaw_apply F measurableSet_Iic]
  have hset : Iic x ∩ Ioi 0 = Ioc 0 x := by ext; simp [and_comm]
  rw [hset]

/-- There is no mass on the nonpositive half-line. -/
@[simp] theorem equilibriumExcessLaw_Iic_zero (F : Measure ℝ≥0) :
    equilibriumExcessLaw F (Iic 0) = 0 := by
  simp [equilibriumExcessLaw_Iic]

/-- The real distribution function is the integrated tail divided by the extended mean.
Taking the inverse before converting to `ℝ` also covers infinite mean without treating a
nonintegrable Bochner integral as an expectation. -/
theorem equilibriumExcessLaw_real_Iic (F : Measure ℝ≥0) [IsFiniteMeasure F] (x : ℝ) :
    (equilibriumExcessLaw F).real (Iic x) = ((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal *
      ∫ t in Ioc 0 x, F.real {u | t < (u : ℝ)} := by
  have ht : Measurable fun t : ℝ => F {u | t < (u : ℝ)} :=
    Antitone.measurable fun _ _ h => measure_mono fun _ hu => h.trans_lt hu
  rw [measureReal_def, equilibriumExcessLaw_Iic, ENNReal.toReal_mul,
    ← integral_toReal ht.aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)]
  rfl

/-- Deterministic positive gaps give the uniform equilibrium excess on the interval
between zero and the gap. The equation also holds at gap zero, with both sides zero. -/
theorem equilibriumExcessLaw_dirac (a : ℝ≥0) :
    equilibriumExcessLaw (Measure.dirac a) =
      (a : ℝ≥0∞)⁻¹ • volume.restrict (Ioo 0 (a : ℝ)) := by
  rw [equilibriumExcessLaw_def]
  have hd : (fun t : ℝ => (∫⁻ u, (u : ℝ≥0∞) ∂Measure.dirac a)⁻¹ *
      (Measure.dirac a) {u | t < (u : ℝ)}) =
      (Iio (a : ℝ)).indicator (fun _ => (a : ℝ≥0∞)⁻¹) := by
    funext t
    by_cases h : t < (a : ℝ) <;> simp [h,
      Measure.dirac_apply' _ (measurableSet_lt measurable_const measurable_coe_nnreal_real)]
  rw [hd, withDensity_indicator measurableSet_Iio, withDensity_const,
    Measure.restrict_restrict measurableSet_Iio]
  congr 2
  ext t
  simp [and_comm]

/-- The equilibrium excess tail is the normalized expected truncated gap. This extended
formula also covers infinite interarrival means. -/
theorem equilibriumExcessLaw_Ioi (F : Measure ℝ≥0) (x : ℝ≥0) :
    F.equilibriumExcessLaw (Ioi (x : ℝ)) =
      (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ * ∫⁻ u, ((u - x : ℝ≥0) : ℝ≥0∞) ∂F := by
  rw [equilibriumExcessLaw_apply F measurableSet_Ioi,
    inter_eq_left.2 (Ioi_subset_Ioi x.coe_nonneg)]
  congr 1
  have hm : Measurable fun t : ℝ => F {u | t < (u : ℝ)} :=
    Antitone.measurable fun _ _ h => measure_mono fun _ hu => h.trans_lt hu
  have hpre : (fun t : ℝ => t + x) ⁻¹' Ioi (x : ℝ) = Ioi 0 := by
    ext t
    simp
  have hshift := MeasurePreserving.setLIntegral_comp_preimage (s := Ioi (x : ℝ))
    (measurePreserving_add_right (volume : Measure ℝ) (x : ℝ)) measurableSet_Ioi hm
  rw [hpre] at hshift
  rw [← hshift, ← lintegral_Ioi_tail_add]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  congr 1
  ext u
  simp only [mem_ofPred_eq, mem_Ioi, ← NNReal.coe_lt_coe, NNReal.coe_add,
    Real.coe_toNNReal _ ht.le]

/-- The normalized integral of the excess-tail forcing is exactly the real equilibrium
tail. With finite mean the forcing is integrable by
`integrableOn_Ioi_measureReal_tail_add`; with infinite mean both coefficients are zero. -/
theorem equilibriumExcessLaw_real_Ioi_eq_integral_tail_add (F : Measure ℝ≥0) (x : ℝ≥0) :
    F.equilibriumExcessLaw.real (Ioi (x : ℝ)) =
      ((∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹).toReal *
        ∫ t : ℝ in Ioi 0, F.real (Ioi (t.toNNReal + x)) := by
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞
  · simp [hmean]
  have hm : Measurable fun t : ℝ => F (Ioi (t.toNNReal + x)) :=
    Antitone.measurable fun _ _ h => measure_mono (Ioi_subset_Ioi (by gcongr))
  have htail : (∫⁻ t : ℝ in Ioi 0, F (Ioi (t.toNNReal + x))) ≠ ∞ := by
    rw [lintegral_Ioi_tail_add]
    exact ne_top_of_le_ne_top hmean
      (lintegral_mono fun u => ENNReal.coe_le_coe.mpr (tsub_le_self : u - x ≤ u))
  rw [measureReal_def, equilibriumExcessLaw_Ioi, ENNReal.toReal_mul,
    ← lintegral_Ioi_tail_add, ← integral_toReal hm.aemeasurable
      (ae_lt_top' hm.aemeasurable htail)]
  rfl

end MeasureTheory.Measure
