/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Lebesgue.Cumulative
public import TauCeti.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Predictable accumulated energy and finite-energy cutoffs

A nonnegative progressive process has an adapted cumulative lower integral on its original
filtration. Under an atomless time measure its extended-valued paths are left-continuous,
hence predictable. Neither local finiteness of the integral nor usual conditions on the
filtration are required.

For a predictable real process `H`, this makes the set where its accumulated square energy
is finite predictable. Cutting `H` off on the complement therefore preserves predictability,
and changes no values up to a horizon with finite square energy. The lower integral retains
infinite energy instead of the fallback zero of a nonintegrable Bochner integral. This is the
measurability step needed before constructing energy-level stopping times; no continuity of
the repaired energy clock or stochastic-integral construction is asserted here.

The results allow any s-finite atomless time measure; for Brownian integration use
Lebesgue measure pulled back from `ℝ` to `ℝ≥0`. The closed initial segment can be replaced
by `(0,t]`, since the time-zero singleton is null.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {Ω : Type*}

/-- Square energy accumulated up to time `t`, retaining infinite energy as an extended value.
Under an atomless time measure the time-zero contribution vanishes. -/
def accumulatedEnergy (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Iic t, ‖H s ω‖ₑ ^ 2 ∂μ

theorem accumulatedEnergy_def (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → ℝ) :
    accumulatedEnergy μ H = fun t ω ↦ ∫⁻ s in Iic t, ‖H s ω‖ₑ ^ 2 ∂μ := (rfl)

/-- Accumulated square energy is nondecreasing on every path. -/
theorem monotone_accumulatedEnergy (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Monotone (fun t ↦ accumulatedEnergy μ H t ω) := by
  intro s t hst
  exact lintegral_mono_set (Iic_subset_Iic.mpr hst)

/-- Accumulated energy has left-continuous extended-valued paths for an atomless time
measure, whether or not those paths remain finite. -/
theorem isLeftContinuous_accumulatedEnergy (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (H : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    IsLeftContinuous (fun t ↦ accumulatedEnergy μ H t ω) := by
  simpa only [accumulatedEnergy_def] using
    isLeftContinuous_setLIntegral_Iic μ (fun s ↦ ‖H s ω‖ₑ ^ 2)

/-- Accumulated energy starts at zero for an atomless time measure. -/
@[simp]
theorem accumulatedEnergy_zero (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (H : ℝ≥0 → Ω → ℝ) (ω : Ω) : accumulatedEnergy μ H 0 ω = 0 := by
  have hI : Iic (0 : ℝ≥0) = {0} := by ext s; simp
  simp [accumulatedEnergy_def, hI]

/-- A process cut off when its accumulated square energy is infinite. This is a predictable
cutoff for a predictable input and an s-finite atomless time measure. -/
def finiteEnergyCutoff (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if accumulatedEnergy μ H t ω < ∞ then H t ω else 0

theorem finiteEnergyCutoff_def (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → ℝ) :
    finiteEnergyCutoff μ H = fun t ω ↦
      if accumulatedEnergy μ H t ω < ∞ then H t ω else 0 := (rfl)

/-- The cutoff does not change a value with finite accumulated energy. -/
@[simp]
theorem finiteEnergyCutoff_of_lt_top {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → ℝ}
    {t : ℝ≥0} {ω : Ω} (h : accumulatedEnergy μ H t ω < ∞) :
    finiteEnergyCutoff μ H t ω = H t ω := by
  simp [finiteEnergyCutoff_def, h]

/-- The cutoff vanishes at an infinite accumulated energy. -/
@[simp]
theorem finiteEnergyCutoff_of_eq_top {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → ℝ}
    {t : ℝ≥0} {ω : Ω} (h : accumulatedEnergy μ H t ω = ∞) :
    finiteEnergyCutoff μ H t ω = 0 := by
  simp [finiteEnergyCutoff_def, h]

/-- A finite terminal energy leaves the entire path unchanged up to that horizon. -/
theorem finiteEnergyCutoff_eqOn {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hT : accumulatedEnergy μ H T ω < ∞) :
    EqOn (fun t ↦ finiteEnergyCutoff μ H t ω) (fun t ↦ H t ω) (Iic T) :=
  fun _ ht ↦ finiteEnergyCutoff_of_lt_top ((monotone_accumulatedEnergy μ H ω ht).trans_lt hT)

end MeasureTheory.Measure

namespace MeasureTheory.IsProgressive

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {F : ℝ≥0 → Ω → ℝ≥0∞}

/-- The cumulative lower integral of a progressive nonnegative process is adapted to the
original filtration. Infinite values are permitted and no sample measure is needed. -/
theorem adapted_setLIntegral_Iic (hF : IsProgressive ℱ F) (μ : Measure ℝ≥0) [SFinite μ] :
    Adapted ℱ (fun t ω ↦ ∫⁻ s in Iic t, F s ω ∂μ) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  -- Capping time at the horizon extends the progressive restriction measurably to all times.
  have hg : Measurable[(_ : MeasurableSpace ℝ≥0).prod (ℱ t)]
      (fun p : ℝ≥0 × Ω ↦ F (min p.1 t) p.2) :=
    (hF t).comp (((measurable_fst.min measurable_const).subtype_mk
      (h := fun p : ℝ≥0 × Ω ↦ min_le_right p.1 t)).prodMk measurable_snd)
  convert hg.lintegral_prod_left' (μ := μ.restrict (Iic t)) using 1
  ext ω
  exact setLIntegral_congr_fun measurableSet_Iic fun s hs ↦
    congrArg (fun u ↦ F u ω) (min_eq_left (α := ℝ≥0) hs).symm

/-- Accumulated nonnegative mass is predictable under an atomless time measure, even on
paths where it becomes infinite. -/
theorem isStronglyPredictable_setLIntegral_Iic (hF : IsProgressive ℱ F)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    IsStronglyPredictable ℱ (fun t ω ↦ ∫⁻ s in Iic t, F s ω ∂μ) :=
  (hF.adapted_setLIntegral_Iic μ).stronglyAdapted.isStronglyPredictable_of_isLeftContinuous
    (fun ω ↦ μ.isLeftContinuous_setLIntegral_Iic (fun s ↦ F s ω))

end MeasureTheory.IsProgressive

namespace MeasureTheory.IsStronglyPredictable

open Measure

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {H : ℝ≥0 → Ω → ℝ}
  (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]

/-- The accumulated square energy of a predictable real process is itself predictable as
an extended-nonnegative-valued process. No finite-energy hypothesis is imposed. -/
theorem accumulatedEnergy (hH : IsStronglyPredictable ℱ H) :
    IsStronglyPredictable ℱ (μ.accumulatedEnergy H) := by
  simp only [accumulatedEnergy_def]
  apply IsProgressive.isStronglyPredictable_setLIntegral_Iic (μ := μ)
  intro t
  let : MeasurableSpace Ω := ℱ t
  exact (hH.isStronglyProgressive t).enorm.pow_const 2

/-- The finite-accumulated-energy set is predictable on a raw filtration. -/
theorem measurableSet_finite_accumulatedEnergy (hH : IsStronglyPredictable ℱ H) :
    MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω |
      μ.accumulatedEnergy H p.1 p.2 < ∞} :=
  measurableSet_lt (hH.accumulatedEnergy μ).measurable measurable_const

/-- Removing a predictable integrand after its accumulated square energy becomes infinite
preserves literal predictability, without modifying the filtration. -/
theorem finiteEnergyCutoff (hH : IsStronglyPredictable ℱ H) :
    IsStronglyPredictable ℱ (μ.finiteEnergyCutoff H) := by
  simp only [finiteEnergyCutoff_def]
  exact hH.ite (hH.measurableSet_finite_accumulatedEnergy μ) stronglyMeasurable_zero

end MeasureTheory.IsStronglyPredictable
