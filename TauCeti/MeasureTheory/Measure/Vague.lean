/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Continuity sets under vague convergence

Convergence of locally finite measures against continuous compactly supported real functions
implies convergence of their masses on relatively compact measurable continuity sets.
Unlike weak convergence of finite measures, this allows measures with infinite total mass.
The localization uses a compactly supported cutoff equal to one on the set's closure.
-/

public section

open Filter Set Topology
open scoped ENNReal CompactlySupported

namespace MeasureTheory.Measure

variable {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [HasOuterApproxClosed X]
  {l : Filter ι} {μs : ι → Measure X} {μ : Measure X}
  [∀ i, IsLocallyFiniteMeasure (μs i)] [IsLocallyFiniteMeasure μ]

/-- Vague convergence implies convergence on relatively compact measurable sets whose
boundary has zero limit mass. The measures need not have finite total mass. -/
theorem tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported
    (h : ∀ f : C_c(X, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)))
    {s : Set X} (hs : MeasurableSet s) (hsc : IsCompact (closure s))
    (hboundary : μ (frontier s) = 0) :
    Tendsto (fun i ↦ μs i s) l (𝓝 (μ s)) := by
  obtain ⟨χ, hχone, hχcomp, -, hχrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hsc isOpen_univ (subset_univ _)
  let w : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (χ x)
  have hw : Measurable w := χ.continuous.measurable.ennreal_ofReal
  have hfinite (ν : Measure X) [IsLocallyFiniteMeasure ν] :
      IsFiniteMeasure (ν.withDensity w) := by
    apply isFiniteMeasure_withDensity
    exact (lintegral_ofReal_ne_top_iff_integrable χ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ (hχrange x).1)).2
      (χ.continuous.integrable_of_hasCompactSupport hχcomp)
  let νs : ι → FiniteMeasure X := fun i ↦ ⟨(μs i).withDensity w, hfinite (μs i)⟩
  let ν : FiniteMeasure X := ⟨μ.withDensity w, hfinite μ⟩
  have hint (ρ : Measure X) (f : X → ℝ) :
      ∫ x, f x ∂ρ.withDensity w = ∫ x, χ x * f x ∂ρ := by
    rw [integral_withDensity_eq_integral_toReal_smul hw
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [w, ENNReal.toReal_ofReal (hχrange _).1, smul_eq_mul]
  have hn : Tendsto νs l (𝓝 ν) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.2
    intro f
    let g : C_c(X, ℝ) := ⟨χ * f.toContinuousMap, HasCompactSupport.mul_right hχcomp⟩
    simpa only [νs, ν, FiniteMeasure.toMeasure_mk, hint, g,
      CompactlySupportedContinuousMap.coe_mk,
      ContinuousMap.mul_apply, BoundedContinuousFunction.coe_toContinuousMap] using h g
  have heq (ρ : Measure X) : ρ.withDensity w s = ρ s := by
    rw [withDensity_apply _ hs]
    calc
      ∫⁻ x in s, w x ∂ρ = ∫⁻ _ in s, 1 ∂ρ :=
        setLIntegral_congr_fun hs fun x hx ↦ by simp [w, hχone (subset_closure hx)]
      _ = ρ s := by simp
  simpa only [νs, ν, FiniteMeasure.toMeasure_mk, heq] using
    FiniteMeasure.tendsto_measure_of_null_frontier_of_tendsto hn
      ((withDensity_absolutelyContinuous μ w) hboundary)

end MeasureTheory.Measure
