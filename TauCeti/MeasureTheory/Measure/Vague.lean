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
import Mathlib.MeasureTheory.Integral.CompactlySupported
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Continuity sets and compact sets under vague convergence

Locally finite measures `μs i` converge vaguely to `μ` if `∫ f ∂μs i → ∫ f ∂μ` for every
continuous compactly supported real function `f`. Unlike weak convergence of finite measures,
this allows measures with infinite total mass. This file proves the two parts of the
portmanteau theorem that survive localization:

* the masses converge on relatively compact measurable sets whose boundary has zero limit mass
  (`MeasureTheory.Measure.tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported`);
* the mass of a compact set is upper semicontinuous, `limsup μs i K ≤ μ K`
  (`MeasureTheory.Measure.limsup_measure_le_of_tendsto_integral_compactlySupported`).

Both reduce to the portmanteau theorem for finite measures: weighting by a nonnegative compactly
supported continuous function `χ` turns vague convergence into weak convergence of the finite
measures `χ μs i`
(`MeasureTheory.Measure.tendsto_withDensity_ofReal_of_tendsto_integral_compactlySupported`), and
these agree with `μs i` on the set when `χ` is a cutoff equal to one there
(`MeasureTheory.withDensity_apply_eq_self_of_eqOn_one`).

In the other direction, a mass bound on an open neighbourhood `V` of a compact set `K` passes to
the limit measure of `K` (`IsCompact.measure_le_of_tendsto_integral`). This needs no local
finiteness of the approximating measures and only an `R1Space`: it tests against a compactly
supported cutoff whose integral lies between the masses of `K` and of `V`
(`IsCompact.exists_compactlySupported_measure_le_integral_le`).

## References

* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapter 1 (weak convergence
  of Radon measures).
-/

public section

open Filter Set Topology
open scoped ENNReal CompactlySupported

namespace MeasureTheory.Measure

variable {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [HasOuterApproxClosed X]
  {l : Filter ι} {μs : ι → Measure X} {μ : Measure X}
  [∀ i, IsLocallyFiniteMeasure (μs i)] [IsLocallyFiniteMeasure μ]

omit [T2Space X] [LocallyCompactSpace X] [HasOuterApproxClosed X] in
/-- **Localization of vague convergence.** Weighting by a nonnegative compactly supported
continuous function `χ` turns vague convergence of locally finite measures into weak convergence
of the finite measures `χ μs i`. -/
theorem tendsto_withDensity_ofReal_of_tendsto_integral_compactlySupported
    (h : ∀ f : C_c(X, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)))
    (χ : C(X, ℝ)) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    Tendsto (β := FiniteMeasure X) (fun i ↦ ⟨(μs i).withDensity fun x ↦ ENNReal.ofReal (χ x),
        isFiniteMeasure_withDensity_ofReal
          (χ.continuous.integrable_of_hasCompactSupport hχc).hasFiniteIntegral⟩) l
      (𝓝 ⟨μ.withDensity fun x ↦ ENNReal.ofReal (χ x), isFiniteMeasure_withDensity_ofReal
        (χ.continuous.integrable_of_hasCompactSupport hχc).hasFiniteIntegral⟩) := by
  have hint (ρ : Measure X) (f : X → ℝ) :
      ∫ x, f x ∂ρ.withDensity (fun x ↦ ENNReal.ofReal (χ x)) = ∫ x, χ x * f x ∂ρ := by
    rw [integral_withDensity_eq_integral_toReal_smul χ.continuous.measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hχ0 _), smul_eq_mul]
  refine FiniteMeasure.tendsto_iff_forall_integral_tendsto.2 fun f ↦ ?_
  let g : C_c(X, ℝ) := ⟨χ * f.toContinuousMap, HasCompactSupport.mul_right hχc⟩
  simpa only [FiniteMeasure.toMeasure_mk, hint, g, CompactlySupportedContinuousMap.coe_mk,
    ContinuousMap.mul_apply, BoundedContinuousFunction.coe_toContinuousMap] using h g

/-- Vague convergence implies convergence on relatively compact measurable sets whose
boundary has zero limit mass. The measures need not have finite total mass. -/
theorem tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported
    (h : ∀ f : C_c(X, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)))
    {s : Set X} (hs : MeasurableSet s) (hsc : IsCompact (closure s))
    (hboundary : μ (frontier s) = 0) :
    Tendsto (fun i ↦ μs i s) l (𝓝 (μ s)) := by
  obtain ⟨χ, hχone, hχcomp, -, hχrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hsc isOpen_univ (subset_univ _)
  have hχs : EqOn (fun x ↦ ENNReal.ofReal (χ x)) 1 s := fun x hx ↦ by
    simp [hχone (subset_closure hx)]
  simpa only [FiniteMeasure.toMeasure_mk, withDensity_apply_eq_self_of_eqOn_one hs hχs] using
    FiniteMeasure.tendsto_measure_of_null_frontier_of_tendsto
      (tendsto_withDensity_ofReal_of_tendsto_integral_compactlySupported h χ hχcomp
        fun x ↦ (hχrange x).1)
      ((withDensity_absolutelyContinuous μ _) hboundary)

/-- **Portmanteau theorem for compact sets under vague convergence.** The limit superior of the
masses of a compact set is at most its mass for the limit measure. The measures need not have
finite total mass. -/
theorem limsup_measure_le_of_tendsto_integral_compactlySupported
    (h : ∀ f : C_c(X, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)))
    {K : Set X} (hK : IsCompact K) :
    limsup (fun i ↦ μs i K) l ≤ μ K := by
  obtain ⟨χ, hχone, hχcomp, -, hχrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  have hχK : EqOn (fun x ↦ ENNReal.ofReal (χ x)) 1 K := fun x hx ↦ by simp [hχone hx]
  simpa only [FiniteMeasure.toMeasure_mk,
    withDensity_apply_eq_self_of_eqOn_one hK.isClosed.measurableSet hχK] using
    FiniteMeasure.limsup_measure_closed_le_of_tendsto
      (tendsto_withDensity_ofReal_of_tendsto_integral_compactlySupported h χ hχcomp
        fun x ↦ (hχrange x).1) hK.isClosed

end MeasureTheory.Measure

section CompactMassBound

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
  [OpensMeasurableSpace X]

/-- A compactly supported continuous function whose integral against every measure lies between
the mass of a compact set `K` and the mass of an open neighbourhood `U` of `K`; the lower bound
needs the measure to be finite on compact sets. -/
theorem IsCompact.exists_compactlySupported_measure_le_integral_le {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : C_c(X, ℝ), (∀ (ρ : Measure X) [IsFiniteMeasureOnCompacts ρ],
      ρ K ≤ ENNReal.ofReal (∫ x, f x ∂ρ)) ∧
      ∀ ρ : Measure X, ENNReal.ofReal (∫ x, f x ∂ρ) ≤ ρ U := by
  obtain ⟨f, hf1, hfc, hfU, hfr⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨⟨f, hfc⟩, fun ρ _ ↦ ?_, fun ρ ↦ ?_⟩
  · exact (CompactlySupportedContinuousMap.integrable ⟨f, hfc⟩).measure_le_integral
      (ae_of_all _ fun x ↦ (hfr x).1) fun _ hx ↦ (hf1 hx).ge
  · exact integral_le_measure (fun x _ ↦ (hfr x).2) fun x hx ↦
      (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfU h)).le

/-- Under convergence against compactly supported continuous functions, a mass bound on an
open neighbourhood passes to the measure of a compact subset for the limiting measure. -/
theorem IsCompact.measure_le_of_tendsto_integral {ι : Type*} {l : Filter ι} [NeBot l]
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {σ : ι → Measure X} {C : ℝ≥0∞}
    (hbound : ∀ᶠ i in l, σ i V ≤ C)
    (hlim : ∀ f : C_c(X, ℝ), Tendsto (fun i => ∫ x, f x ∂σ i) l
      (𝓝 (∫ x, f x ∂μ))) : μ K ≤ C := by
  obtain ⟨f, hfK, hfV⟩ := hK.exists_compactlySupported_measure_le_integral_le hV hKV
  exact (hfK μ).trans (le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp (hlim f))
    (hbound.mono fun i hi ↦ (hfV (σ i)).trans hi))

end CompactMassBound
