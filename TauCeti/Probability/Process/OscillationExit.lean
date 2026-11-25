/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Filtration.Ray
public import TauCeti.Probability.Process.Progressive
public import TauCeti.Topology.Order.Cadlag.OscillationExit
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Oscillation exit stopping times and step-process ray measurability

For a strongly adapted process `X : ι → Ω → E` on a second-countable conditionally complete
linear order with bottom having everywhere càdlàg paths in a pseudometric space `E` and any
threshold `ε > 0`, the pathwise `ε`-oscillation exit time
`TauCeti.oscillationExitAfter (X · ω) ε (τ ω)` after a stopping time `τ` is a stopping time on
the raw filtration `ℱ` (`MeasureTheory.StronglyAdapted.isStoppingTime_oscillationExitAfter`),
assuming neither completeness nor right continuity of `ℱ`, no a priori measurable structure on
`ι`, and neither separability nor algebraic structure on `E`. Iterating from `⊥` gives an
increasing exhausting sequence of stopping times `TauCeti.oscillationExit (X · ω) ε n`
(`MeasureTheory.StronglyAdapted.isStoppingTime_oscillationExit`), proved via right-continuous
strong progressive measurability
(`MeasureTheory.StronglyAdapted.isStronglyProgressive_of_isRightContinuous`)
and specializing immediately to adapted càdlàg processes
(`MeasureTheory.Adapted.isStoppingTime_oscillationExitAfter`,
`MeasureTheory.Adapted.isStoppingTime_oscillationExit`).

Specializing `MeasureTheory.Filtration.measurable_rayMeasurableSpace_of_eq_on_Ico` to the
deterministic step approximation `TauCeti.oscillationApprox` (defined in
`TauCeti.Topology.Order.Cadlag.OscillationExit`) yields joint ray measurability of
`oscillationApprox`
(`MeasureTheory.StronglyAdapted.measurable_rayMeasurableSpace_oscillationApprox`).

## References

* C. Dellacherie and P.-A. Meyer, *Probabilities and Potential*, Chapter IV, Theorem 64 (generation
  of the optional σ-algebra by stopping-time intervals).
* J. Jacod and A. N. Shiryaev, *Limit Theorems for Stochastic Processes*, second edition,
  Chapter I, Proposition 1.21.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

section StoppingTime

variable {ι Ω E : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  [OrderTopology ι] [SecondCountableTopology ι] {m : MeasurableSpace Ω} [PseudoMetricSpace E]
  {ℱ : Filtration ι m} {X : ι → Ω → E}

/-- For a strongly adapted process with everywhere càdlàg paths, the first `ε`-oscillation
exit time (`ε > 0`) after a stopping time `τ` is a stopping time on the raw filtration `ℱ`, with no
right-continuity or completeness assumption on `ℱ` and no separability assumption on `E`. -/
theorem StronglyAdapted.isStoppingTime_oscillationExitAfter
    (hX : StronglyAdapted ℱ X) (hc : ∀ ω, IsCadlag (X · ω))
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime ℱ τ) {ε : ℝ} (hε : 0 < ε) :
    IsStoppingTime ℱ (fun ω ↦ TauCeti.oscillationExitAfter (X · ω) ε (τ ω)) := by
  borelize ι
  have hprog : IsStronglyProgressive ℱ X :=
    hX.isStronglyProgressive_of_isRightContinuous fun ω ↦ (hc ω).isRightContinuous
  intro T
  obtain ⟨S, hSc, hST, hS⟩ :=
    TauCeti.exists_countable_subset_Iic_oscillationExitAfter_le_coe_iff (E := E) T
  have hstop : StronglyAdapted ℱ (MeasureTheory.stoppedProcess X τ) :=
    hprog.stronglyAdapted_stoppedProcess hτ
  have heq : {ω | TauCeti.oscillationExitAfter (X · ω) ε (τ ω) ≤ (T : WithTop ι)} =
      (fun ω ↦ ⨆ s ∈ S, edist (X s ω) (MeasureTheory.stoppedProcess X τ s ω)) ⁻¹'
        Ici (ENNReal.ofReal ε) := by
    ext ω
    simpa only [mem_ofPred_eq, mem_preimage, mem_Ici, MeasureTheory.stoppedProcess] using
      hS (hc ω) hε (τ ω)
  rw [heq]
  let _ : MeasurableSpace Ω := ℱ T
  refine Measurable.biSup S hSc (fun s hs ↦ ?_) measurableSet_Ici
  have hsT : s ≤ T := hST hs
  exact (((hX s).mono (ℱ.mono hsT)).edist ((hstop s).mono (ℱ.mono hsT))).measurable

/-- Iterated `ε`-oscillation exit times (`ε > 0`) of a strongly adapted càdlàg process are stopping
times on the raw filtration `ℱ`. -/
theorem StronglyAdapted.isStoppingTime_oscillationExit
    (hX : StronglyAdapted ℱ X) (hc : ∀ ω, IsCadlag (X · ω)) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ TauCeti.oscillationExit (X · ω) ε n) := by
  induction n with
  | zero => simpa only [TauCeti.oscillationExit_zero] using isStoppingTime_const ℱ (⊥ : ι)
  | succ n ih =>
    simpa only [TauCeti.oscillationExit_succ] using
      hX.isStoppingTime_oscillationExitAfter hc ih hε

/-- For an adapted càdlàg process in a second-countable pseudometric space with measurable open
sets, the first `ε`-oscillation exit time (`ε > 0`) after a stopping time `τ` is a stopping time on
the raw filtration `ℱ`. -/
theorem Adapted.isStoppingTime_oscillationExitAfter
    [SecondCountableTopology E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (hX : Adapted ℱ X) (hc : ∀ ω, IsCadlag (X · ω))
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime ℱ τ) {ε : ℝ} (hε : 0 < ε) :
    IsStoppingTime ℱ (fun ω ↦ TauCeti.oscillationExitAfter (X · ω) ε (τ ω)) :=
  hX.stronglyAdapted.isStoppingTime_oscillationExitAfter hc hτ hε

/-- Iterated `ε`-oscillation exit times (`ε > 0`) of an adapted càdlàg process in a
second-countable pseudometric space with measurable open sets are stopping times on the raw
filtration `ℱ`. -/
theorem Adapted.isStoppingTime_oscillationExit
    [SecondCountableTopology E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (hX : Adapted ℱ X) (hc : ∀ ω, IsCadlag (X · ω)) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ TauCeti.oscillationExit (X · ω) ε n) :=
  hX.stronglyAdapted.isStoppingTime_oscillationExit hc hε n

end StoppingTime

/-- For a strongly adapted càdlàg process in a pseudometric Borel space and `ε > 0`, the pathwise
step approximation `fun p ↦ TauCeti.oscillationApprox (X · p.2) ε p.1` is measurable with respect
to `ℱ.rayMeasurableSpace` on the raw filtration `ℱ`. -/
theorem StronglyAdapted.measurable_rayMeasurableSpace_oscillationApprox
    {ι Ω E : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] {m : MeasurableSpace Ω}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {ℱ : Filtration ι m} {X : ι → Ω → E}
    (hX : StronglyAdapted ℱ X) (hc : ∀ ω, IsCadlag (X · ω)) {ε : ℝ} (hε : 0 < ε) :
    Measurable[ℱ.rayMeasurableSpace]
      (fun p : ι × Ω ↦ TauCeti.oscillationApprox (X · p.2) ε p.1) := by
  borelize ι
  have hprog : IsStronglyProgressive ℱ X :=
    hX.isStronglyProgressive_of_isRightContinuous fun ω ↦ (hc ω).isRightContinuous
  let τ (n : ℕ) (ω : Ω) : WithTop ι := TauCeti.oscillationExit (X · ω) ε n
  have hτ (n : ℕ) : IsStoppingTime ℱ (τ n) := hX.isStoppingTime_oscillationExit hc hε n
  exact Filtration.measurable_rayMeasurableSpace_of_eq_on_Ico hτ
    (fun t ω ↦ (hc ω).exists_mem_Ico_oscillationExit hε t)
    (fun n ↦ measurable_stoppedValue hprog (hτ n))
    (Z := fun t ω ↦ TauCeti.oscillationApprox (X · ω) ε t)
    (fun _ _ _ hle hlt ↦ TauCeti.oscillationApprox_eq_of_mem_Ico hle hlt)

end MeasureTheory
