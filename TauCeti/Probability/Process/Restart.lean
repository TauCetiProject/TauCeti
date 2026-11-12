/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.Process.StoppedValue
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Passing a fixed conditional law to a stopping time

Suppose that, at each deterministic time `s`, a measurable random variable `U s` has a fixed
law independently of a filtration through `s`. The same event identity holds at countable-range
stopping times. For discrete-valued, almost surely right-continuous `U`, it holds at every
stopping time on the event of finiteness, by upward dyadic approximation. No usual-conditions
assumption on the filtration is needed.

The process `U` need not be adapted: for example, `U s` can be the increment over a fixed
duration after `s`. The deterministic conditional-law identity is an explicit hypothesis,
not a consequence of adaptation.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press (2018), Chapter 7, the restart argument for exponential interarrival times.
-/

public section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace MeasureTheory.IsStoppingTime

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {τ : Ω → WithTop ℝ≥0} {U : ℝ≥0 → Ω → β} {μ : Measure β}

/-- On an event of the stopped sigma-algebra where a countable-range stopping time is finite,
the preimage of a measurable set under a stopped measurable process is measurable. The process
need not be adapted. -/
theorem measurableSet_inter_stoppedValue_preimage_of_countable_range
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hm : ∀ s, Measurable (U s))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hfin : ∀ ω ∈ A, τ ω ≠ ⊤) {B : Set β} (hB : MeasurableSet B) :
    MeasurableSet (A ∩ stoppedValue U τ ⁻¹' B) := by
  classical
  let R : Set ℝ≥0 := {s | (s : WithTop ℝ≥0) ∈ range τ}
  have hR : R.Countable := hc.preimage WithTop.coe_injective
  let := hR.to_subtype
  have hevent : A ∩ stoppedValue U τ ⁻¹' B =
      ⋃ s : R, (A ∩ {ω | τ ω = s.val}) ∩ U s.val ⁻¹' B := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hω, hB⟩
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hfin ω hω)
      exact ⟨⟨s, ω, hs.symm⟩, ⟨hω, hs.symm⟩,
        by rwa [stoppedValue_of_eq hs.symm] at hB⟩
    · rintro ⟨s, ⟨hω, hs⟩, hB⟩
      exact ⟨hω, by rwa [stoppedValue_of_eq hs]⟩
  rw [hevent]
  refine .iUnion fun s => ?_
  have hs : MeasurableSet[ℱ s.val] (A ∩ {ω | τ ω = s.val}) :=
    (hτ.measurableSet_inter_eq_iff A s.val).mp
      (hA.inter (hτ.measurableSet_eq_of_countable_range' hc s.val))
  exact (ℱ.le _ _ hs).inter (hm _ hB)

/-- A deterministic fixed conditional law passes to a countable-range stopping time.
Restrict to an event of the stopped sigma-algebra on which the time is finite, so no value
at infinity is used. -/
theorem measure_inter_stoppedValue_preimage_eq_mul_of_countable_range
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hm : ∀ s, Measurable (U s))
    (hdet : ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[ℱ s] A →
      ∀ B, MeasurableSet B → P (A ∩ U s ⁻¹' B) = P A * μ B)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hfin : ∀ ω ∈ A, τ ω ≠ ⊤) {B : Set β} (hB : MeasurableSet B) :
    P (A ∩ stoppedValue U τ ⁻¹' B) = P A * μ B := by
  classical
  let R : Set ℝ≥0 := {s | (s : WithTop ℝ≥0) ∈ range τ}
  have hR : R.Countable := hc.preimage WithTop.coe_injective
  let := hR.to_subtype
  let E (s : R) : Set Ω := A ∩ {ω | τ ω = s.val}
  have hmE (s : R) : MeasurableSet[ℱ s.val] (E s) :=
    (hτ.measurableSet_inter_eq_iff A s.val).mp
      (hA.inter (hτ.measurableSet_eq_of_countable_range' hc s.val))
  have hdisj : Pairwise (Disjoint on E) := by
    intro s u hsu
    exact disjoint_left.mpr fun ω hs hu => hsu (Subtype.ext
      (WithTop.coe_injective (hs.2.symm.trans hu.2)))
  have hcover : (⋃ s : R, E s) = A := by
    ext ω
    simp only [mem_iUnion]
    constructor
    · rintro ⟨_, hs⟩
      exact hs.1
    · intro hω
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hfin ω hω)
      exact ⟨⟨s, ω, hs.symm⟩, hω, hs.symm⟩
  have hevent : A ∩ stoppedValue U τ ⁻¹' B = ⋃ s : R, E s ∩ U s.val ⁻¹' B := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hω, hB⟩
      obtain ⟨s, hs⟩ := mem_iUnion.mp (hcover.symm ▸ hω)
      exact ⟨s, hs, by rwa [stoppedValue_of_eq hs.2] at hB⟩
    · rintro ⟨s, hs, hB⟩
      exact ⟨hs.1, by rwa [stoppedValue_of_eq hs.2]⟩
  have hmI (s : R) : MeasurableSet (E s ∩ U s.val ⁻¹' B) :=
    (ℱ.le _ _ (hmE s)).inter (hm _ hB)
  rw [hevent]
  rw [measure_iUnion (fun s u hsu => (hdisj hsu).mono inter_subset_left inter_subset_left) hmI]
  simp_rw [hdet _ _ (hmE _) _ hB]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hdisj (fun s => ℱ.le _ _ (hmE s)), hcover]

/-- For discrete-valued, almost surely right-continuous variables, a deterministic fixed
conditional law passes to any stopping time, on its finite-time event. Neither adaptation of
`U` nor completeness or right continuity of the filtration is assumed. -/
theorem measure_inter_stoppedValue_preimage_eq_mul [TopologicalSpace β] [DiscreteTopology β]
    [IsFiniteMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hm : ∀ s, Measurable (U s))
    (hrc : ∀ᵐ ω ∂P, ∀ s, ContinuousWithinAt (fun u => U u ω) (Ici s) s)
    (hdet : ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[ℱ s] A →
      ∀ B, MeasurableSet B → P (A ∩ U s ⁻¹' B) = P A * μ B)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) {B : Set β}
    (hB : MeasurableSet B) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩ stoppedValue U τ ⁻¹' B) =
      P (A ∩ {ω | τ ω ≠ ⊤}) * μ B := by
  classical
  let C := A ∩ {ω | τ ω ≠ ⊤}
  have hC : MeasurableSet[hτ.measurableSpace] C :=
    hA.inter (hτ.measurable (measurableSet_singleton ⊤)).compl
  let σ (n : ℕ) (ω : Ω) := TauCeti.dyadicCeilTime n (τ ω)
  let E (n : ℕ) := C ∩ stoppedValue U (σ n) ⁻¹' B
  let F := C ∩ stoppedValue U τ ⁻¹' B
  have hCn (n : ℕ) : MeasurableSet[(hτ.dyadicCeilTime n).measurableSpace] C :=
    hτ.measurableSpace_mono (hτ.dyadicCeilTime n)
      (fun ω => TauCeti.le_dyadicCeilTime n _) _ hC
  have hmEn (n : ℕ) : MeasurableSet (E n) :=
    (hτ.dyadicCeilTime n).measurableSet_inter_stoppedValue_preimage_of_countable_range
      (TauCeti.countable_range_dyadicCeilTime τ n) hm (hCn n)
      (fun ω hω => (TauCeti.dyadicCeilTime_eq_top_iff n _).not.mpr hω.2) hB
  have hEn (n : ℕ) : P (E n) = P C * μ B :=
    (hτ.dyadicCeilTime n).measure_inter_stoppedValue_preimage_eq_mul_of_countable_range
      (TauCeti.countable_range_dyadicCeilTime τ n) hm hdet (hCn n)
      (fun ω hω => (TauCeti.dyadicCeilTime_eq_top_iff n _).not.mpr hω.2) hB
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ F := by
    filter_upwards [hrc] with ω hω
    by_cases hmem : ω ∈ C
    · have hconv := TauCeti.tendsto_stoppedValue_dyadicCeilTime U τ ω hmem.2 (hω _)
      have heq : ∀ᶠ n in atTop, stoppedValue U (σ n) ω = stoppedValue U τ ω := by
        simpa only [nhds_discrete, tendsto_pure] using hconv
      filter_upwards [heq] with n hn
      simp only [E, F, mem_inter_iff, mem_preimage, hn]
    · exact Eventually.of_forall fun n => by simp [E, F, hmem]
  -- The limiting event need only be null-measurable. Use its measurable eventual-event version.
  let L := {ω | ∀ᶠ n in atTop, ω ∈ E n}
  have hmL : MeasurableSet L := by
    have hset : L = ⋃ k : ℕ, ⋂ n : ℕ, ⋂ (_ : k ≤ n), E n := by
      ext ω
      simp [L, eventually_atTop]
    rw [hset]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun _ => hmEn n
  have hLF : L =ᵐ[P] F := by
    filter_upwards [hlim] with ω hω
    exact propext ((eventually_congr hω).trans eventually_const)
  have hconv : Tendsto (fun n => P (E n)) atTop (𝓝 (P L)) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hmL hmEn
    filter_upwards [hlim, hLF] with ω hω hLFω
    simpa only [hLFω] using hω
  have heq : P L = P C * μ B :=
    tendsto_nhds_unique hconv (by simpa only [hEn] using tendsto_const_nhds)
  exact (measure_congr hLF).symm.trans heq

end MeasureTheory.IsStoppingTime
