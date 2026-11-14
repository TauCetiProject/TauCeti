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
stopping times in any partially ordered index type. For nonnegative real time and discrete-valued
`U` almost surely right-continuous at the stopping time, it holds on the event of finiteness,
by upward dyadic approximation. No usual-conditions
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
open scoped NNReal ENNReal Topology

namespace MeasureTheory.IsStoppingTime

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace β]
  {P : Measure Ω}

section CountableRange

variable {ι : Type*} [PartialOrder ι] [Nonempty ι] {ℱ : Filtration ι mΩ}
  {τ : Ω → WithTop ι} {U : ι → Ω → β}

/-- A deterministic fixed conditional law passes to a countable-range stopping time.
Restrict to an event of the stopped sigma-algebra on which the time is finite, so no value
at infinity is used. -/
theorem measure_inter_stoppedValue_preimage_eq_mul_of_countable_range
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hm : ∀ s, Measurable (U s)) {B : Set β} (hB : MeasurableSet B) {c : ℝ≥0∞}
    (hdet : ∀ (s : ι) (C : Set Ω), MeasurableSet[ℱ s] C →
      P (C ∩ U s ⁻¹' B) = P C * c)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hfin : ∀ ω ∈ A, τ ω ≠ ⊤) :
    P (A ∩ stoppedValue U τ ⁻¹' B) = P A * c := by
  classical
  let R : Set ι := {s | (s : WithTop ι) ∈ range τ}
  have hR : R.Countable := hc.preimage WithTop.coe_injective
  let := hR.to_subtype
  let E (s : R) : Set Ω := A ∩ {ω | τ ω = s.val}
  have hmE (s : R) : MeasurableSet[ℱ s.val] (E s) :=
    (hτ.measurableSet_inter_eq_iff A s.val).mp
      (hA.inter (by
        simpa only [univ_inter] using (hτ.measurableSet_inter_eq_iff univ s.val).mpr
          (by simpa using hτ.measurableSet_eq_of_countable_range hc s.val)))
  have hdisj : Pairwise (Disjoint on E) := by
    intro s u hsu
    exact disjoint_left.mpr fun ω hs hu => hsu (Subtype.ext
      (WithTop.coe_injective (hs.2.symm.trans hu.2)))
  have hevent (D : Set β) :
      A ∩ stoppedValue U τ ⁻¹' D = ⋃ s : R, E s ∩ U s.val ⁻¹' D := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hω, hD⟩
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hfin ω hω)
      exact ⟨⟨s, ω, hs.symm⟩, ⟨hω, hs.symm⟩,
        by rwa [stoppedValue_of_eq hs.symm] at hD⟩
    · rintro ⟨s, hs, hD⟩
      exact ⟨hs.1, by rwa [stoppedValue_of_eq hs.2]⟩
  have hcover : (⋃ s : R, E s) = A := by simpa using (hevent univ).symm
  have hmI (s : R) : MeasurableSet (E s ∩ U s.val ⁻¹' B) :=
    (ℱ.le _ _ (hmE s)).inter (hm _ hB)
  rw [hevent B]
  rw [measure_iUnion (fun s u hsu => (hdisj hsu).mono inter_subset_left inter_subset_left) hmI]
  simp_rw [hdet _ _ (hmE _)]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hdisj (fun s => ℱ.le _ _ (hmE s)), hcover]

end CountableRange

variable {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {U : ℝ≥0 → Ω → β}

/-- For discrete-valued, almost surely right-continuous variables, a deterministic fixed
conditional law passes to any stopping time, on its finite-time event. Neither adaptation of
`U` nor completeness or right continuity of the filtration is assumed. Right continuity is
needed only at the finite stopped time, and the deterministic identity is needed only for
one fixed measurable target event. -/
theorem measure_inter_stoppedValue_preimage_eq_mul [TopologicalSpace β] [DiscreteTopology β]
    [IsFiniteMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hm : ∀ s, Measurable (U s))
    (hrc : ∀ᵐ ω ∂P, τ ω ≠ ⊤ →
      ContinuousWithinAt (fun u => U u ω) (Ici (τ ω).untopA) (τ ω).untopA)
    {B : Set β} (hB : MeasurableSet B) {c : ℝ≥0∞}
    (hdet : ∀ (s : ℝ≥0) (C : Set Ω), MeasurableSet[ℱ s] C →
      P (C ∩ U s ⁻¹' B) = P C * c)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩ stoppedValue U τ ⁻¹' B) =
      P (A ∩ {ω | τ ω ≠ ⊤}) * c := by
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
    (hτ.measurableSpace_le C hC).inter
      ((hτ.dyadicCeilTime n).measurable_stoppedValue_of_countable_range
        (TauCeti.countable_range_dyadicCeilTime τ n) hm hB)
  have hEn (n : ℕ) : P (E n) = P C * c :=
    (hτ.dyadicCeilTime n).measure_inter_stoppedValue_preimage_eq_mul_of_countable_range
      (TauCeti.countable_range_dyadicCeilTime τ n) hm hB hdet (hCn n)
      (fun ω hω => (TauCeti.dyadicCeilTime_eq_top_iff n _).not.mpr hω.2)
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ F := by
    filter_upwards [hrc] with ω hω
    by_cases hmem : ω ∈ C
    · have hconv := TauCeti.tendsto_stoppedValue_dyadicCeilTime U τ ω hmem.2 (hω hmem.2)
      have heq : ∀ᶠ n in atTop, stoppedValue U (σ n) ω = stoppedValue U τ ω := by
        simpa only [nhds_discrete, tendsto_pure] using hconv
      filter_upwards [heq] with n hn
      simp only [E, F, mem_inter_iff, mem_preimage, hn]
    · exact Eventually.of_forall fun n => by simp [E, F, hmem]
  -- The limiting event need only be null-measurable. Use its measurable eventual-event version.
  let L := liminf E atTop
  have hmL : MeasurableSet L := MeasurableSet.measurableSet_liminf hmEn
  have hLF : L =ᵐ[P] F := by
    filter_upwards [hlim] with ω hω
    exact mem_liminf_iff_eventually_mem.trans ((eventually_congr hω).trans eventually_const)
  have hconv : Tendsto (fun n => P (E n)) atTop (𝓝 (P L)) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hmL hmEn
    filter_upwards [hlim, hLF] with ω hω hLFω
    simpa only [hLFω] using hω
  have heq : P L = P C * c :=
    tendsto_nhds_unique hconv (by simpa only [hEn] using tendsto_const_nhds)
  exact (measure_congr hLF).symm.trans heq

end MeasureTheory.IsStoppingTime
