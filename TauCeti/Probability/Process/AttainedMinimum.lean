/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Topology.Order.SequenceMinimum

/-!
# Attained minima of stopping times on raw filtrations

A countable family of stopping times has a stopping-time minimum if the value is
set to infinity on paths where no member is least. Unlike an unrestricted
countable infimum, this construction needs no right continuity of the filtration.
Its range is countable whenever the candidate ranges are countable.

For grid localizers, almost-sure attainment follows from converging lower barriers
and summable probabilities of missing an upper barrier. The resulting stopping
time agrees almost surely with the ordinary infimum; the fallback is retained on
exceptional paths rather than changing the process on a possibly unobservable
null set. Barrier measurability is not required: the probability bound uses outer
measure, as does the Borel–Cantelli lemma.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Chapter 1, §5, and Chapter 3, §2.D, for localization.

The stopping-time proof uses Mathlib's comparison events in the stopping
sigma-algebra, `MeasureTheory.IsStoppingTime.measurableSet_le_stopping_time`.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

section LinearOrder

variable {Ω ι κ : Type*} [LinearOrder ι] (τ : κ → Ω → WithTop ι)

/-- The least candidate value on each path, or infinity if no candidate is least.
In particular, the empty family has attained minimum infinity. -/
noncomputable def attainedMin (ω : Ω) : WithTop ι := by
  classical
  exact if h : ∃ i, ∀ j, τ i ω ≤ τ j ω then τ h.choose ω else ⊤

/-- An attained least candidate determines the value of `attainedMin`. -/
theorem attainedMin_eq_of_forall_le {ω : Ω} {i : κ}
    (hi : ∀ j, τ i ω ≤ τ j ω) : attainedMin τ ω = τ i ω := by
  classical
  have hex : ∃ i, ∀ j, τ i ω ≤ τ j ω := ⟨i, hi⟩
  simp only [attainedMin, dite_eq_left hex]
  exact le_antisymm (hex.choose_spec i) (hi hex.choose)

/-- If no candidate is least, the attained minimum is infinity. -/
theorem attainedMin_eq_top_of_not_exists {ω : Ω}
    (h : ¬ ∃ i, ∀ j, τ i ω ≤ τ j ω) : attainedMin τ ω = ⊤ := by
  classical
  simp only [attainedMin, dite_eq_right h]

/-- The attained minimum is infinity exactly when every least candidate is infinity.
This includes the case in which no candidate is least. -/
@[simp] theorem attainedMin_eq_top_iff {ω : Ω} :
    attainedMin τ ω = ⊤ ↔ ∀ i, (∀ j, τ i ω ≤ τ j ω) → τ i ω = ⊤ := by
  constructor
  · intro h i hi
    rwa [attainedMin_eq_of_forall_le τ hi] at h
  · intro h
    by_cases hex : ∃ i, ∀ j, τ i ω ≤ τ j ω
    · exact (attainedMin_eq_of_forall_le τ hex.choose_spec).trans
        (h hex.choose hex.choose_spec)
    · exact attainedMin_eq_top_of_not_exists τ hex

/-- Countable candidate ranges give a countable attained-minimum range. -/
theorem countable_range_attainedMin [Countable κ]
    (hcount : ∀ i, (range (τ i)).Countable) : (range (attainedMin τ)).Countable := by
  have hrange : range (attainedMin τ) ⊆ insert ⊤ (⋃ i, range (τ i)) := by
    rintro _ ⟨ω, rfl⟩
    by_cases hex : ∃ i, ∀ j, τ i ω ≤ τ j ω
    · rw [attainedMin_eq_of_forall_le τ hex.choose_spec]
      exact mem_insert_of_mem _ (mem_iUnion.2 ⟨hex.choose, ⟨ω, rfl⟩⟩)
    · rw [attainedMin_eq_top_of_not_exists τ hex]
      exact mem_insert _ _
  exact ((countable_iUnion hcount).insert ⊤).mono hrange

/-- The attained minimum of a countable family of stopping times is a stopping time
on the original filtration, without completeness or right continuity. -/
theorem isStoppingTime_attainedMin [MeasurableSpace Ω]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [Countable κ] {F : Filtration ι ‹MeasurableSpace Ω›}
    (hτ : ∀ i, IsStoppingTime F (τ i)) : IsStoppingTime F (attainedMin τ) := by
  classical
  intro t
  have hevent : {ω | attainedMin τ ω ≤ t} =
      ⋃ i, {ω | ∀ j, τ i ω ≤ τ j ω} ∩ {ω | τ i ω ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      by_cases hex : ∃ i, ∀ j, τ i ω ≤ τ j ω
      · exact ⟨hex.choose, hex.choose_spec,
          (attainedMin_eq_of_forall_le τ hex.choose_spec) ▸ h⟩
      · rw [attainedMin_eq_top_of_not_exists τ hex] at h
        exact (WithTop.not_top_le_coe t h).elim
    · rintro ⟨i, hi, hit⟩
      rwa [attainedMin_eq_of_forall_le τ hi]
  rw [hevent]
  refine MeasurableSet.iUnion fun i => ?_
  have hm : MeasurableSet[(hτ i).measurableSpace] {ω | ∀ j, τ i ω ≤ τ j ω} := by
    simpa only [ofPred_forall] using
      MeasurableSet.iInter fun j => (hτ i).measurableSet_le_stopping_time (hτ j)
  exact ((hτ i).measurableSet _).1 hm |>.2 t

end LinearOrder

/-- The ordinary infimum is at most the attained minimum, including on paths where
no candidate is least and the attained minimum is infinity. -/
theorem iInf_le_attainedMin {Ω ι κ : Type*} [ConditionallyCompleteLinearOrder ι]
    (τ : κ → Ω → WithTop ι) (ω : Ω) : (⨅ i, τ i ω) ≤ attainedMin τ ω := by
  by_cases hex : ∃ i, ∀ j, τ i ω ≤ τ j ω
  · rw [attainedMin_eq_of_forall_le τ hex.choose_spec]
    exact ciInf_le ⟨τ hex.choose ω, forall_mem_range.2 hex.choose_spec⟩ hex.choose
  · rw [attainedMin_eq_top_of_not_exists τ hex]
    exact le_top

/-- Converging lower barriers and summable upper-barrier misses make the attained
minimum equal almost surely to the ordinary infimum and bounded by the upper
barrier. No measurability of the barriers or completion of the measure is needed. -/
theorem ae_attainedMin_eq_iInf_and_le
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    {τ b : ℕ → Ω → WithTop ι} {c : Ω → WithTop ι}
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => b n ω) atTop (𝓝 (c ω)))
    (hbound : ∀ᵐ ω ∂P, ∀ n, b n ω ≤ τ n ω)
    (hmiss : (∑' n, P {ω | c ω < τ n ω}) ≠ ∞) :
    ∀ᵐ ω ∂P, attainedMin τ ω = ⨅ n, τ n ω ∧ attainedMin τ ω ≤ c ω := by
  have hevent := ae_eventually_notMem hmiss
  filter_upwards [hlim, hbound, hevent] with ω hlimω hboundω heventω
  have hle : ∀ᶠ n in atTop, τ n ω ≤ c ω := by
    simpa only [mem_ofPred_eq, not_lt] using heventω
  obtain ⟨i, hic, himin⟩ := hlimω.exists_le_and_forall_le_of_le hboundω hle.frequently
  rw [attainedMin_eq_of_forall_le τ himin]
  exact ⟨le_antisymm (le_ciInf himin)
    (ciInf_le ⟨τ i ω, forall_mem_range.2 himin⟩ i), hic⟩

end TauCeti
