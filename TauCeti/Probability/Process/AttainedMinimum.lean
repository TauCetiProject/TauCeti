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

/-- Select the least member of a countable family of stopping times when one
exists, and infinity otherwise. This is a stopping time on the original filtration,
without completeness or right continuity. The alternatives specify its value on
every path, including paths on which the infimum is not attained. -/
theorem exists_isStoppingTime_attained_minimum {Ω ι κ : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [Countable κ] {F : Filtration ι ‹MeasurableSpace Ω›} {τ : κ → Ω → WithTop ι}
    (hτ : ∀ i, IsStoppingTime F (τ i)) :
    ∃ ρ : Ω → WithTop ι, IsStoppingTime F ρ ∧ ∀ ω,
      (∃ i, ρ ω = τ i ω ∧ ∀ j, τ i ω ≤ τ j ω) ∨
        (ρ ω = ⊤ ∧ ¬ ∃ i, ∀ j, τ i ω ≤ τ j ω) := by
  classical
  let p (ω : Ω) (i : κ) := ∀ j, τ i ω ≤ τ j ω
  let ρ (ω : Ω) := if h : ∃ i, p ω i then τ h.choose ω else ⊤
  have hmin (ω : Ω) (i : κ) (hi : p ω i) : ρ ω = τ i ω := by
    have hex : ∃ j, p ω j := ⟨i, hi⟩
    simp only [ρ, dite_eq_left hex]
    exact le_antisymm (hex.choose_spec i) (hi hex.choose)
  have hnone (ω : Ω) (h : ¬ ∃ i, p ω i) : ρ ω = ⊤ := by
    simp only [ρ, dite_eq_right h]
  refine ⟨ρ, ?_, fun ω => ?_⟩
  · intro t
    have hevent : {ω | ρ ω ≤ t} =
        ⋃ i, {ω | p ω i} ∩ {ω | τ i ω ≤ t} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · intro h
        by_cases hex : ∃ i, p ω i
        · exact ⟨hex.choose, hex.choose_spec, (hmin ω _ hex.choose_spec) ▸ h⟩
        · rw [hnone ω hex] at h
          exact (WithTop.not_top_le_coe t h).elim
      · rintro ⟨i, hi, hit⟩
        rwa [hmin ω i hi]
    rw [hevent]
    refine MeasurableSet.iUnion fun i => ?_
    have hm : MeasurableSet[(hτ i).measurableSpace] {ω | p ω i} := by
      simpa only [p, ofPred_forall] using
        MeasurableSet.iInter fun j => (hτ i).measurableSet_le_stopping_time (hτ j)
    exact ((hτ i).measurableSet _).1 hm |>.2 t
  · by_cases h : ∃ i, p ω i
    · exact Or.inl ⟨h.choose, hmin ω _ h.choose_spec, h.choose_spec⟩
    · exact Or.inr ⟨hnone ω h, h⟩

/-- Converging lower barriers and summable upper-barrier misses give a
countable-range stopping time equal almost surely to the infimum of the candidate
times and bounded by the upper barrier. The candidates and the constructed time
are stopping times for the raw filtration; no null-set completion is used. -/
theorem exists_countable_range_isStoppingTime_ae_eq_iInf
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] {F : Filtration ι ‹MeasurableSpace Ω›}
    {τ b : ℕ → Ω → WithTop ι} {c : Ω → WithTop ι}
    (hτ : ∀ n, IsStoppingTime F (τ n)) (hcount : ∀ n, (range (τ n)).Countable)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => b n ω) atTop (𝓝 (c ω)))
    (hbound : ∀ᵐ ω ∂P, ∀ n, b n ω ≤ τ n ω)
    (hmiss : (∑' n, P {ω | c ω < τ n ω}) ≠ ∞) :
    ∃ ρ : Ω → WithTop ι, IsStoppingTime F ρ ∧ (range ρ).Countable ∧
      ∀ᵐ ω ∂P, ρ ω = ⨅ n, τ n ω ∧ ρ ω ≤ c ω := by
  obtain ⟨ρ, hρ, hvalue⟩ := exists_isStoppingTime_attained_minimum hτ
  have hrange : range ρ ⊆ insert ⊤ (⋃ n, range (τ n)) := by
    rintro _ ⟨ω, rfl⟩
    rcases hvalue ω with ⟨n, hn, _⟩ | ⟨hn, _⟩
    · exact mem_insert_of_mem _ (mem_iUnion.2 ⟨n, ⟨ω, hn.symm⟩⟩)
    · exact hn ▸ mem_insert _ _
  refine ⟨ρ, hρ, ((countable_iUnion hcount).insert ⊤).mono hrange, ?_⟩
  have hevent := ae_eventually_notMem hmiss
  filter_upwards [hlim, hbound, hevent] with ω hlimω hboundω heventω
  have hle : ∀ᶠ n in atTop, τ n ω ≤ c ω := by
    simpa only [mem_ofPred_eq, not_lt] using heventω
  obtain ⟨i, hic, himin⟩ := hlimω.exists_minimum_of_lower_bound hboundω hle.frequently
  have heq : ρ ω = τ i ω := by
    rcases hvalue ω with ⟨j, hj, hjmin⟩ | ⟨_, hnone⟩
    · exact hj.trans (le_antisymm (hjmin i) (himin j))
    · exact (hnone ⟨i, himin⟩).elim
  refine ⟨?_, heq ▸ hic⟩
  rw [heq]
  exact le_antisymm (le_iInf himin) (iInf_le _ i)

end TauCeti
