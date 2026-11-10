/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Authors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Closed-set hitting times of continuous adapted processes

For continuous paths, the first entrance into a closed set is attained whenever it is
finite. On a compact time interval, entrance is equivalent to the minimum distance to
the target being zero. The minimum can be measured through a countable dense set of
times, giving a stopping time on the original filtration, without right continuity or
completion assumptions.

These results apply in particular to exits from open domains and to closed-level
localization of continuous adapted processes. Path continuity here is everywhere,
not merely almost sure; arbitrary null-set changes need not preserve raw adaptation.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, Chapter 1, §2.
-/

public section

open Set Metric MeasureTheory
open scoped ENNReal

variable {Ω ι E : Type*} [ConditionallyCompleteLinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι]

namespace IsClosed

variable [TopologicalSpace E] {X : ι → Ω → E} {s : Set E} {a t : ι} {ω : Ω}

/-- A continuous path attains its first entrance into a closed set, if that entrance is
finite. The returned time is at least the declared starting time. -/
theorem exists_hittingAfter_eq (hs : IsClosed s)
    (hX : Continuous (X · ω)) (hfinite : hittingAfter X s a ω ≠ ⊤) :
    ∃ u : ι, hittingAfter X s a ω = u ∧ a ≤ u ∧ X u ω ∈ s := by
  classical
  have hne : ∃ u, a ≤ u ∧ X u ω ∈ s := by
    by_contra h
    exact hfinite (hittingAfter_eq_top_iff.mpr (by simpa using h))
  have hclosed : IsClosed {u | a ≤ u ∧ X u ω ∈ s} :=
    isClosed_Ici.inter (hs.preimage hX)
  have hmem := hclosed.csInf_mem hne ⟨a, fun _ hu ↦ hu.1⟩
  exact ⟨_, by simp [hittingAfter_def, hne], hmem⟩

/-- For a continuous path and a closed target, entrance by time `t` means that an
actual hit occurs between the starting time and `t`, including both endpoints. -/
theorem hittingAfter_le_iff (hs : IsClosed s) (hX : Continuous (X · ω)) :
    hittingAfter X s a ω ≤ t ↔ ∃ u ∈ Icc a t, X u ω ∈ s := by
  constructor
  · intro h
    obtain ⟨u, hu, hau, hus⟩ := hs.exists_hittingAfter_eq hX
      (ne_top_of_le_ne_top WithTop.coe_ne_top h)
    exact ⟨u, ⟨hau, WithTop.coe_le_coe.mp (hu ▸ h)⟩, hus⟩
  · rintro ⟨u, hu, hus⟩
    exact (hittingAfter_le_of_mem hu.1 hus).trans (WithTop.coe_le_coe.mpr hu.2)

end IsClosed

namespace MeasureTheory

section Stopping

variable [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopology ι] [CompactIccSpace ι]
  {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {X : ι → Ω → E} {s : Set E}

/-- Closed-set entrance of an everywhere-continuous adapted process is a stopping time
on an arbitrary filtration. Neither right continuity nor completeness is required. -/
theorem Adapted.isStoppingTime_hittingAfter_of_isClosed (hX : Adapted ℱ X)
    (hc : ∀ ω, Continuous (X · ω)) (hs : IsClosed s) (a : ι) :
    IsStoppingTime ℱ (hittingAfter X s a) := by
  classical
  intro t
  by_cases hat : a ≤ t
  · let K := Icc a t
    have hK : K.Nonempty := nonempty_Icc.mpr hat
    let : Nonempty K := hK.to_subtype
    have hcont (ω : Ω) : Continuous (fun u : K ↦ infEDist (X u ω) s) :=
      continuous_infEDist.comp ((hc ω).comp continuous_subtype_val)
    have hm : @Measurable Ω ℝ≥0∞ (ℱ t) _
        (fun ω ↦ ⨅ u : K, infEDist (X u ω) s) := by
      have hm' : @Measurable Ω ℝ≥0∞ (ℱ t) _
          (⨅ u : K, fun ω ↦ infEDist (X u ω) s) := by
        apply measurable_iInf_of_upperSemicontinuous
        · intro u
          exact continuous_infEDist.measurable.comp
            ((hX u).mono (ℱ.mono u.property.2) le_rfl)
        · exact fun ω ↦ (hcont ω).upperSemicontinuous
      convert hm' using 1
      exact funext fun ω ↦ (iInf_apply (f := fun (u : K) ω ↦
        infEDist (X u ω) s) (a := ω)).symm
    convert hm (measurableSet_singleton 0) using 1
    ext ω
    rw [mem_ofPred_eq, hs.hittingAfter_le_iff (hc ω)]
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨u, hu, hus⟩
      exact le_antisymm ((iInf_le _ (⟨u, hu⟩ : K)).trans_eq
        (infEDist_zero_of_mem hus)) bot_le
    · intro hz
      obtain ⟨u, _, hmin⟩ := isCompact_univ.exists_isMinOn
        (Set.univ_nonempty : (Set.univ : Set K).Nonempty) (hcont ω).continuousOn
      have hu : infEDist (X u ω) s = 0 := by
        apply le_antisymm _ bot_le
        exact (le_iInf fun v ↦ hmin (mem_univ v)).trans_eq hz
      exact ⟨u, u.property, (mem_iff_infEDist_zero_of_closed hs).mpr hu⟩
  · have heq : {ω | hittingAfter X s a ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, hs.hittingAfter_le_iff (hc ω), mem_empty_iff_false,
        iff_false, not_exists, not_and]
      exact fun u hu _ ↦ hat (hu.1.trans hu.2)
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ t)

/-- First exit from an open domain, including an immediate exit when the initial state
is outside, is a stopping time for a continuous adapted process on a raw filtration. -/
theorem Adapted.isStoppingTime_hittingAfter_compl_of_isOpen (hX : Adapted ℱ X)
    (hc : ∀ ω, Continuous (X · ω)) {U : Set E} (hU : IsOpen U) (a : ι) :
    IsStoppingTime ℱ (hittingAfter X Uᶜ a) :=
  hX.isStoppingTime_hittingAfter_of_isClosed hc hU.isClosed_compl a

end Stopping

end MeasureTheory
