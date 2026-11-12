/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Level localizers for increasing right-continuous processes

A right-continuous increasing extended-nonnegative process can be stopped when it first reaches
a finite level. Its entrance event is determined by its value at the current time, so these are
stopping times on the original filtration, without completeness or right continuity of the
filtration. Starting below the level makes the stopping time strictly later than the start.
For continuous paths, the hit is exact and the entire stopped process is bounded by the level.
Increasing levels tending to the top element give a localizing sequence (`IsLocalizingSequence`)
whenever the process is finite at every finite time almost surely.

These results apply to continuous accumulated-energy processes used to localize stochastic
integrands. Extended values are retained: a path may reach infinity in finite time, but such a
path is excluded only from the exhaustion conclusion, not from the stopping or bound results.

The results use general ordered time and value spaces and an arbitrary starting time.
The exhaustion and localizing-sequence results additionally require a top element in the value
space, with level sequences tending to that top element.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Monotone

variable {Ω ι β : Type*} [ConditionallyCompleteLinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [ConditionallyCompleteLinearOrder β]
  [TopologicalSpace β] [OrderTopology β] {A : ι → Ω → β} {ω : Ω} {c : β} {n t : ι}

/-- An increasing right-continuous process has reached a level by time `t` exactly when
`t` is at or after the starting time and its value at `t` is at least that level.
The first entrance time may be infinite. -/
theorem hittingAfter_Ici_le_iff (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) :
    hittingAfter A (Ici c) n ω ≤ t ↔ n ≤ t ∧ c ≤ A t ω := by
  classical
  constructor
  · intro h
    have hex : ∃ s, n ≤ s ∧ A s ω ∈ Ici c := by
      by_contra hn
      simp only [hittingAfter, hn, ↓reduceIte] at h
      exact WithTop.not_top_le_coe t h
    have hbelow : BddBelow {s : ι | n ≤ s ∧ c ≤ A s ω} := ⟨n, fun _ hs => hs.1⟩
    have hmem : c ≤ A (sInf {s : ι | n ≤ s ∧ c ≤ A s ω}) ω := by
      rw [MonotoneOn.map_csInf_of_continuousWithinAt
        (A := {s : ι | n ≤ s ∧ c ≤ A s ω})
        ((hcont _).mono (fun s hs => csInf_le hbelow hs))
        (hmono.monotoneOn _) hex hbelow]
      exact le_csInf (Set.Nonempty.image (A · ω) hex)
        (by rintro _ ⟨s, hs, rfl⟩; exact hs.2)
    refine ⟨WithTop.coe_le_coe.mp ((le_hittingAfter ω).trans h), ?_⟩
    simp only [hittingAfter, hex, ↓reduceIte] at h
    exact hmem.trans (hmono (WithTop.coe_le_coe.mp h))
  · rintro ⟨hnt, h⟩
    exact hittingAfter_le_of_mem hnt h

/-- Before the first level hit, either the process has not started or its value is strictly
below the level. -/
theorem lt_hittingAfter_Ici_iff (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) :
    (t : WithTop ι) < hittingAfter A (Ici c) n ω ↔ t < n ∨ A t ω < c := by
  simpa only [not_and_or, not_le] using not_congr (hittingAfter_Ici_le_iff hmono hcont)

/-- Starting strictly below a level makes its entrance time strictly greater than the initial
time. -/
theorem lt_hittingAfter_Ici (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) (hstart : A n ω < c) :
    (n : WithTop ι) < hittingAfter A (Ici c) n ω := by
  exact (lt_hittingAfter_Ici_iff hmono hcont).2 (Or.inr hstart)

variable [OrderTop β] {c : ℕ → β}

/-- At any time where the process is finite, level times for levels tending to infinity
eventually exceed that time. -/
theorem eventually_lt_hittingAfter_Ici (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) (hfinite : A t ω ≠ ⊤)
    (hc : Tendsto c atTop (𝓝 ⊤)) :
    ∀ᶠ k in atTop, (t : WithTop ι) < hittingAfter A (Ici (c k)) n ω := by
  filter_upwards [hc.eventually (eventually_gt_nhds (lt_top_iff_ne_top.mpr hfinite))]
    with k hk
  exact (lt_hittingAfter_Ici_iff hmono hcont).2 (Or.inr hk)

/-- If all finite-time values are finite, the first entrance times of any levels tending to
infinity tend to infinity. This is a pathwise exhaustion statement. -/
theorem tendsto_hittingAfter_Ici (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) (hfinite : ∀ t, A t ω ≠ ⊤)
    (hc : Tendsto c atTop (𝓝 ⊤)) :
    Tendsto (fun k => hittingAfter A (Ici (c k)) n ω) atTop (𝓝 ⊤) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    lift b to ι using hb.ne with b
    exact eventually_lt_hittingAfter_Ici hmono hcont (hfinite b) hc
  · intro b hb
    exact (not_lt_of_ge le_top hb).elim

end Monotone

namespace Continuous

variable {Ω ι β : Type*} [ConditionallyCompleteLinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
  {A : ι → Ω → β} {ω : Ω} {c : β} {n t : ι}

/-- A continuous increasing process starting at or below a level hits it exactly, whenever
the entrance time is finite. No finite-valuedness assumption on the path is needed. -/
theorem stoppedValue_hittingAfter_Ici_eq (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hstart : A n ω ≤ c)
    (hfinite : hittingAfter A (Ici c) n ω ≠ ⊤) :
    stoppedValue A (hittingAfter A (Ici c) n) ω = c := by
  simp only [stoppedValue]
  have hright : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s :=
    fun _ => hcont.continuousAt.continuousWithinAt
  lift hittingAfter A (Ici c) n ω to ι using hfinite with s hs
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hcs : n ≤ s ∧ c ≤ A s ω :=
    (hmono.hittingAfter_Ici_le_iff hright).1 (by rw [hs])
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc hcs.1 hcont.continuousOn
    ⟨hstart, hcs.2⟩
  have hsu : s ≤ u := WithTop.coe_le_coe.mp
    (hs ▸ (hmono.hittingAfter_Ici_le_iff hright).2 ⟨hu.1, heq.ge⟩)
  simpa only [le_antisymm hu.2 hsu] using heq

/-- Stopping at a level bounds the whole stopped increasing process by that level. -/
theorem stoppedProcess_hittingAfter_Ici_le (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hstart : A n ω ≤ c) :
    stoppedProcess A (hittingAfter A (Ici c) n) t ω ≤ c := by
  by_cases ht : (t : WithTop ι) < hittingAfter A (Ici c) n ω
  · rw [stoppedProcess_eq_of_le ht.le]
    rcases ((hmono.lt_hittingAfter_Ici_iff
      (fun _ => hcont.continuousAt.continuousWithinAt)).1 ht) with htn | hlt
    · exact (hmono htn.le).trans hstart
    · exact hlt.le
  · have hle := le_of_not_gt ht
    rw [stoppedProcess_eq_of_ge hle]
    simpa only [stoppedValue] using
      (stoppedValue_hittingAfter_Ici_eq hcont hmono hstart (ne_top_of_le_ne_top
        WithTop.coe_ne_top hle)).le

end Continuous

namespace MeasureTheory.Adapted

variable {Ω ι β : Type*} [ConditionallyCompleteLinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [ConditionallyCompleteLinearOrder β]
  [TopologicalSpace β] [OrderTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
  {mΩ : MeasurableSpace Ω} {F : Filtration ι mΩ} {A : ι → Ω → β}

/-- Level entrance times of an increasing right-continuous adapted process are stopping times
on the raw filtration. In particular no usual-filtration conditions are required. -/
theorem isStoppingTime_hittingAfter_Ici_of_monotone (hA : Adapted F A)
    (hcont : ∀ ω s, ContinuousWithinAt (A · ω) (Ici s) s)
    (hmono : ∀ ω, Monotone (A · ω)) (c : β) (n : ι) :
    IsStoppingTime F (hittingAfter A (Ici c) n) := by
  intro t
  simp_rw [(hmono _).hittingAfter_Ici_le_iff (hcont _)]
  by_cases hnt : n ≤ t
  · simpa only [hnt, true_and, preimage, mem_Ici] using
      (measurableSet_Ici (a := c)).preimage (hA t)
  · simp only [hnt, false_and, ofPred_false]
    exact @MeasurableSet.empty Ω (F t)

variable [OrderTop β] {c : ℕ → β}

/-- The level times of an increasing right-continuous adapted process at increasing levels
tending to infinity form a localizing sequence when its finite-time values are almost
surely finite. No moment assumption is used. -/
theorem isLocalizingSequence_hittingAfter_Ici (hA : Adapted F A)
    (hcont : ∀ ω s, ContinuousWithinAt (A · ω) (Ici s) s)
    (hmono : ∀ ω, Monotone (A · ω))
    (P : Measure Ω) (hfinite : ∀ᵐ ω ∂P, ∀ t, A t ω ≠ ⊤)
    (hc : Tendsto c atTop (𝓝 ⊤)) (hcm : Monotone c) (n : ι) :
    ProbabilityTheory.IsLocalizingSequence F
      (fun k => hittingAfter A (Ici (c k)) n) P where
  isStoppingTime _ := hA.isStoppingTime_hittingAfter_Ici_of_monotone hcont hmono _ n
  tendsto_top := hfinite.mono fun ω hω =>
    (hmono ω).tendsto_hittingAfter_Ici (hcont ω) hω hc
  mono := ae_of_all _ fun ω _ _ hij =>
    hittingAfter_apply_anti A n ω (Ici_subset_Ici.mpr (hcm hij))

end MeasureTheory.Adapted
