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
filtration. Starting below the level gives a strictly positive stopping time. For continuous
paths, the hit is exact and the entire stopped process is bounded by the level. Levels tending
to infinity give a native localizing sequence whenever the process is finite at every finite
time almost surely.

These results apply to continuous accumulated-energy processes used to localize stochastic
integrands. Extended values are retained: a path may reach infinity in finite time, but such a
path is excluded only from the exhaustion conclusion, not from the stopping or bound results.
Constructing a continuous accumulated-energy process from a general integrand is separate.

The pathwise and stopping-time results use general ordered time and value spaces, with time
starting at its bottom element. Only the exhaustion and localizing-sequence results require
extended-nonnegative values, with level sequences tending to infinity.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace Monotone

variable {Ω ι β : Type*} [ConditionallyCompleteLinearOrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] [ConditionallyCompleteLinearOrder β]
  [TopologicalSpace β] [OrderTopology β] {A : ι → Ω → β} {ω : Ω} {c : β} {t : ι}

/-- An increasing right-continuous process has reached a level by time `t` exactly when its
value at `t` is at least that level. The first entrance time may be infinite. -/
theorem hittingAfter_Ici_le_iff (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) :
    hittingAfter A (Ici c) ⊥ ω ≤ t ↔ c ≤ A t ω := by
  classical
  constructor
  · intro h
    have hex : ∃ s, ⊥ ≤ s ∧ A s ω ∈ Ici c := by
      by_contra hn
      simp only [hittingAfter, hn, ↓reduceIte] at h
      exact WithTop.not_top_le_coe t h
    have hmem : c ≤ A (sInf {s : ι | ⊥ ≤ s ∧ c ≤ A s ω}) ω := by
      rw [MonotoneOn.map_csInf_of_continuousWithinAt
        (A := {s : ι | ⊥ ≤ s ∧ c ≤ A s ω})
        ((hcont _).mono (fun s hs => csInf_le (OrderBot.bddBelow _) hs))
        (hmono.monotoneOn _) hex]
      exact le_csInf (Set.Nonempty.image (A · ω) hex)
        (by rintro _ ⟨s, hs, rfl⟩; exact hs.2)
    simp only [hittingAfter, hex, ↓reduceIte] at h
    exact hmem.trans (hmono (WithTop.coe_le_coe.mp h))
  · intro h
    exact hittingAfter_le_of_mem bot_le h

/-- Before the first level hit, an increasing right-continuous process is strictly below
that level. -/
theorem lt_hittingAfter_Ici_iff (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) :
    (t : WithTop ι) < hittingAfter A (Ici c) ⊥ ω ↔ A t ω < c := by
  simpa only [not_le] using not_congr (hittingAfter_Ici_le_iff hmono hcont)

/-- Starting strictly below a level makes its entrance time strictly greater than the initial
time. -/
theorem hittingAfter_Ici_pos (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) (hzero : A ⊥ ω < c) :
    (⊥ : ι) < hittingAfter A (Ici c) ⊥ ω := by
  exact (lt_hittingAfter_Ici_iff hmono hcont).2 hzero

variable {A : ι → Ω → ℝ≥0∞} {c : ℕ → ℝ≥0∞}

/-- At any time where the process is finite, level times for levels tending to infinity
eventually exceed that time. In particular their minima with a fixed finite horizon eventually
equal that horizon. -/
theorem eventually_lt_hittingAfter_Ici (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) (hfinite : A t ω ≠ ⊤)
    (hc : Tendsto c atTop (𝓝 ⊤)) :
    ∀ᶠ n in atTop, (t : WithTop ι) < hittingAfter A (Ici (c n)) ⊥ ω := by
  filter_upwards [hc.eventually (eventually_gt_nhds (lt_top_iff_ne_top.mpr hfinite))]
    with n hn
  exact (lt_hittingAfter_Ici_iff hmono hcont).2 hn

/-- If all finite-time values are finite, the first entrance times of any levels tending to
infinity tend to infinity. This is a pathwise exhaustion statement. -/
theorem tendsto_hittingAfter_Ici (hmono : Monotone (A · ω))
    (hcont : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s) (hfinite : ∀ t, A t ω ≠ ⊤)
    (hc : Tendsto c atTop (𝓝 ⊤)) :
    Tendsto (fun n => hittingAfter A (Ici (c n)) ⊥ ω) atTop (𝓝 ⊤) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    lift b to ι using hb.ne with b
    exact eventually_lt_hittingAfter_Ici hmono hcont (hfinite b) hc
  · intro b hb
    exact (not_lt_of_ge le_top hb).elim

end Monotone

namespace Continuous

variable {Ω ι β : Type*} [ConditionallyCompleteLinearOrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
  {A : ι → Ω → β} {ω : Ω} {c : β} {t : ι}

/-- A continuous increasing process starting at or below a level hits it exactly, whenever
the entrance time is finite. No finite-valuedness assumption on the path is needed. -/
theorem apply_untopA_hittingAfter_Ici_eq (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hzero : A ⊥ ω ≤ c)
    (hfinite : hittingAfter A (Ici c) ⊥ ω ≠ ⊤) :
    A (hittingAfter A (Ici c) ⊥ ω).untopA ω = c := by
  have hright : ∀ s, ContinuousWithinAt (A · ω) (Ici s) s :=
    fun _ => hcont.continuousAt.continuousWithinAt
  lift hittingAfter A (Ici c) ⊥ ω to ι using hfinite with s hs
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hcs : c ≤ A s ω :=
    (hmono.hittingAfter_Ici_le_iff hright).1 (by rw [hs])
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc (bot_le : ⊥ ≤ s) hcont.continuousOn
    ⟨hzero, hcs⟩
  have hsu : s ≤ u := WithTop.coe_le_coe.mp
    (hs ▸ (hmono.hittingAfter_Ici_le_iff hright).2 heq.ge)
  simpa only [le_antisymm hu.2 hsu] using heq

/-- Stopping at a level bounds the whole stopped increasing process by that level. -/
theorem stoppedProcess_hittingAfter_Ici_le (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hzero : A ⊥ ω ≤ c) :
    stoppedProcess A (hittingAfter A (Ici c) ⊥) t ω ≤ c := by
  by_cases ht : (t : WithTop ι) < hittingAfter A (Ici c) ⊥ ω
  · rw [stoppedProcess_eq_of_le ht.le]
    exact ((hmono.lt_hittingAfter_Ici_iff
      (fun _ => hcont.continuousAt.continuousWithinAt)).1 ht).le
  · have hle := le_of_not_gt ht
    rw [stoppedProcess_eq_of_ge hle]
    exact (apply_untopA_hittingAfter_Ici_eq hcont hmono hzero (ne_top_of_le_ne_top
      WithTop.coe_ne_top hle)).le

end Continuous

namespace MeasureTheory.Adapted

variable {Ω ι β : Type*} [ConditionallyCompleteLinearOrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] [ConditionallyCompleteLinearOrder β]
  [TopologicalSpace β] [OrderTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
  {mΩ : MeasurableSpace Ω} {F : Filtration ι mΩ} {A : ι → Ω → β}

/-- Level entrance times of an increasing right-continuous adapted process are stopping times
on the raw filtration. In particular no usual-filtration conditions are required. -/
theorem isStoppingTime_hittingAfter_Ici_of_monotone (hA : Adapted F A)
    (hcont : ∀ ω s, ContinuousWithinAt (A · ω) (Ici s) s)
    (hmono : ∀ ω, Monotone (A · ω)) (c : β) :
    IsStoppingTime F (hittingAfter A (Ici c) ⊥) := by
  intro t
  simp_rw [(hmono _).hittingAfter_Ici_le_iff (hcont _)]
  exact measurableSet_Ici.preimage (hA t)

variable {A : ι → Ω → ℝ≥0∞} {c : ℕ → ℝ≥0∞}

/-- The level times of an increasing right-continuous adapted process at increasing levels
tending to infinity form a native localizing sequence when its finite-time values are almost
surely finite. No moment assumption is used. -/
theorem isLocalizingSequence_hittingAfter_Ici (hA : Adapted F A)
    (hcont : ∀ ω s, ContinuousWithinAt (A · ω) (Ici s) s)
    (hmono : ∀ ω, Monotone (A · ω))
    (P : Measure Ω) (hfinite : ∀ᵐ ω ∂P, ∀ t, A t ω ≠ ⊤)
    (hc : Tendsto c atTop (𝓝 ⊤)) (hcm : Monotone c) :
    ProbabilityTheory.IsLocalizingSequence F
      (fun n => hittingAfter A (Ici (c n)) ⊥) P where
  isStoppingTime _ := hA.isStoppingTime_hittingAfter_Ici_of_monotone hcont hmono _
  tendsto_top := hfinite.mono fun ω hω =>
    (hmono ω).tendsto_hittingAfter_Ici (hcont ω) hω hc
  mono := ae_of_all _ fun ω _ _ hij =>
    hittingAfter_apply_anti A ⊥ ω (Ici_subset_Ici.mpr (hcm hij))

end MeasureTheory.Adapted
