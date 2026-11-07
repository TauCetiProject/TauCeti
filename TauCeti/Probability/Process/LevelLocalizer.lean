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
# Level localizers for increasing continuous processes

A continuous increasing extended-nonnegative process can be stopped when it first reaches a
finite level. Its entrance event is determined by its value at the current time, so these are
stopping times on the original filtration, without completeness or right continuity. Starting
below the level gives an exact hit, a strictly positive stopping time, and a bound on the
entire stopped process. Levels tending to infinity give a native localizing sequence whenever
the process is finite at every finite time almost surely.

These results apply to continuous accumulated-energy processes used to localize stochastic
integrands. Extended values are retained: a path may reach infinity in finite time, but such a
path is excluded only from the exhaustion conclusion, not from the stopping or bound results.
Constructing a continuous accumulated-energy process from a general integrand is separate.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace Continuous

variable {Ω : Type*} {A : ℝ≥0 → Ω → ℝ≥0∞} {ω : Ω} {c : ℝ≥0∞} {t : ℝ≥0}

/-- An increasing continuous process has reached a level by time `t` exactly when its value
at `t` is at least that level. The first entrance time may be infinite. -/
theorem hittingAfter_Ici_le_iff (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) :
    hittingAfter A (Ici c) 0 ω ≤ t ↔ c ≤ A t ω := by
  classical
  constructor
  · intro h
    have hex : ∃ s, 0 ≤ s ∧ A s ω ∈ Ici c := by
      by_contra hn
      simp only [hittingAfter, hn, ↓reduceIte] at h
      exact WithTop.not_top_le_coe t h
    have hclosed : IsClosed {s : ℝ≥0 | 0 ≤ s ∧ c ≤ A s ω} := by
      simpa only [zero_le, true_and, preimage, mem_Ici] using
        isClosed_Ici.preimage hcont
    have hmem := hclosed.csInf_mem hex (OrderBot.bddBelow _)
    simp only [hittingAfter, hex, ↓reduceIte] at h
    exact hmem.2.trans (hmono (WithTop.coe_le_coe.mp h))
  · intro h
    exact hittingAfter_le_of_mem (by positivity) h

/-- Before the first level hit, an increasing continuous process is strictly below that level. -/
theorem lt_hittingAfter_Ici_iff (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) :
    (t : WithTop ℝ≥0) < hittingAfter A (Ici c) 0 ω ↔ A t ω < c := by
  simpa only [not_le] using not_congr (hittingAfter_Ici_le_iff hcont hmono)

/-- A continuous increasing process starting at or below a level hits it exactly, whenever
the entrance time is finite. No finite-valuedness assumption on the path is needed. -/
theorem hittingAfter_Ici_eq_level (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hzero : A 0 ω ≤ c)
    (hfinite : hittingAfter A (Ici c) 0 ω ≠ ⊤) :
    A (hittingAfter A (Ici c) 0 ω).untopA ω = c := by
  lift hittingAfter A (Ici c) 0 ω to ℝ≥0 using hfinite with s hs
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hcs : c ≤ A s ω :=
    (hittingAfter_Ici_le_iff hcont hmono).1 (by rw [hs])
  apply le_antisymm _ hcs
  by_contra hn
  have hlt : c < A s ω := lt_of_not_ge hn
  obtain ⟨d, hcd, hds⟩ := exists_between hlt
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc (by positivity : 0 ≤ s) hcont.continuousOn
    ⟨hzero.trans hcd.le, hds.le⟩
  have hsu : s ≤ u := WithTop.coe_le_coe.mp
    (hs ▸ (hittingAfter_Ici_le_iff hcont hmono).2 (hcd.le.trans heq.ge))
  have hus : u < s := lt_of_le_of_ne hu.2 (by intro h; subst u; exact hds.ne heq.symm)
  exact (not_lt_of_ge hsu) hus

/-- Starting strictly below a level makes its entrance time strictly positive. -/
theorem hittingAfter_Ici_pos (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hzero : A 0 ω < c) :
    0 < hittingAfter A (Ici c) 0 ω := by
  exact (lt_hittingAfter_Ici_iff hcont hmono).2 hzero

/-- Stopping at a finite level bounds the whole stopped increasing process by that level. -/
theorem stoppedProcess_hittingAfter_Ici_le (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hzero : A 0 ω ≤ c) :
    stoppedProcess A (hittingAfter A (Ici c) 0) t ω ≤ c := by
  by_cases ht : (t : WithTop ℝ≥0) < hittingAfter A (Ici c) 0 ω
  · rw [stoppedProcess_eq_of_le ht.le]
    exact ((lt_hittingAfter_Ici_iff hcont hmono).1 ht).le
  · have hle := le_of_not_gt ht
    rw [stoppedProcess_eq_of_ge hle]
    exact (hittingAfter_Ici_eq_level hcont hmono hzero (ne_top_of_le_ne_top
      WithTop.coe_ne_top hle)).le

/-- At any time where the process is finite, all sufficiently high level times exceed that
time. In particular their minima with a fixed finite horizon eventually equal that horizon. -/
theorem eventually_lt_hittingAfter_Ici_nat (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hfinite : A t ω ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, (t : WithTop ℝ≥0) <
      hittingAfter A (Ici (n + 1 : ℝ≥0∞)) 0 ω := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfinite
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (lt_hittingAfter_Ici_iff hcont hmono).2
  exact hN.trans_le (by exact_mod_cast (Nat.le_succ_of_le hn))

/-- If all finite-time values are finite, the first entrance times of the levels `n + 1`
tend to infinity. This is a pathwise exhaustion statement. -/
theorem tendsto_hittingAfter_Ici_nat (hcont : Continuous (A · ω))
    (hmono : Monotone (A · ω)) (hfinite : ∀ t, A t ω ≠ ⊤) :
    Tendsto (fun n : ℕ => hittingAfter A (Ici (n + 1 : ℝ≥0∞)) 0 ω) atTop (𝓝 ⊤) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    lift b to ℝ≥0 using hb.ne with b
    exact eventually_lt_hittingAfter_Ici_nat hcont hmono (hfinite b)
  · intro b hb
    exact (not_lt_of_ge le_top hb).elim

end Continuous

namespace MeasureTheory.Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {A : ℝ≥0 → Ω → ℝ≥0∞}

/-- Level entrance times of an increasing continuous adapted process are stopping times on
the raw filtration. In particular no usual-filtration conditions are required. -/
theorem isStoppingTime_hittingAfter_Ici_of_monotone (hA : Adapted F A)
    (hcont : ∀ ω, Continuous (A · ω)) (hmono : ∀ ω, Monotone (A · ω)) (c : ℝ≥0∞) :
    IsStoppingTime F (hittingAfter A (Ici c) 0) := by
  intro t
  simp_rw [(hcont _).hittingAfter_Ici_le_iff (hmono _)]
  exact measurableSet_le measurable_const (hA t)

/-- The level times of an increasing continuous adapted process form a native localizing
sequence when its finite-time values are almost surely finite. No moment assumption is used. -/
theorem isLocalizingSequence_hittingAfter_Ici (hA : Adapted F A)
    (hcont : ∀ ω, Continuous (A · ω)) (hmono : ∀ ω, Monotone (A · ω))
    (P : Measure Ω) (hfinite : ∀ᵐ ω ∂P, ∀ t, A t ω ≠ ⊤) :
    ProbabilityTheory.IsLocalizingSequence F
      (fun n => hittingAfter A (Ici (n + 1 : ℝ≥0∞)) 0) P where
  isStoppingTime n := hA.isStoppingTime_hittingAfter_Ici_of_monotone hcont hmono _
  tendsto_top := hfinite.mono fun ω hω =>
    (hcont ω).tendsto_hittingAfter_Ici_nat (hmono ω) hω
  mono := ae_of_all _ fun ω i j hij =>
    hittingAfter_apply_anti A 0 ω (Ici_subset_Ici.mpr
      (by exact_mod_cast Nat.add_le_add_right hij 1))

end MeasureTheory.Adapted
