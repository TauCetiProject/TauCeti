/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty

/-!
# Dominated local martingales

A strongly adapted native local martingale is a martingale if its paths on each finite
initial interval are dominated by an integrable random variable. In particular, deterministic
bounds on finite initial intervals give a martingale under a finite measure.
These criteria justify removing localization in bounded conditional-expectation arguments.

We retain Mathlib's native convention: the localized stages stop the process multiplied by
`1_{0 < τ_n}`. Strong adaptation of the original process is a separate hypothesis: native
locality alone can hide nonmeasurable changes on null sets. No path regularity or usual
conditions on the filtration are needed.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, Chapter 1, §5.
-/

public section

open Filter ProbabilityTheory
open scoped Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {F : Filtration ι mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ι → Ω → E}

/-- A strongly adapted local martingale whose paths on each initial interval admit an
integrable dominator is a true martingale. The dominator for horizon `t` bounds `‖X s ω‖`
almost surely for all `s ≤ t` simultaneously. -/
theorem StronglyAdapted.martingale_of_locally_martingale_of_dominated [SigmaFiniteFiltration P F]
    (hX : StronglyAdapted F X) (hlocal : Locally (fun Y ↦ Martingale Y F P) F X P)
    (hbound : ∀ t, ∃ b : Ω → ℝ, Integrable b P ∧
      ∀ᵐ ω ∂P, ∀ s ≤ t, ‖X s ω‖ ≤ b ω) : Martingale X F P := by
  classical
  obtain ⟨τ, hτ, hmart⟩ := hlocal
  let Z := fun n ↦ MeasureTheory.stoppedProcess
    (fun s ↦ {ω | ⊥ < τ n ω}.indicator (X s)) (τ n)
  have hlim (t : ι) : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Z n t ω) atTop (𝓝 (X t ω)) := by
    filter_upwards [hτ.tendsto_top] with ω hω
    have hevent := (WithTop.tendsto_nhds_top_iff _).mp hω t
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    have hpos : ω ∈ {ω | ⊥ < τ n ω} := by
      simpa only [WithTop.coe_bot, Set.mem_ofPred_eq] using
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr bot_le) hn
    simp only [Z, stoppedProcess_eq_of_le hn.le, Set.indicator_of_mem hpos]
  have hZbound (t : ι) (b : Ω → ℝ)
      (hb : ∀ᵐ ω ∂P, ∀ s ≤ t, ‖X s ω‖ ≤ b ω) (n : ℕ) :
      ∀ᵐ ω ∂P, ‖Z n t ω‖ ≤ b ω := by
    filter_upwards [hb] with ω hω
    dsimp only [Z]
    rw [stoppedProcess_indicator_comm]
    refine (norm_indicator_le_norm_self _ _).trans ?_
    by_cases ht : (t : WithTop ι) ≤ τ n ω
    · simpa [stoppedProcess_eq_of_le ht] using hω t le_rfl
    · have hlt := lt_of_not_ge ht
      rw [stoppedProcess_eq_of_ge hlt.le]
      exact hω _ ((WithTop.untopA_le_iff hlt.ne_top).mpr hlt.le)
  have hint (t : ι) : Integrable (X t) P := by
    obtain ⟨b, hb, hdom⟩ := hbound t
    exact hb.mono' ((hX t).mono (F.le t)).aestronglyMeasurable
      (hdom.mono fun ω hω ↦ hω t le_rfl)
  refine ⟨hX, fun s t hst ↦ ?_⟩
  obtain ⟨bs, hbs, hdoms⟩ := hbound s
  obtain ⟨bt, hbt, hdomt⟩ := hbound t
  have hcond := tendsto_condExp_unique (m := F s) (fun n ↦ Z n t) (fun n ↦ Z n s)
    (X t) (X s) (fun n ↦ (hmart n).integrable t) (fun n ↦ (hmart n).integrable s)
    (hlim t) (hlim s) bt hbt bs hbs (hZbound t bt hdomt) (hZbound s bs hdoms)
    (fun n ↦ ((hmart n).condExp_ae_eq hst).trans
      (by rw [condExp_of_stronglyMeasurable (F.le s) ((hmart n).stronglyAdapted s)
        ((hmart n).integrable s)]))
  exact hcond.trans (by rw [condExp_of_stronglyMeasurable (F.le s) (hX s) (hint s)])

/-- A strongly adapted local martingale with a deterministic bound on each finite initial
interval is a martingale under any finite measure. The bound may depend on the horizon;
no continuity, complete filtration, or right-continuous filtration is required. -/
theorem StronglyAdapted.martingale_of_locally_martingale_of_bounded [IsFiniteMeasure P]
    (hX : StronglyAdapted F X) (hlocal : Locally (fun Y ↦ Martingale Y F P) F X P)
    (hbound : ∀ t, ∃ C : ℝ, ∀ᵐ ω ∂P, ∀ s ≤ t, ‖X s ω‖ ≤ C) : Martingale X F P := by
  apply hX.martingale_of_locally_martingale_of_dominated hlocal
  intro t
  obtain ⟨C, hC⟩ := hbound t
  exact ⟨fun _ ↦ C, integrable_const C, hC⟩

end MeasureTheory
