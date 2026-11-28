/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Analysis.Normed.Group.FunctionSeries

/-!
# Almost sure uniform convergence from summable increment bounds

If a sequence of random functions `X n : α → Ω → E` into a Banach space has consecutive increments
on a set `s : Set α` exceeding `u n` only on events of summable outer measure, with `Summable u`,
then `X n · ω` converges uniformly on `s` to `limUnder atTop (fun n ↦ X n · ω)` almost
everywhere (`TauCeti.MeasureTheory.ae_tendstoUniformlyOn_limUnder_of_summable`). When `α` is a
topological space and each `X n · ω` is almost surely continuous on `s`, the limit is also
almost surely continuous on `s`
(`TauCeti.MeasureTheory.ae_continuousOn_and_tendstoUniformlyOn_limUnder_of_summable`).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti.MeasureTheory

variable {α Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [CompleteSpace E]

/-- On an arbitrary set `s`, summable uniform increment bounds outside events of summable measure
yield almost sure uniform convergence on `s` to `limUnder atTop (fun n ↦ X n t ω)`. -/
theorem ae_tendstoUniformlyOn_limUnder_of_summable
    {s : Set α} {X : ℕ → α → Ω → E} {u : ℕ → ℝ} (hu : Summable u)
    (herr : (∑' n, μ {ω | ∃ t ∈ s, u n < ‖X (n + 1) t ω - X n t ω‖}) ≠ ∞) :
    ∀ᵐ ω ∂μ, TendstoUniformlyOn (fun n t ↦ X n t ω)
      (fun t ↦ limUnder atTop (fun n ↦ X n t ω)) atTop s := by
  have hbound : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ t ∈ s, ‖X (n + 1) t ω - X n t ω‖ ≤ u n := by
    filter_upwards [ae_eventually_notMem herr] with ω hω
    exact hω.mono fun n hn t ht ↦ le_of_not_gt fun h ↦ hn ⟨t, ht, h⟩
  filter_upwards [hbound] with ω hω
  exact TauCeti.tendstoUniformlyOn_limUnder_of_eventually (f := fun n t ↦ X n t ω) hu hω

/-- On an arbitrary set `s` in a topological space, summable uniform increment bounds yield a.s.
continuity on `s` and a.s. uniform convergence on `s` of `limUnder atTop (fun n ↦ X n t ω)`. -/
theorem ae_continuousOn_and_tendstoUniformlyOn_limUnder_of_summable [TopologicalSpace α]
    {s : Set α} {X : ℕ → α → Ω → E} {u : ℕ → ℝ}
    (hc : ∀ n, ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X n t ω) s) (hu : Summable u)
    (herr : (∑' n, μ {ω | ∃ t ∈ s, u n < ‖X (n + 1) t ω - X n t ω‖}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ limUnder atTop (fun n ↦ X n t ω)) s ∧
      TendstoUniformlyOn (fun n t ↦ X n t ω)
        (fun t ↦ limUnder atTop (fun n ↦ X n t ω)) atTop s := by
  filter_upwards [ae_tendstoUniformlyOn_limUnder_of_summable hu herr, ae_all_iff.2 hc]
    with ω hunif hcω
  exact ⟨hunif.continuousOn (Frequently.of_forall hcω), hunif⟩

end TauCeti.MeasureTheory
