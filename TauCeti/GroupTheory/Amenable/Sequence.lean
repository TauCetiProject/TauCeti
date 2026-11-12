/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Foelner
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Følner sequences in countable groups

A countable group has Følner sets exactly when it admits a sequence of finite nonempty sets
whose relative translation boundaries tend to zero for every group element. Countability
allows the finite-test Følner net to be restricted along a cofinal sequence of tests. This
works for finite groups as well as infinite ones: no injective enumeration is required.

The sets in the resulting sequence need not be nested or exhaust the group.

## Main results

* `TauCeti.hasFoelnerSets_iff_exists_seq`: the countable Følner sequence criterion.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3, Theorem 3.6.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open Filter Finset Topology
open scoped Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G] [DecidableEq G]

/-- A countable group has Følner sets exactly when there is a sequence of finite nonempty
sets whose relative translation boundaries tend to zero for every group element. -/
theorem hasFoelnerSets_iff_exists_seq [Countable G] : HasFoelnerSets G ↔
    ∃ F : ℕ → Finset G, (∀ n, (F n).Nonempty) ∧
      ∀ g : G, Tendsto (fun n => (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) := by
  let : MeasurableSpace G := ⊤
  refine ⟨fun h => ?_, fun ⟨F, hne, hF⟩ =>
    .of_tendsto_card_smul_symmDiff_div_card (Eventually.of_forall hne) hF⟩
  obtain ⟨F, hne, hF⟩ := exists_isFoelner_atTop (hasFoelnerSets_iff.1 h)
  -- A cofinal sequence of finite tests also sends the tolerance parameter to infinity.
  obtain ⟨a, -, ha⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset G × ℕ)
  refine ⟨F ∘ a, fun n => hne (a n), fun g => ?_⟩
  exact (hF.comp_tendsto ha).tendsto_card_smul_symmDiff_div_card g

end TauCeti
