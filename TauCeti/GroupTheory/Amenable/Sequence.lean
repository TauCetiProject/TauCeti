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

Conversely, a family of finite nonempty sets with vanishing relative boundaries along any
nontrivial filter passes each finite test simultaneously. This implication needs no
countability hypothesis. The sets in the resulting sequence need not be nested or exhaust
the group.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3, Theorem 3.6.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open Filter Finset MeasureTheory Topology
open scoped ENNReal Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G] [DecidableEq G]

/-- A group has Følner sets if a family of eventually nonempty finite sets has vanishing
relative translation boundaries along a nontrivial filter. -/
theorem HasFoelnerSets.of_tendsto_card_smul_symmDiff_div_card {ι : Type*} {l : Filter ι}
    [l.NeBot] {F : ι → Finset G} (hne : ∀ᶠ i in l, (F i).Nonempty)
    (hF : ∀ g : G, Tendsto (fun i => (#((g • F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    HasFoelnerSets G := by
  rw [hasFoelnerSets_iff]
  intro K ε hε
  have hevent : ∀ᶠ i in l, ∀ g ∈ K, (#((g • F i) ∆ F i) : ℝ) / #(F i) < ε :=
    (eventually_all_finset K).2 fun g _ => (hF g).eventually (gt_mem_nhds hε)
  obtain ⟨i, hni, hi⟩ := (hne.and hevent).exists
  exact ⟨F i, hni, fun g hg =>
    (div_lt_iff₀ (by exact_mod_cast hni.card_pos)).1 (hi g hg)⟩

/-- A countable group has Følner sets exactly when there is a sequence of finite nonempty
sets whose relative translation boundaries tend to zero for every group element. -/
theorem hasFoelnerSets_iff_exists_sequence [Countable G] : HasFoelnerSets G ↔
    ∃ F : ℕ → Finset G, (∀ n, (F n).Nonempty) ∧
      ∀ g : G, Tendsto (fun n => (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) := by
  let : MeasurableSpace G := ⊤
  refine ⟨fun h => ?_, fun ⟨F, hne, hF⟩ =>
    .of_tendsto_card_smul_symmDiff_div_card (Eventually.of_forall hne) hF⟩
  obtain ⟨F, hne, hF⟩ := exists_isFoelner_atTop (hasFoelnerSets_iff.1 h)
  -- A cofinal sequence of finite tests also sends the tolerance parameter to infinity.
  obtain ⟨a, -, ha⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset G × ℕ)
  refine ⟨F ∘ a, fun n => hne (a n), fun g => ?_⟩
  have hlimit := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    ((hF.comp_tendsto ha).tendsto_meas_smul_symmDiff g)
  simpa only [Function.comp_def, ← coe_smul_finset, ← coe_symmDiff,
    Measure.count_apply_finset, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_zero] using hlimit

end TauCeti
