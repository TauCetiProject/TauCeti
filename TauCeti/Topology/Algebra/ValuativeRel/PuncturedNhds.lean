/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Punctured neighbourhoods in nontrivially valued division rings

In a division ring `K` carrying a nontrivial valuative relation (`ValuativeRel.IsNontrivial K`) and
its valuative topology (`IsValuativeTopology K`), no point is isolated: every punctured
neighbourhood `𝓝[≠] x` is nontrivial. Around `0`, every basic open ball `{y | v y < γ}` (`γ > 0`)
contains a nonzero element of valuation `δ * γ < γ` where `0 < δ < 1`, and translation transports
this to every `x : K`.

This is the valuative counterpart of `NormedField.nhdsNE_neBot`; in particular, it triggers
Mathlib's `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass` on nonarchimedean local
fields and supplies the `[NeBot (𝓝[≠] (0 : K))]` assumption of `Module.punctured_nhds_neBot` for
nontrivial topological vector spaces over `K`.

## Main declarations

* `TauCeti.instPuncturedNhdsNeBotOfIsValuativeTopology`: `(𝓝[≠] x).NeBot` for `x : K`.
-/

public section

open Filter Set Topology ValuativeRel

namespace TauCeti

variable {K : Type*} [DivisionRing K] [ValuativeRel K] [ValuativeRel.IsNontrivial K]
  [TopologicalSpace K] [IsValuativeTopology K]

/-- In a division ring with a nontrivial valuative topology, no point is isolated. -/
instance instPuncturedNhdsNeBotOfIsValuativeTopology (x : K) : (𝓝[≠] x).NeBot := by
  -- Translate `0` to `x` once `(𝓝[≠] (0 : K)).NeBot` is established.
  have h0 : (𝓝[≠] (0 : K)).NeBot := by
    refine forall_mem_nonempty_iff_neBot.mp fun s hs ↦ ?_
    obtain ⟨t, ht, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs
    obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp ht
    obtain ⟨δ, hδ0, hδ1⟩ := IsNontrivial.exists_lt_one (R := K)
    obtain ⟨a, ha⟩ := valuation_surjective δ
    obtain ⟨b, hb⟩ := valuation_surjective γ.val
    refine ⟨a * b, hsub ⟨hγ ?_, ?_⟩⟩
    · rw [mem_ofPred_eq, map_mul, ha, hb]
      exact (mul_lt_mul_of_pos_right hδ1 γ.zero_lt).trans_eq (one_mul _)
    · rw [mem_compl_singleton_iff, ← (valuation K).ne_zero_iff, map_mul, ha, hb]
      exact (mul_pos hδ0 γ.zero_lt).ne'
  have hmap := (Homeomorph.addLeft x).map_punctured_nhds_eq 0
  simp only [Homeomorph.coe_addLeft, add_zero] at hmap
  rw [← hmap]
  exact h0.map _

end TauCeti
