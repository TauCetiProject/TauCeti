/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Continuity of valuation-preserving ring endomorphisms

A ring endomorphism of a valued ring that preserves the valuation is continuous for the valuation
topology (`Valued.continuous_of_valuation_eq`).
-/

public section

namespace Valued

/-- A ring endomorphism of a valued ring that preserves the valuation is continuous. -/
theorem continuous_of_valuation_eq {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued R Γ₀] {σ : R →+* R} (hσ : ∀ x : R, Valued.v (σ x) = Valued.v x) : Continuous σ := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  rw [Valued.mem_nhds] at hs ⊢
  obtain ⟨γ, hγ⟩ := hs
  refine ⟨γ, fun y hy ↦ hγ ?_⟩
  have hsub : Valued.v (σ y - σ x) = Valued.v (y - x) := by rw [← map_sub, hσ]
  have hr : (Valued.v (R := R)).restrict (σ y - σ x) = (Valued.v (R := R)).restrict (y - x) :=
    le_antisymm ((Valuation.restrict_le_iff _).mpr hsub.le)
      ((Valuation.restrict_le_iff _).mpr hsub.ge)
  simpa [hr] using hy

end Valued
