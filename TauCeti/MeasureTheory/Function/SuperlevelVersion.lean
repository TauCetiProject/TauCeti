/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurable versions from measurable versions of the superlevel sets

Let `μ` be a measure and `m` a σ-algebra on the same type, typically a sub-σ-algebra. If every
superlevel set `{x | q < f x}` of a function `f : α → ℝ≥0∞` at a rational height `q`
agrees `μ`-almost everywhere with an `m`-measurable set, then `f` agrees `μ`-almost everywhere
with an `m`-measurable function
(`TauCeti.MeasureTheory.exists_measurable_ae_eq_of_forall_superlevel`): the supremum over `q` of
`q` times the indicators of those sets. No measurability of `f` is assumed.

Taking for `m` the infimum of a family of σ-algebras gives a single version that is measurable for
every member of the family; this is how invariant densities of invariant Gibbs measures are made
measurable for every exterior σ-algebra at once.
-/

public section

open Filter MeasureTheory Set

open scoped ENNReal NNReal

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f : α → ℝ≥0∞}

/-- **A function whose superlevel sets have measurable versions has a measurable version.** If
for every rational `q` the superlevel set `{x | q < f x}` agrees `μ`-almost everywhere
with an `m`-measurable set, then `f` agrees `μ`-almost everywhere with an `m`-measurable
function. -/
theorem exists_measurable_ae_eq_of_forall_superlevel
    (h : ∀ q : ℚ, ∃ T : Set α, MeasurableSet[m] T ∧ T =ᵐ[μ] {x | ENNReal.ofReal q < f x}) :
    ∃ g : α → ℝ≥0∞, Measurable[m] g ∧ g =ᵐ[μ] f := by
  -- `f` is almost surely the supremum of the heights `q` with `x ∈ T q`.
  choose T hT hTf using h
  refine ⟨fun x => ⨆ q : ℚ, (T q).indicator (fun _ => ENNReal.ofReal q) x,
    Measurable.iSup fun q => measurable_const.indicator (hT q), ?_⟩
  filter_upwards [ae_all_iff.2 hTf] with x hx
  refine le_antisymm (iSup_le fun q => ?_) (le_of_forall_lt fun r hr => ?_)
  · by_cases hq : x ∈ T q
    · exact (indicator_of_mem hq _).trans_le ((hx q).1 hq).le
    · simp [indicator_of_notMem hq]
  · obtain ⟨q, -, hrq, hqf⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hr
    rw [ENNReal.ofNNReal_toNNReal] at hrq hqf
    exact hrq.trans_le <| le_iSup_of_le q
      (indicator_of_mem ((hx q).2 hqf) fun _ => ENNReal.ofReal q).ge

end MeasureTheory

end TauCeti
