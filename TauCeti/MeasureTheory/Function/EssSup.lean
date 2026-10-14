/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Essential suprema on the support of a measure

For a nonnegative extended-valued lower semicontinuous function, its essential supremum is
its pointwise supremum on the support, provided that support is conull. In particular this
holds on hereditarily Lindelöf spaces, without a finiteness assumption on the measure.

This identifies essential bounds on continuous observables, such as distance from a fixed
point, with geometric bounds on the support. Lower semicontinuity is important: an upward
change at a single null point need not affect the essential supremum.

The file also records two facts about the essential oscillation `essSup f μ - essInf f μ` of a
real function: an essentially bounded function takes values between its essential infimum and
supremum almost everywhere (`TauCeti.ae_mem_Icc_essInf_essSup`), and a function with values in
an interval of length `L` has essential oscillation at most `L`
(`TauCeti.essSup_sub_essInf_le`). Together they make the essential oscillation on a ball the
smallest length of an interval containing the function there, which is how oscillation decay
estimates are iterated.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}

/-- The essential supremum of a lower semicontinuous nonnegative extended-valued function
is its supremum on the support, whenever the support is conull. -/
theorem essSup_eq_iSup_support (f : X → ℝ≥0∞)
    (hf : LowerSemicontinuous f) (hμ : μ.support ∈ ae μ) :
    essSup f μ = ⨆ x ∈ μ.support, f x := by
  apply le_antisymm
  · exact essSup_le_of_ae_le _ (by
      filter_upwards [hμ] with x hx
      exact le_iSup₂_of_le x hx le_rfl)
  · have hsub := μ.support_subset_of_isClosed (hf.isClosed_preimage (essSup f μ))
      (ENNReal.ae_le_essSup f)
    exact iSup₂_le fun x hx ↦ hsub hx

section Oscillation

variable {α β : Type*} [MeasurableSpace α] {ν : Measure α}

/-- A function that is essentially bounded above and below takes values between its essential
infimum and its essential supremum almost everywhere. -/
theorem ae_mem_Icc_essInf_essSup [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [FirstCountableTopology β] [OrderTopology β] {f : α → β}
    (hf₁ : Filter.IsBoundedUnder (· ≤ ·) (ae ν) f)
    (hf₂ : Filter.IsBoundedUnder (· ≥ ·) (ae ν) f) :
    ∀ᵐ x ∂ν, f x ∈ Set.Icc (essInf f ν) (essSup f ν) := by
  filter_upwards [ae_le_essSup hf₁, ae_essInf_le hf₂] with x hx₁ hx₂
  exact ⟨hx₂, hx₁⟩

/-- A real function taking values almost everywhere in an interval of length `L` has essential
oscillation at most `L`. -/
theorem essSup_sub_essInf_le [(ae ν).NeBot] {f : α → ℝ} {m L : ℝ}
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc m (m + L)) : essSup f ν - essInf f ν ≤ L := by
  have hsup : essSup f ν ≤ m + L := essSup_le_of_ae_le _ (hf.mono fun _ hx => hx.2)
    (Filter.isCoboundedUnder_le_of_eventually_le _ (hf.mono fun _ hx => hx.1))
  have hinf : m ≤ essInf f ν := le_essInf_of_ae_le _ (hf.mono fun _ hx => hx.1)
    (Filter.isCoboundedUnder_ge_of_eventually_le _ (hf.mono fun _ hx => hx.2))
  linarith

end Oscillation

end TauCeti
