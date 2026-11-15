/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import TauCeti.Topology.Order.LeftRight

/-!
# Measurability of the running maximum of a right-continuous process

The event `{∃ t ≤ T, a < X_t}` and the running maximum `sup_{t ≤ T} X_t` of a process `X` involve
uncountably many times, so they need not be measurable even when every `X_t` is. If the paths of
`X` are almost surely right-continuous before `T` and the time set is second countable (for
instance `ℝ≥0` or `ℕ`), the running maximum agrees almost everywhere with a supremum over countably
many times, hence is almost everywhere measurable whenever every `X_t` is.

## Main declarations

* `MeasureTheory.exists_countable_subset_Iic_iSup_ae_eq`: the running supremum of an `ℝ≥0∞`-valued
  process with right-continuous paths before `T` agrees almost everywhere with the supremum over a
  countable set of times `≤ T`.
* `MeasureTheory.exists_countable_subset_Iic_iSup_ofReal_ae_eq` and
  `MeasureTheory.exists_countable_subset_Iic_iSup_eNorm_ae_eq`: specializations to `ENNReal.ofReal`
  of a real-valued process and `‖·‖ₑ` of a `ContinuousENorm`-valued process.
* `MeasureTheory.aemeasurable_iSup_le`, `MeasureTheory.aemeasurable_iSup_le_ofReal`, and
  `MeasureTheory.aemeasurable_iSup_le_eNorm`: almost everywhere measurability of the running
  maximum for `ℝ≥0∞`-, `ℝ`-, and `ContinuousENorm`-valued right-continuous processes.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- The running supremum `⨆ t ≤ T, Y t ω` of an `ℝ≥0∞`-valued process whose paths are almost
surely right-continuous before `T` agrees almost everywhere with the supremum over a single
countable set of times `≤ T`. -/
theorem exists_countable_subset_Iic_iSup_ae_eq {Y : ι → Ω → ℝ≥0∞} {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ Y u ω) (Ioi t) t) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧
      (fun ω ↦ ⨆ t ≤ T, Y t ω) =ᵐ[μ] fun ω ↦ ⨆ t ∈ S, Y t ω := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ≥0∞) T
  refine ⟨S, hSc, hST, ?_⟩
  filter_upwards [hcont] with ω hω
  refine le_antisymm ?_ (iSup₂_le fun s hs ↦ le_iSup₂_of_le s (hST hs) le_rfl)
  refine iSup₂_le fun t htT ↦ le_of_forall_lt fun a ha ↦ ?_
  obtain ⟨s, hs, has⟩ := hS hω htT ha
  exact has.trans_le (le_iSup₂ (f := fun s _ ↦ Y s ω) s hs)

/-- The running supremum `⨆ t ≤ T, Y t ω` of an `ℝ≥0∞`-valued process with almost everywhere
measurable values on `(-∞, T]` and almost surely right-continuous paths before `T` is almost
everywhere measurable. -/
theorem aemeasurable_iSup_le {Y : ι → Ω → ℝ≥0∞} {T : ι}
    (hY : ∀ t ≤ T, AEMeasurable (Y t) μ)
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ Y u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, Y t ω) μ := by
  obtain ⟨S, hSc, hST, hae⟩ := exists_countable_subset_Iic_iSup_ae_eq hcont
  have := hSc.to_subtype
  refine (AEMeasurable.iSup fun s : S ↦ hY s (hST s.2)).congr ?_
  filter_upwards [hae] with ω hω
  rw [hω, iSup_subtype']

/-- For a real-valued process whose paths are almost surely right-continuous before `T`, the
running supremum `⨆ t ≤ T, ENNReal.ofReal (X t ω)` agrees almost everywhere with the supremum over
a countable set of times `≤ T`. -/
theorem exists_countable_subset_Iic_iSup_ofReal_ae_eq {X : ι → Ω → ℝ} {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧
      (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (X t ω)) =ᵐ[μ] fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (X t ω) :=
  exists_countable_subset_Iic_iSup_ae_eq <| hcont.mono fun _ hω t ht ↦
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hω t ht)

/-- The running maximum `sup_{t ≤ T} X_t` of a process whose values `X_t` are almost everywhere
measurable and whose paths are almost surely right-continuous before `T` is almost everywhere
measurable: it agrees almost everywhere with the supremum over a countable set of times. -/
theorem aemeasurable_iSup_le_ofReal {X : ι → Ω → ℝ} (hX : ∀ t, AEMeasurable (X t) μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (X t ω)) μ :=
  aemeasurable_iSup_le (fun t _ ↦ (hX t).ennreal_ofReal) <| hcont.mono fun _ hω t ht ↦
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hω t ht)

/-- For a process valued in a `ContinuousENorm` space whose paths are almost surely
right-continuous before `T`, the running extended norm supremum `⨆ t ≤ T, ‖X t ω‖ₑ` agrees almost
everywhere with the supremum over a countable set of times `≤ T`. -/
theorem exists_countable_subset_Iic_iSup_eNorm_ae_eq {E : Type*} [TopologicalSpace E]
    [ContinuousENorm E] {X : ι → Ω → E} {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧
      (fun ω ↦ ⨆ t ≤ T, ‖X t ω‖ₑ) =ᵐ[μ] fun ω ↦ ⨆ t ∈ S, ‖X t ω‖ₑ :=
  exists_countable_subset_Iic_iSup_ae_eq <| hcont.mono fun _ hω t ht ↦
    ContinuousENorm.continuous_eNorm.continuousAt.comp_continuousWithinAt (hω t ht)

/-- The running extended norm supremum `⨆ t ≤ T, ‖X t ω‖ₑ` of a `ContinuousENorm`-valued process
with almost everywhere measurable extended norms on `(-∞, T]` and almost surely right-continuous
paths before `T` is almost everywhere measurable. -/
theorem aemeasurable_iSup_le_eNorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {X : ι → Ω → E} {T : ι} (hX : ∀ t ≤ T, AEMeasurable (fun ω ↦ ‖X t ω‖ₑ) μ)
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, ‖X t ω‖ₑ) μ :=
  aemeasurable_iSup_le hX <| hcont.mono fun _ hω t ht ↦
    ContinuousENorm.continuous_eNorm.continuousAt.comp_continuousWithinAt (hω t ht)

end MeasureTheory
