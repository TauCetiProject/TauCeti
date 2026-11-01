/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import TauCeti.Topology.Order.LeftRight

/-!
# Measurability of the running maximum of a right-continuous process

The event `{∃ t ≤ T, a < X_t}` and the running maximum `sup_{t ≤ T} X_t` of a process `X` involve
uncountably many times, so they need not be measurable even when every `X_t` is. If the paths of
`X` are almost surely right-continuous before `T` and the time set is densely ordered and separable
(for instance `ℝ≥0`), the running maximum agrees almost everywhere with a supremum over countably
many times, hence is almost everywhere measurable whenever every `X_t` is.

## Main declarations

* `MeasureTheory.aemeasurable_iSup_le_ofReal`: the running maximum of a process with almost
  everywhere measurable values and right-continuous paths is almost everywhere measurable.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [TopologicalSpace.SeparableSpace ι]

/-- The running maximum `sup_{t ≤ T} X_t` of a process whose values `X_t` are almost everywhere
measurable and whose paths are almost surely right-continuous before `T` is almost everywhere
measurable: it agrees almost everywhere with the supremum over a countable set of times. -/
theorem aemeasurable_iSup_le_ofReal {X : ι → Ω → ℝ} (hX : ∀ t, AEMeasurable (X t) μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (X t ω)) μ := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ) T
  have := hSc.to_subtype
  refine (AEMeasurable.iSup fun s : S ↦ (hX s).ennreal_ofReal).congr ?_
  filter_upwards [hcont] with ω hω
  refine le_antisymm (iSup_le fun s ↦ le_iSup₂_of_le s (hST s.2) le_rfl) ?_
  refine iSup₂_le fun t htT ↦ le_of_forall_lt fun a ha ↦ ?_
  have hatop : a ≠ ∞ := ha.ne_top
  rw [← ENNReal.ofReal_toReal hatop, ENNReal.ofReal_lt_ofReal_iff'] at ha
  obtain ⟨s, hs, has⟩ := hS hω htT ha.1
  refine lt_of_lt_of_le ?_ (le_iSup _ (⟨s, hs⟩ : S))
  rwa [← ENNReal.ofReal_toReal hatop, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]

end MeasureTheory
