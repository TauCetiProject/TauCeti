/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lower semicontinuity of suprema over neighbourhoods

A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s`, for an arbitrary `G : Set X → β` with values in a
complete linear order, is lower semicontinuous (`TauCeti.lowerSemicontinuous_iSup_nhds`): a strict
lower bound witnessed by a neighbourhood of `x` is witnessed by the same set at every point of its
interior. Lower envelopes and lower and upper Γ-limits are of this form.

A lower semicontinuous subadditive function `A` with values in `ℝ≥0∞` and `A 0 = 0`, such as a
lower semicontinuous extended seminorm, satisfies the triangle inequality for convergent series:
`A (∑ f) ≤ ∑' b, A (f b)` (`LowerSemicontinuous.le_tsum_of_hasSum`). No continuity of `A` is needed,
because the bound on the partial sums passes to their limit through the closed sublevel set.
-/

public section

open Set Topology

namespace TauCeti

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β]

/-- A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s` is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_nhds (G : Set X → β) :
    LowerSemicontinuous fun x ↦ ⨆ s ∈ 𝓝 x, G s := by
  intro x c hc
  obtain ⟨s, hcs⟩ := lt_iSup_iff.1 hc
  obtain ⟨hs, hcs⟩ := lt_iSup_iff.1 hcs
  filter_upwards [interior_mem_nhds.2 hs] with y hy
  exact hcs.trans_le (le_iSup₂ (f := fun s (_ : s ∈ 𝓝 y) ↦ G s) s (mem_interior_iff_mem_nhds.1 hy))

end TauCeti

open scoped ENNReal

namespace LowerSemicontinuous

variable {E β : Type*} [AddCommMonoid E] [TopologicalSpace E] {A : E → ℝ≥0∞}

/-- A lower semicontinuous subadditive function with values in `ℝ≥0∞` vanishing at zero bounds
the sum of a convergent series by the sum of its values on the terms. -/
theorem le_tsum_of_hasSum (hA : LowerSemicontinuous A) (h0 : A 0 = 0)
    (hadd : ∀ x y, A (x + y) ≤ A x + A y) {f : β → E} {s : E} (hf : HasSum f s) :
    A s ≤ ∑' b, A (f b) :=
  (hA.isClosed_preimage _).mem_of_tendsto hf <| Filter.Eventually.of_forall fun t ↦
    (Finset.le_sum_of_subadditive A h0.le hadd t f).trans (sum_le_tsum t)

end LowerSemicontinuous
