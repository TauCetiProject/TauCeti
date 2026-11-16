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

On a closed subset `s`, lower semicontinuity of a function into a linear order is equivalent to
closedness of every relative sublevel `{x ∈ s | f x ≤ b}`
(`TauCeti.lowerSemicontinuousOn_iff_isClosed_sublevel`).
-/

public section

open Set Topology

namespace TauCeti

variable {X β : Type*} [TopologicalSpace X]

/-- A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s` is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_nhds [CompleteLinearOrder β] (G : Set X → β) :
    LowerSemicontinuous fun x ↦ ⨆ s ∈ 𝓝 x, G s := by
  intro x c hc
  obtain ⟨s, hcs⟩ := lt_iSup_iff.1 hc
  obtain ⟨hs, hcs⟩ := lt_iSup_iff.1 hcs
  filter_upwards [eventually_mem_nhds_iff.2 hs] with y hy
  exact hcs.trans_le (le_iSup₂_of_le s hy le_rfl)

/-- On a closed set, lower semicontinuity of a function into a linear order is equivalent to
closedness of every relative sublevel `{x ∈ s | f x ≤ b}`. -/
theorem lowerSemicontinuousOn_iff_isClosed_sublevel [LinearOrder β] {f : X → β} {s : Set X}
    (hs : IsClosed s) :
    LowerSemicontinuousOn f s ↔ ∀ b, IsClosed {x ∈ s | f x ≤ b} := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  refine ⟨fun h b ↦ ?_, fun h b ↦ ⟨{x ∈ s | f x ≤ b}, h b, ?_⟩⟩
  · obtain ⟨v, hv, heq⟩ := h b
    have hsub : {x ∈ s | f x ≤ b} = s ∩ f ⁻¹' Iic b := by ext x; simp
    rw [hsub, heq]
    exact hs.inter hv
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_ofPred_eq, and_self_left]

end TauCeti

namespace LowerSemicontinuousOn

/-- On a closed set, every relative sublevel of a lower semicontinuous function into a linear
order is closed. -/
theorem isClosed_sublevel {X β : Type*} [TopologicalSpace X] [LinearOrder β]
    {f : X → β} {s : Set X} (hf : LowerSemicontinuousOn f s) (hs : IsClosed s) (b : β) :
    IsClosed {x ∈ s | f x ≤ b} :=
  (TauCeti.lowerSemicontinuousOn_iff_isClosed_sublevel hs).1 hf b

end LowerSemicontinuousOn

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
