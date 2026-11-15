/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.LocallyConstant.Basic

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

Two upper semicontinuous functions with values in `ℕ` whose sum is locally constant are each
locally constant (`UpperSemicontinuous.isLocallyConstant_of_isLocallyConstant_add`): near a point
neither can increase, so neither can decrease. This is how constancy of a sum of fibre dimensions
forces constancy of each summand.
-/

public section

open Topology

namespace TauCeti

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β]

/-- A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s` is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_nhds (G : Set X → β) :
    LowerSemicontinuous fun x ↦ ⨆ s ∈ 𝓝 x, G s := by
  intro x c hc
  obtain ⟨s, hcs⟩ := lt_iSup_iff.1 hc
  obtain ⟨hs, hcs⟩ := lt_iSup_iff.1 hcs
  filter_upwards [eventually_mem_nhds_iff.2 hs] with y hy
  exact hcs.trans_le (le_iSup₂_of_le s hy le_rfl)

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

namespace UpperSemicontinuous

variable {X : Type*} [TopologicalSpace X] {u v : X → ℕ}

/-- If two upper semicontinuous functions with values in `ℕ` have a locally constant sum, then the
first is locally constant. -/
theorem isLocallyConstant_of_isLocallyConstant_add (hu : UpperSemicontinuous u)
    (hv : UpperSemicontinuous v) (h : IsLocallyConstant fun x ↦ u x + v x) :
    IsLocallyConstant u := by
  refine (IsLocallyConstant.iff_eventually_eq u).2 fun x ↦ ?_
  filter_upwards [hu x _ (Nat.lt_succ_self _), hv x _ (Nat.lt_succ_self _), h.eventually_eq x]
    with y hux hvx hx
  omega

end UpperSemicontinuous
