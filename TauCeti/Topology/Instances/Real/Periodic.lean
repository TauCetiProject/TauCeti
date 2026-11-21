/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Order.Interval.Set.Basic

/-!
# Boundedness of periodic families over a compact space

A family `f t x`, periodic in the real parameter `t` with a nonzero period and jointly continuous
in `(t, x)` with `x` in a compact space, is bounded
(`Function.Periodic.exists_bound_of_continuous_uncurry`). This is the parametrised version of
Mathlib's `Function.Periodic.isBounded_of_continuous`; time-periodic Hamiltonians on a compact
manifold are the basic example.
-/

public section

open Set

namespace Function

/-- A family `f t x`, periodic in `t ∈ ℝ` with a nonzero period and jointly continuous in
`(t, x)` with `x` in a compact space, is bounded. -/
theorem Periodic.exists_bound_of_continuous_uncurry {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [SeminormedAddGroup E] {f : ℝ → X → E} {c : ℝ} (hf : Periodic f c)
    (hc : c ≠ 0) (hcont : Continuous (uncurry f)) : ∃ B, ∀ t x, ‖f t x‖ ≤ B := by
  -- A positive period of `f`.
  have hf' : Periodic f |c| := by
    rcases abs_choice c with h | h <;> rw [h]
    exacts [hf, hf.neg]
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := |c|)).prod
    (isCompact_univ (X := X))).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨B, fun t x ↦ ?_⟩
  obtain ⟨t', ht', hft⟩ := hf'.exists_mem_Ico₀ (abs_pos.2 hc) t
  simpa only [hft, uncurry_apply_pair] using hB (t', x) ⟨Ico_subset_Icc_self ht', mem_univ x⟩

end Function
