/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Codimension of a common kernel

The simultaneous equations given by a finite family of linear maps remove at most as many
dimensions as the sum of their individual ranks. The targets can be different spaces.
-/

public section

namespace LinearMap

/-- The codimension of the common kernel of finitely many maps is bounded by the sum of the
ranks of the maps. The bound counts image dimensions, even for infinite-dimensional targets.
For an infinite-dimensional source the left-hand `finrank` is zero. -/
theorem finrank_le_finrank_iInf_ker_add_sum_finrank_range {K V ι : Type*} {W : ι → Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [Fintype ι]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (f : ∀ i, V →ₗ[K] W i) :
    Module.finrank K V ≤ Module.finrank K (⨅ i, ker (f i) : Submodule K V) +
      ∑ i, Module.finrank K (range (f i)) := by
  by_cases hV : Module.Finite K V
  · let F := LinearMap.pi fun i ↦ (f i).rangeRestrict
    have hker : ker F = ⨅ i, ker (f i) := by simp [F, LinearMap.ker_pi]
    have hrank := F.finrank_range_add_finrank_ker
    rw [hker] at hrank
    have hle := F.range.finrank_le
    rw [Module.finrank_pi_fintype] at hle
    omega
  · rw [Module.finrank_of_not_finite hV]
    exact Nat.zero_le _

end LinearMap
