/-
Copyright (c) 2026 AIs@home (Qwen3.8 27B). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AIs@home (Qwen3.8 27B)
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Pullbacks below the rank of the range

A continuous alternating map pulled back along a continuous linear map is zero when the
range of the map is a finite module of rank strictly less than the number of arguments.
-/

public section

namespace ContinuousAlternatingMap

variable {K M N M' ι : Type*} [Ring K] [StrongRankCondition K] [IsDomain K]
  [AddCommGroup M] [Module K M] [TopologicalSpace M]
  [AddCommGroup N] [Module K N] [Module.IsTorsionFree K N]
  [TopologicalSpace N] [AddCommGroup M'] [Module K M'] [TopologicalSpace M'] [Fintype ι]

/-- Pulling a continuous alternating map back along a continuous linear map gives zero when
the range of the map is a finite module of rank strictly less than the number of arguments. -/
theorem compContinuousLinearMap_eq_zero_of_range_finrank_lt
    (ω : M [⋀^ι]→L[K] N) (L : M' →L[K] M)
    [Module.Finite K (LinearMap.range L.toLinearMap)]
    (h : Module.finrank K (LinearMap.range L.toLinearMap) < Fintype.card ι) :
    ω.compContinuousLinearMap L = 0 := by
  classical
  ext v
  rw [compContinuousLinearMap_apply]
  let s : Submodule K M := LinearMap.range L.toLinearMap
  let w : ι → s := fun i ↦ ⟨L (v i), ⟨v i, rfl⟩⟩
  -- The family lies in the finite range `s`, so more than `finrank K s` of it are
  -- linearly dependent, and an alternating map vanishes on such a family.
  have hlin : ¬LinearIndependent K w :=
    fun hli ↦ Nat.not_le_of_gt h (hli.fintype_card_le_finrank)
  exact (ω.toAlternatingMap.compLinearMap s.subtype).map_linearDependent w hlin

end ContinuousAlternatingMap
