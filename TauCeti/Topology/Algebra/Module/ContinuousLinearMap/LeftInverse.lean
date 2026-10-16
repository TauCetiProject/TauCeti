/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Left inverses for triangular operators

An operator on a product which retains the first coordinate admits a continuous linear
left inverse exactly when its restriction to the second factor does. This is the linear
algebra of the differential of a parameter-preserving family of immersions.

The construction uses Mathlib's `ContinuousLinearMap.HasLeftInverse`: subtract the
contribution of the first coordinate, then apply a left inverse on the second factor.
-/

public section

namespace ContinuousLinearMap

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G] [IsTopologicalAddGroup G]

/-- A continuous linear operator retaining the first coordinate is split-injective
exactly when its restriction to the second factor is split-injective. -/
theorem hasLeftInverse_fst_prod_iff (A : E × F →L[R] G) :
    ((fst R E F).prod A).HasLeftInverse ↔ (A.comp (inr R E F)).HasLeftInverse := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨(snd R E F).comp (L.comp (inr R E G)), fun y => ?_⟩
    have hy := congrArg Prod.snd (hL (0, y))
    simpa using hy
  · rintro ⟨L, hL⟩
    refine ⟨(fst R E G).prod
      (L.comp ((snd R E G) - (A.comp (inl R E F)).comp (fst R E G))), ?_⟩
    rintro ⟨x, y⟩
    have hA : A (x, y) - A (x, 0) = A (0, y) := by
      rw [← map_sub]
      simp
    simpa [hA] using congrArg (Prod.mk x) (hL y)

end ContinuousLinearMap
