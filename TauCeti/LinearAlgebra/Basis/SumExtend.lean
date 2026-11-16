/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The original vectors of `Module.Basis.sumExtend`

`Module.Basis.sumExtend hs` completes a linearly independent family `v` to a basis indexed by
`ι ⊕ sumExtendIndex hs`. This file records that the basis restricts to `v` on the left summand, so
that users need not unfold the construction.
-/

public section

namespace Module.Basis

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {v : ι → V}

/-- The extended basis `Module.Basis.sumExtend hs` agrees with `v` on the left summand. -/
@[simp]
theorem sumExtend_apply_inl (hs : LinearIndependent K v) (i : ι) :
    sumExtend hs (.inl i) = v i := by
  simp only [sumExtend, reindex_apply, coe_extend]
  -- `Module.Basis.sumExtend` decides membership in the range of `v` classically.
  exact congrArg Subtype.val
    (@Equiv.Set.sumDiffSubset_apply_inl _ _ _
      (hs.linearIndepOn_id.subset_extend (Set.subset_univ _)) (Classical.decPred _) _)

end Module.Basis
