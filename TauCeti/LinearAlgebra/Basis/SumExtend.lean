/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The original vectors of `Module.Basis.sumExtend`

`Module.Basis.sumExtend hs` completes a linearly independent family `v` to a basis indexed by
`ι ⊕ sumExtendIndex hs`. This file records that the basis restricts to `v` on the left summand, so
that users need not unfold the construction. In finite dimension, the new vectors may be indexed
by any finite type `κ` of the right cardinality
(`Module.Basis.exists_basis_sum_apply_inl`).
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

/-- In finite dimension, a linearly independent family `v` indexed by `ι` extends to a basis
indexed by `ι ⊕ κ`, for any finite `κ` with `|ι| + |κ| = dim V`, with the original vectors at the
`Sum.inl` positions. -/
theorem exists_basis_sum_apply_inl [Module.Finite K V] {κ : Type*} [Finite κ]
    (hs : LinearIndependent K v) (h : Nat.card ι + Nat.card κ = Module.finrank K V) :
    ∃ b : Basis (ι ⊕ κ) K V, ∀ i, b (.inl i) = v i := by
  let b₀ := sumExtend hs
  have := Module.Finite.finite_basis b₀
  have : Finite ι := .of_injective (Sum.inl : _ → ι ⊕ sumExtendIndex hs) Sum.inl_injective
  have : Finite (sumExtendIndex hs) :=
    .of_injective (Sum.inr : _ → ι ⊕ _) Sum.inr_injective
  have hcard : Nat.card (sumExtendIndex hs) = Nat.card κ := by
    rw [Module.finrank_eq_nat_card_basis b₀, Nat.card_sum] at h
    omega
  exact ⟨b₀.reindex (Equiv.sumCongr (Equiv.refl ι) (Finite.card_eq.mp hcard).some),
    fun i ↦ by simp [b₀]⟩

end Module.Basis
