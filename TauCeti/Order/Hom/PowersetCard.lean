/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.PowersetCard

/-!
# The top block of indices as a fixed-cardinality subset

For `k + p = N`, the indices `k, …, N - 1` of `Fin N` form the `p`-subset `TauCeti.topBlock h`,
built through `Set.powersetCard.ofFinEmbEquiv` from the order embedding `a ↦ k + a`. Its increasing
enumeration is `a ↦ k + a`, an index lies in it exactly when it is at least `k`, and every other
`p`-subset meets the first `k` indices.
-/

public section

open Set.powersetCard

namespace TauCeti

variable {p N : ℕ}

/-- **The top block** `{k, …, N - 1}` of the indices of `Fin N`, for `k + p = N`, as a
`p`-subset. -/
def topBlock {k : ℕ} (h : k + p = N) : Set.powersetCard (Fin N) p :=
  ofFinEmbEquiv ((Fin.natAddOrderEmb k).trans (Fin.castOrderIso h).toOrderEmbedding)

/-- The `a`-th index of the top block, in increasing order, is `k + a`. -/
@[simp]
theorem val_ofFinEmbEquiv_symm_topBlock {k : ℕ} (h : k + p = N) (a : Fin p) :
    (ofFinEmbEquiv.symm (topBlock h) a : ℕ) = k + a := by
  simp [topBlock]

/-- An index lies in the top block exactly when it is at least `k`. -/
@[simp]
theorem mem_topBlock {k : ℕ} (h : k + p = N) {j : Fin N} : j ∈ topBlock h ↔ k ≤ (j : ℕ) := by
  rw [← mem_range_ofFinEmbEquiv_symm_iff_mem]
  refine ⟨?_, fun hj ↦ ⟨⟨j - k, by omega⟩, Fin.ext ?_⟩⟩
  · rintro ⟨a, rfl⟩
    simp
  · simp only [val_ofFinEmbEquiv_symm_topBlock]
    omega

/-- **A `p`-subset other than the top block meets the first `k` indices.** -/
theorem exists_lt_of_ne_topBlock {k : ℕ} (h : k + p = N) {J : Set.powersetCard (Fin N) p}
    (hJ : J ≠ topBlock h) : ∃ j ∈ J, (j : ℕ) < k := by
  by_contra! hc
  exact hJ (eq_iff_subset.2 fun j hj ↦ (mem_topBlock h).2 (hc j hj))

end TauCeti
