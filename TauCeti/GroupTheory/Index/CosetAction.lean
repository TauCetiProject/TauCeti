/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import TauCeti.GroupTheory.GroupAction.Free
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Index divisibility from coset actions

If a subgroup `K ≤ G` meets every conjugate of `H ≤ G` trivially, then `K` acts freely on the
coset space `G ⧸ H`, so `Nat.card K` divides `H.index`.

## Main results

* `Subgroup.natCard_dvd_index_of_forall_conj_mem`: if `K` meets every conjugate of `H` trivially,
  then `Nat.card K ∣ H.index`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- If a subgroup `K` meets every conjugate of `H` trivially, then `Nat.card K` divides `H.index`.
No finiteness assumption is needed since `H.index` vanishes when `G ⧸ H` is infinite. -/
theorem natCard_dvd_index_of_forall_conj_mem {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ g : G, g⁻¹ * k * g ∈ H → k = 1) : Nat.card K ∣ H.index := by
  have : IsCancelSMul K (G ⧸ H) := isCancelSMul_quotient_iff.mpr h
  rw [H.index_eq_card]
  exact MulAction.natCard_dvd_natCard_of_isCancelSMul

end Subgroup
