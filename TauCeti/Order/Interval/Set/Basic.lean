/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic

/-!
# Interleaving of open intervals in a linear order

Two open intervals `Set.Ioo x y` and `Set.Ioo m M` with `m < M`, `x ≠ m`, and `y ≠ M` interleave
along a linear order (`x < m < y < M` or `m < x < M < y`) if and only if strictly one of the
endpoints `m, M` belongs to `Set.Ioo x y`.

## Main results

* `Set.mem_Ioo_and_notMem_Ioo_iff`: for `m < M` and `y ≠ M`, `m ∈ Ioo x y ∧ M ∉ Ioo x y` holds iff
  `x < m < y < M`.
* `Set.notMem_Ioo_and_mem_Ioo_iff`: for `m < M` and `x ≠ m`, `m ∉ Ioo x y ∧ M ∈ Ioo x y` holds iff
  `m < x < M < y`.
* `Set.xor_mem_Ioo_iff`: for `m < M`, `x ≠ m`, and `y ≠ M`, `Xor (m ∈ Ioo x y) (M ∈ Ioo x y)`
  holds iff the two intervals interleave in one of the two alternating orders.
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {x y m M : α}

/-- When `m < M` and `y ≠ M`, the lower endpoint `m` lies in `Ioo x y` while `M` does not if and
only if the endpoints alternate as `x < m < y < M`. -/
theorem mem_Ioo_and_notMem_Ioo_iff (hmM : m < M) (hyM : y ≠ M) :
    m ∈ Ioo x y ∧ M ∉ Ioo x y ↔ x < m ∧ m < y ∧ y < M := by
  simp only [mem_Ioo]
  refine ⟨fun ⟨⟨hxm, hmy⟩, hM⟩ => ⟨hxm, hmy, ?_⟩,
    fun ⟨hxm, hmy, hyM'⟩ => ⟨⟨hxm, hmy⟩, fun ⟨_, hMy⟩ => lt_asymm hyM' hMy⟩⟩
  exact lt_of_le_of_ne (not_lt.mp fun hMy => hM ⟨lt_trans hxm hmM, hMy⟩) hyM

/-- When `m < M` and `x ≠ m`, the upper endpoint `M` lies in `Ioo x y` while `m` does not if and
only if the endpoints alternate as `m < x < M < y`. -/
theorem notMem_Ioo_and_mem_Ioo_iff (hmM : m < M) (hxm : x ≠ m) :
    m ∉ Ioo x y ∧ M ∈ Ioo x y ↔ m < x ∧ x < M ∧ M < y := by
  simp only [mem_Ioo]
  refine ⟨fun ⟨hm, ⟨hxM, hMy⟩⟩ => ⟨?_, hxM, hMy⟩,
    fun ⟨hmx, hxM, hMy⟩ => ⟨fun ⟨hxm', _⟩ => lt_asymm hmx hxm', ⟨hxM, hMy⟩⟩⟩
  exact lt_of_le_of_ne (not_lt.mp fun hxm' => hm ⟨hxm', lt_trans hmM hMy⟩) hxm.symm

/-- Two open intervals `Ioo x y` and `Ioo m M` with `m < M`, `x ≠ m`, and `y ≠ M` interleave if
and only if strictly one of `m` and `M` lies in `Ioo x y`. -/
theorem xor_mem_Ioo_iff (hmM : m < M) (hxm : x ≠ m) (hyM : y ≠ M) :
    Xor (m ∈ Ioo x y) (M ∈ Ioo x y) ↔
      (x < m ∧ m < y ∧ y < M) ∨ (m < x ∧ x < M ∧ M < y) := by
  rw [Xor, mem_Ioo_and_notMem_Ioo_iff hmM hyM, and_comm (a := M ∈ Ioo x y),
    notMem_Ioo_and_mem_Ioo_iff hmM hxm]

end Set
