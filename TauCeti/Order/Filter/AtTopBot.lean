/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Diagonal indices along `atTop`

If for every `k` a property `P k n` holds for all large `n`, then an index `κ n` tending to
infinity can be chosen so slowly that `P (κ n) n` holds for all large `n`
(`TauCeti.exists_tendsto_atTop_of_forall_eventually`). This is the diagonal step of constructions
that must meet countably many eventual requirements at once with a single sequence, such as a
recovery sequence built from a countable neighbourhood basis. It complements Mathlib's
`Filter.extraction_forall_of_eventually`, which meets the requirements along a subsequence
instead.
-/

public section

open Filter

namespace TauCeti

/-- If for every `k` the property `P k n` holds for all large `n`, then there is an index `κ n`
tending to infinity with `P (κ n) n` for all large `n`. -/
theorem exists_tendsto_atTop_of_forall_eventually {P : ℕ → ℕ → Prop}
    (h : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧ ∀ᶠ n in atTop, P (κ n) n := by
  classical
  choose N hN using fun k ↦ eventually_atTop.1 (h k)
  -- `κ n` is the largest `k ≤ n` such that `N j ≤ n` for every `j ≤ k`.
  refine ⟨fun n ↦ Nat.findGreatest (fun k ↦ ∀ j ≤ k, N j ≤ n) n, tendsto_atTop.2 fun k ↦ ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop k, (eventually_all_finset (Finset.range (k + 1))).2
      fun j _ ↦ eventually_ge_atTop (N j)] with n hkn hn
    exact Nat.le_findGreatest hkn fun j hj ↦ hn j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    refine hN _ _ (Nat.findGreatest_spec (P := fun k ↦ ∀ j ≤ k, N j ≤ n) (Nat.zero_le n)
      (fun j hj ↦ ?_) _ le_rfl)
    rwa [Nat.le_zero.1 hj]

end TauCeti
