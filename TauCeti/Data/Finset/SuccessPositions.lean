/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Range
public import Mathlib.Order.Lattice.Nat

/-!
# Failures before a prescribed success

A finite set of natural numbers records the zero-based positions of successful draws.
`Finset.failuresBeforeSuccess s r` counts failures before the `r`th success, with zero
for `r = 0` or when fewer than `r` successes occur. Its cumulative characterization
relates this stopping count to the number of successes in a fixed draw prefix.
-/

public section

noncomputable section

namespace Finset

/-- The number of failures before success `r`, for zero-based success positions `s`.
It is zero if `r = 0` or `s` contains fewer than `r` successes. -/
def failuresBeforeSuccess (s : Finset ℕ) (r : ℕ) : ℕ :=
  sInf {k : ℕ | r ≤ (s ∩ range (k + r)).card}

/-- If `r ≤ s.card`, the stopping count is the least failure allowance for which the
corresponding prefix contains at least `r` successes. Otherwise, the count is zero. -/
theorem failuresBeforeSuccess_def (s : Finset ℕ) (r : ℕ) :
    s.failuresBeforeSuccess r = sInf {k : ℕ | r ≤ (s ∩ range (k + r)).card} := (rfl)

private theorem nonempty_success_prefix (s : Finset ℕ) {r : ℕ} (hr : r ≤ s.card) :
    {k : ℕ | r ≤ (s ∩ range (k + r)).card}.Nonempty := by
  obtain ⟨n, hn⟩ := exists_nat_subset_range s
  refine ⟨n, ?_⟩
  have hinter : s ∩ range (n + r) = s :=
    inter_eq_left.mpr (hn.trans (range_mono (Nat.le_add_right n r)))
  simpa only [Set.mem_ofPred_eq, hinter] using hr

/-- At most `k` failures precede success `r` exactly when the first `k + r` draws
contain at least `r` successes. The assumption ensures that success `r` exists. -/
@[simp]
theorem failuresBeforeSuccess_le_iff (s : Finset ℕ) {r k : ℕ} (hr : r ≤ s.card) :
    s.failuresBeforeSuccess r ≤ k ↔ r ≤ (s ∩ range (k + r)).card := by
  constructor
  · intro hk
    have hhit : r ≤ (s ∩ range (s.failuresBeforeSuccess r + r)).card :=
      Nat.sInf_mem (nonempty_success_prefix s hr)
    exact hhit.trans (card_le_card (inter_subset_inter_left
      (range_mono (Nat.add_le_add_right hk r))))
  · intro hk
    exact Nat.sInf_le (s := {j : ℕ | r ≤ (s ∩ range (j + r)).card}) hk

/-- Waiting for zero successes incurs zero failures. -/
@[simp]
theorem failuresBeforeSuccess_zero (s : Finset ℕ) : s.failuresBeforeSuccess 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le (by simp))

/-- If the requested success never occurs, the stopping count is totalized to zero. -/
@[simp]
theorem failuresBeforeSuccess_of_card_lt (s : Finset ℕ) {r : ℕ} (hr : s.card < r) :
    s.failuresBeforeSuccess r = 0 := by
  have hempty : {k : ℕ | r ≤ (s ∩ range (k + r)).card} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    exact (not_le_of_gt hr) (hk.trans (card_le_card inter_subset_left))
  rw [failuresBeforeSuccess_def, hempty, Nat.sInf_empty]

end Finset
