/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Telescoping comparison of convergent sequences

Two sequences `f g : ℕ → α` in an ordered topological additive group that tend to the same limit
can be compared through their decrements: if from index `m` on every decrement
`f n - f (n + 1)` is at most the corresponding decrement `g n - g (n + 1)`, then `f m ≤ g m`.
Indeed `g n - f n` is then antitone from `m` on and tends to `0`, so it is nonnegative. This is
the usual way to turn a bound on consecutive differences into a bound on the terms, for instance
for the error term of an asymptotic expansion whose limit is known.

## Main results

* `TauCeti.le_of_tendsto_of_sub_succ_le` — the telescoping comparison above.
-/

public section

open Filter Topology

namespace TauCeti

variable {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] [TopologicalSpace α]
  [OrderClosedTopology α] [ContinuousSub α]

/-- **Telescoping comparison.** If `f` and `g` tend to the same limit and every decrement of `f`
from index `m` on is at most the corresponding decrement of `g`, then `f m ≤ g m`. -/
theorem le_of_tendsto_of_sub_succ_le {f g : ℕ → α} {m : ℕ} {a : α} (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 a)) (h : ∀ n, m ≤ n → f n - f (n + 1) ≤ g n - g (n + 1)) :
    f m ≤ g m := by
  have hanti : Antitone fun k ↦ g (k + m) - f (k + m) := antitone_nat_of_succ_le fun k ↦ by
    have := h (k + m) (Nat.le_add_left m k)
    rw [Nat.add_right_comm, sub_le_sub_iff, add_comm (g _)]
    rwa [sub_le_sub_iff] at this
  have hlim : Tendsto (fun k ↦ g (k + m) - f (k + m)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hg.sub hf).comp (tendsto_add_atTop_nat m)
  simpa using hanti.le_of_tendsto hlim 0

end TauCeti
