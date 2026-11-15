/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Periodic

/-!
# Eventually periodic sequences on `ℕ`

A sequence `a : ℕ → α` with `a (n + p) = a n` for all `n ≥ N` is periodic of period `p` beyond
the preperiod `N`. This file reduces its values beyond `N` to the window `[N, N + p)`, the
eventually periodic variant of Mathlib's `Function.Periodic.map_mod_nat`.

## Main results

* `TauCeti.Nat.apply_eq_apply_add_sub_mod`: beyond the preperiod `N`, the value at `n` is the
  value at `N + (n - N) % p`.
-/

public section

namespace TauCeti.Nat

/-- Beyond the preperiod `N`, an eventually periodic sequence takes at `n` its value at the
representative of `n` modulo `p` in `[N, N + p)`. -/
theorem apply_eq_apply_add_sub_mod {α : Type*} {a : ℕ → α} {N p : ℕ}
    (h : ∀ n, N ≤ n → a (n + p) = a n) {n : ℕ} (hn : N ≤ n) : a n = a (N + (n - N) % p) := by
  have hper : Function.Periodic (fun m ↦ a (N + m)) p := fun m ↦
    (congrArg a (Nat.add_assoc N m p).symm).trans (h _ (Nat.le_add_right N m))
  simpa [Nat.add_sub_cancel' hn] using (hper.map_mod_nat (n - N)).symm

end TauCeti.Nat
