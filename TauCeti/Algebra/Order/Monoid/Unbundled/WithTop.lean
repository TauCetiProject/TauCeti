/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Scalar multiplication on `WithTop` via `WithTop.map`

In `WithTop α` for an additive monoid `α`, scalar multiplication by `0 : ℕ` sends `⊤` to `0`,
whereas scalar multiplication by a nonzero `n : ℕ` fixes `⊤` and acts on finite elements via
`WithTop.map (n • ·)`.

## Main results

* `WithTop.nsmul_eq_map`: for `n ≠ 0` and `x : WithTop α`, `n • x = x.map (n • ·)`.
-/

public section

namespace WithTop

/-- For a nonzero natural number `n`, scalar multiplication by `n` on `WithTop α` agrees with
`WithTop.map (n • ·)`. -/
theorem nsmul_eq_map {α : Type*} [AddMonoid α] {n : ℕ} (hn : n ≠ 0) (x : WithTop α) :
    n • x = x.map (n • ·) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  cases x with
  | top => rw [succ_nsmul, add_top, map_top]
  | coe a => rw [← coe_nsmul, map_coe]

end WithTop
