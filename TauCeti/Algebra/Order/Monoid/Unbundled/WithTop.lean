/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Natural scalar multiplication and unique divisibility on `WithTop`

For an additive monoid `α` and a nonzero natural number `n`, left multiplication by `n` fixes `⊤`
in `WithTop α` and therefore acts as `WithTop.map (n • ·)`. Consequently, `WithTop α` inherits
`HasUniqueDiv` from `α`.

## Main results

* `WithTop.nsmul_top_of_ne_zero`: `n • (⊤ : WithTop α) = ⊤` for `n ≠ 0`.
* `WithTop.nsmul_eq_map_of_ne_zero`: `n • x = x.map (n • ·)` for `n ≠ 0`.
* `WithTop.instHasUniqueDiv`: `HasUniqueDiv α` passes to `WithTop α`.
-/

public section

namespace WithTop

/-- Multiplying `⊤ : WithTop α` by a nonzero natural number returns `⊤`. -/
theorem nsmul_top_of_ne_zero {α : Type*} [AddMonoid α] {n : ℕ} (hn : n ≠ 0) :
    n • (⊤ : WithTop α) = ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [succ_nsmul, WithTop.add_top]

/-- For a nonzero natural number `n`, `n • ·` on `WithTop α` agrees with
`WithTop.map (n • ·)`. -/
theorem nsmul_eq_map_of_ne_zero {α : Type*} [AddMonoid α] {n : ℕ} (hn : n ≠ 0)
    (x : WithTop α) : n • x = x.map (n • ·) := by
  cases x <;> simp [nsmul_top_of_ne_zero hn]

/-- `WithTop α` has unique division by nonzero natural numbers whenever `α` does. -/
instance instHasUniqueDiv {α : Type*} [AddMonoid α] [HasUniqueDiv α] :
    HasUniqueDiv (WithTop α) where
  nsmul_right_injective _ hn _ _ h :=
    WithTop.map_injective (nsmul_right_injective hn)
      (by rwa [← nsmul_eq_map_of_ne_zero hn, ← nsmul_eq_map_of_ne_zero hn])

end WithTop
