/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.WithTop

/-!
# Scaling elements of `WithTop`

Left multiplication by `c` acts on `WithTop α` through `WithTop.map (c * ·)`, fixing `⊤`.
This file records how this scaling interacts with `WithTop.untop₀` and that scaling by a
nonzero `c` in a group with zero is undone by scaling by `c⁻¹`. A positive natural-multiple
bound by a finite field element can also be divided by that natural number, excluding `⊤`.

## Main results

* `WithTop.untop₀_map_mul`: `(x.map (c * ·)).untop₀ = c * x.untop₀`.
* `WithTop.map_mul_map_inv_mul`, `WithTop.map_inv_mul_map_mul`: scaling by `c⁻¹` and by a
  nonzero `c` are mutually inverse.
-/

public section

namespace WithTop

/-- Scaling an element by a factor scales its real part; `⊤` keeps the real part zero. -/
@[simp]
theorem untop₀_map_mul {α : Type*} [MulZeroClass α] (c : α) (x : WithTop α) :
    (x.map (c * ·)).untop₀ = c * x.untop₀ := by
  cases x <;> simp

/-- Scaling an element by `c⁻¹` and then by a nonzero `c` gives back the element. -/
theorem map_mul_map_inv_mul {α : Type*} [GroupWithZero α] {c : α} (hc : c ≠ 0)
    (x : WithTop α) : (x.map (c⁻¹ * ·)).map (c * ·) = x := by
  cases x <;> simp [hc]

/-- Scaling an element by a nonzero `c` and then by `c⁻¹` gives back the element. -/
theorem map_inv_mul_map_mul {α : Type*} [GroupWithZero α] {c : α} (hc : c ≠ 0)
    (x : WithTop α) : (x.map (c * ·)).map (c⁻¹ * ·) = x := by
  cases x <;> simp [hc]

/-- A positive natural multiple is bounded by a finite value exactly when its argument is
bounded by the quotient. In particular such a bound excludes infinity. -/
theorem nsmul_le_coe_iff {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : ℕ} (hn : 0 < n) {x : WithTop F} {b : F} :
    n • x ≤ (b : WithTop F) ↔ x ≤ ((b / n : F) : WithTop F) := by
  induction x using WithTop.recTopCoe with
  | top =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [succ_nsmul]
  | coe x =>
    rw [← coe_nsmul, coe_le_coe, coe_le_coe, nsmul_eq_mul,
      le_div_iff₀ (Nat.cast_pos.2 hn), mul_comm]

end WithTop
