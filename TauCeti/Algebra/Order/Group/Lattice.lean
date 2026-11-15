/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Lattice

import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Powers and multiples in lattice-ordered groups

Every lattice-ordered group is torsion-free in its order: if `1 ≤ a ^ n` for a nonzero natural
number `n` (additively, `0 ≤ n • a`), then `1 ≤ a` (`0 ≤ a`). This extends `pow_two_semiclosed` /
`nsmul_two_semiclosed` from exponent `2` to arbitrary nonzero exponents, and extends
`one_le_pow_iff` / `nsmul_nonneg_iff` from linearly ordered monoids to lattice-ordered groups
without assuming commutativity.

## Main results

* `TauCeti.inf_one_pow_succ` / `TauCeti.succ_nsmul_inf_zero` : `(a ⊓ 1) ^ (n + 1) =
  a ^ (n + 1) ⊓ (a ⊓ 1) ^ n` in any lattice-ordered group.
* `TauCeti.one_le_pow_iff_of_lattice` / `TauCeti.nsmul_nonneg_iff_of_lattice` : `1 ≤ a ^ n ↔ 1 ≤ a`
  (additively, `0 ≤ n • a ↔ 0 ≤ a`) for `n ≠ 0` in any lattice-ordered group.

## References

* L. Fuchs, *Partially Ordered Algebraic Systems*, Pergamon Press, 1963, Chapter V, §1.E.
* G. Birkhoff, *Lattice-ordered groups*, Ann. of Math. (2) **43** (1942), 298–331.
-/

public section

namespace TauCeti

variable {α : Type*} [Group α] [Lattice α] [MulLeftMono α] [MulRightMono α]

/-- In a lattice-ordered group, `(a ⊓ 1) ^ (n + 1) = a ^ (n + 1) ⊓ (a ⊓ 1) ^ n`, extending the
`n = 1` identity behind `pow_two_semiclosed`. -/
@[to_additive succ_nsmul_inf_zero
  /-- In a lattice-ordered additive group, `(n + 1) • (a ⊓ 0) = (n + 1) • a ⊓ n • (a ⊓ 0)`,
  extending the `n = 1` identity behind `nsmul_two_semiclosed`. -/]
theorem inf_one_pow_succ (a : α) (n : ℕ) :
    (a ⊓ 1) ^ (n + 1) = a ^ (n + 1) ⊓ (a ⊓ 1) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hle : (a ⊓ 1) ^ (m + 1) ≤ a ^ (m + 1) := pow_le_pow_left' inf_le_left (m + 1)
    calc
      (a ⊓ 1) ^ (m + 2) = (a ^ (m + 1) ⊓ (a ⊓ 1) ^ m) * (a ⊓ 1) := by rw [pow_succ, ih]
      _ = a ^ (m + 1) * (a ⊓ 1) ⊓ (a ⊓ 1) ^ (m + 1) := by rw [inf_mul, ← pow_succ]
      _ = a ^ (m + 2) ⊓ (a ⊓ 1) ^ (m + 1) := by
        simp [mul_inf, pow_succ a (m + 1), inf_assoc, hle]

/-- A lattice-ordered group is torsion-free in its order (Fuchs, *Partially Ordered Algebraic
Systems*, Chapter V, §1.E): for `n ≠ 0`, `1 ≤ a ^ n ↔ 1 ≤ a`. This generalizes `pow_two_semiclosed`
from `n = 2` to all nonzero exponents and `one_le_pow_iff` from linear orders to lattices. -/
@[to_additive nsmul_nonneg_iff_of_lattice
  /-- A lattice-ordered additive group is unperforated (Fuchs, *Partially Ordered Algebraic
  Systems*, Chapter V, §1.E): for `n ≠ 0`, `0 ≤ n • a ↔ 0 ≤ a`. This generalizes
  `nsmul_two_semiclosed` from `n = 2` to all nonzero multiples and `nsmul_nonneg_iff` from linear
  orders to lattices. -/]
theorem one_le_pow_iff_of_lattice {a : α} {n : ℕ} (hn : n ≠ 0) :
    1 ≤ a ^ n ↔ 1 ≤ a := by
  refine ⟨fun ha => ?_, fun ha => one_le_pow_of_one_le' ha n⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hle : (a ⊓ 1) ^ k ≤ a ^ (k + 1) := (pow_le_one' inf_le_right k).trans ha
  have hmul : (a ⊓ 1) ^ k * (a ⊓ 1) = (a ⊓ 1) ^ k * 1 := by
    rw [← pow_succ, mul_one, inf_one_pow_succ, inf_of_le_right hle]
  exact inf_eq_right.mp (mul_left_cancel hmul)

end TauCeti
