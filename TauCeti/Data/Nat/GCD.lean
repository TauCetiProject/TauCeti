/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.GCD.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Coprimality and nonzero least common multiples

For `q ≠ 0` and `N ≠ 0`, the natural numbers `q` and `q ^ N - 1` are coprime, because any common
divisor of `q` and `q ^ N - 1` also divides `q ^ N - (q ^ N - 1) = 1`. This is the coprimality
needed to view `q` as a unit of `ZMod (q ^ N - 1)`.

The least common multiple of two nonzero naturals is nonzero, also as a `NeZero` instance.

If the products of two finite families of naturals are coprime and one entry of the first family is
zero, the second family is constantly `1`: a zero entry makes the first product `0`, and `0` is
coprime only to `1`.

## Main results

* `Nat.coprime_pow_sub_one`: `q` is coprime to `q ^ N - 1`.
* `Nat.neZero_lcm`: `NeZero (lcm m n)` for nonzero `m` and `n`.
* `Nat.Coprime.eq_one_of_exists_eq_zero`: coprime products and a zero entry in one family force the
  other family to be `1`.
-/

public section

namespace Nat

/-- The least common multiple of two nonzero natural numbers is nonzero. -/
instance neZero_lcm (m n : ℕ) [NeZero m] [NeZero n] : NeZero (lcm m n) :=
  ⟨lcm_ne_zero (NeZero.ne m) (NeZero.ne n)⟩

/-- If `q ≠ 0` and `N ≠ 0`, then `q` is coprime to `q ^ N - 1`. -/
theorem coprime_pow_sub_one {q N : ℕ} (hq : q ≠ 0) (hN : N ≠ 0) : q.Coprime (q ^ N - 1) :=
  .of_dvd_left (dvd_pow_self q hN) <|
    (coprime_self_sub_right (one_le_pow N q (Nat.pos_of_ne_zero hq))).2 (coprime_one_right _)

/-- If the products of two finite families of naturals are coprime and some entry of the first
family is zero, then the second family is constantly `1`: a zero entry makes the first product
`0`, and `Nat.Coprime 0 m` holds only for `m = 1`. -/
theorem Coprime.eq_one_of_exists_eq_zero {ι : Type*} [Fintype ι] {x y : ι → ℕ}
    (hc : Nat.Coprime (∏ i, x i) (∏ i, y i)) (hx : ∃ i, x i = 0) : y = 1 := by
  obtain ⟨i, hi⟩ := hx
  have hx0 : (∏ i, x i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hy1 : (∏ i, y i) = 1 := (Nat.coprime_zero_left _).mp (hx0 ▸ hc)
  exact funext fun j ↦ Nat.dvd_one.mp (hy1 ▸ Finset.dvd_prod_of_mem y (Finset.mem_univ j))

end Nat
