/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Root multisets of `1 + X + ⋯ + X ^ (n - 1)` and `X ^ n + 1`

In a commutative domain, a primitive `n`-th root of unity `ζ` determines the root multiset of
`1 + X + ⋯ + X ^ (n - 1)` via `(∑_{i < n} X ^ i) (X - 1) = X ^ n - 1`, and a primitive `(2n)`-th
root of unity `ζ` determines the root multiset of `X ^ n + 1 = X ^ n - (-1)` via `ζ ^ n = -1`.

## Main results

* `IsPrimitiveRoot.roots_geom_sum`: the roots of `∑ i ∈ Finset.range n, X ^ i` are `ζ ^ (e + 1)` for
  `e < n - 1`.
* `IsPrimitiveRoot.roots_X_pow_add_one`: the roots of `X ^ n + 1` are `ζ ^ (2 * k + 1)` for `k < n`.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The roots of `1 + X + ⋯ + X ^ (n - 1)` in a domain.** Given a primitive `n`-th root of unity
`ζ`, the root multiset of `∑ i ∈ Finset.range n, X ^ i` consists of `ζ ^ (e + 1)` for
`e = 0, …, n - 2`, each with multiplicity one. For `n ≤ 1` both sides are empty. -/
theorem roots_geom_sum {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    (∑ i ∈ Finset.range n, (X : R[X]) ^ i).roots =
      (Multiset.range (n - 1)).map fun e ↦ ζ ^ (e + 1) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  set p : R[X] := ∑ i ∈ Finset.range n, X ^ i
  have hp : p * (X - C 1) = X ^ n - C 1 := by rw [C_1, geom_sum_mul]
  have hroots : p.roots + {1} = (Multiset.range n).map fun k ↦ ζ ^ k * 1 := by
    rw [← roots_X_sub_C, ← roots_mul (hp ▸ X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1), hp,
      ← nthRoots, hζ.nthRoots_eq (one_pow n)]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [Multiset.range_add, show Multiset.range 1 = {0} from rfl, Multiset.map_add,
    Multiset.map_singleton, pow_zero, one_mul, Multiset.map_map, add_comm] at hroots
  rw [add_left_cancel hroots, Nat.add_sub_cancel_left]
  exact Multiset.map_congr rfl fun e _ ↦ by simp [add_comm]

/-- **The roots of `X ^ n + 1` in a domain.** Given a primitive `(2 * n)`-th root of unity `ζ`, the
root multiset of `X ^ n + 1` consists of the odd powers `ζ ^ (2 * k + 1)` for `k = 0, …, n - 1`,
each with multiplicity one. For `n = 0` the polynomial is constant and both sides are empty. -/
theorem roots_X_pow_add_one {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (X ^ n + 1 : R[X]).roots = (Multiset.range n).map fun k ↦ ζ ^ (2 * k + 1) := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [pow_zero, ← C_1, ← map_add, roots_C]; simp
  have hζn : ζ ^ n = -1 :=
    (sq_eq_one_iff.mp (by rw [← pow_mul, mul_comm, hζ.pow_eq_one])).resolve_left fun h1 ↦ by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hζ.dvd_of_pow_eq_one n h1); omega
  rw [show (X ^ n + 1 : R[X]) = X ^ n - C (-1) by simp [sub_neg_eq_add], ← nthRoots,
    (hζ.pow (by omega) rfl : IsPrimitiveRoot (ζ ^ 2) n).nthRoots_eq hζn]
  exact Multiset.map_congr rfl fun k _ ↦ by rw [← pow_mul, ← pow_succ]

end IsPrimitiveRoot

end
