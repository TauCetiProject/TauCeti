/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.LinearCombination

/-!
# Primitive fourth and sixth roots of unity

In a field of characteristic zero the primitive fourth and sixth roots of unity are the roots of
the quadratic cyclotomic polynomials `Φ₄ = X² + 1` and `Φ₆ = X² - X + 1`. So a square root of
`-1` is a primitive fourth root of unity, and for a square root `θ` of `-3` the element
`(1 + θ)/2` is a primitive sixth root of unity. These are the exceptional roots of unity of the
quadratic fields `ℚ(√-1)` and `ℚ(√-3)`.

## Main results

* `TauCeti.isPrimitiveRoot_four_of_sq_eq_neg_one`: a square root of `-1` is a primitive fourth
  root of unity.
* `TauCeti.isPrimitiveRoot_six_iff`: `μ` is a primitive sixth root of unity if and only if
  `μ² - μ + 1 = 0`.
* `TauCeti.isPrimitiveRoot_one_add_div_two_of_sq_eq_neg_three`: for `θ² = -3`, `(1 + θ)/2` is a
  primitive sixth root of unity.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F]

/-- **The exceptional fourth root of unity.** In a field of characteristic zero, a square root of
`-1` is a primitive fourth root of unity: it is a root of `Φ₄ = X² + 1`. -/
theorem isPrimitiveRoot_four_of_sq_eq_neg_one {θ : F} (h : θ ^ 2 = -1) : IsPrimitiveRoot θ 4 := by
  -- Mathlib evaluates `Φ_{p^(k+1)}` as a geometric sum; `Φ₄` is the case `p = 2`, `k = 1`, where
  -- the sum is `1 + X²`.
  have hfour : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
  rw [← isRoot_cyclotomic_iff_charZero (by norm_num), hfour,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ, h]

/-- In a field of characteristic zero, the primitive sixth roots of unity are the roots of
`Φ₆ = X² - X + 1`. -/
theorem isPrimitiveRoot_six_iff {μ : F} : IsPrimitiveRoot μ 6 ↔ μ ^ 2 - μ + 1 = 0 := by
  rw [← isRoot_cyclotomic_iff_charZero (by norm_num), cyclotomic_six]
  simp only [IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_one]

/-- **The exceptional sixth root of unity.** In a field of characteristic zero, if `θ² = -3`, then
`(1 + θ)/2` is a primitive sixth root of unity: it is a root of `Φ₆ = X² - X + 1`. -/
theorem isPrimitiveRoot_one_add_div_two_of_sq_eq_neg_three {θ : F} (h : θ ^ 2 = -3) :
    IsPrimitiveRoot ((1 + θ) / 2) 6 :=
  isPrimitiveRoot_six_iff.2 (by linear_combination h / 4)

end TauCeti
