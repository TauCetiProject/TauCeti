/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Defs
import Mathlib.RingTheory.Ideal.Basic

/-!
# Nilpotent action of sums and differences of commuting scalars on a vector

Commuting elements of a semiring annihilating a vector of a module in degrees `r₁` and `r₀` have
sum annihilating it in every degree `k` with `r₁ + r₀ ≤ k + 1`; over a ring, so does their
difference. These are the pointwise forms of Mathlib's
`Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero`.

## Main results

* `Commute.add_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero`,
  `Commute.sub_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero`: nilpotent action of `x + y`
  (`x`, `y` in a semiring) and of `x - y` (`x`, `y` in a ring) at each degree `k` with
  `r₁ + r₀ ≤ k + 1` when commuting `x`, `y` kill a vector `u` of a module at degrees `r₁`, `r₀`.
-/

public section

namespace Commute

variable {A M : Type*} [AddCommMonoid M] {x y : A} {r₁ r₀ k : ℕ} {u : M}

/-- If commuting elements `x` and `y` of a semiring satisfy `x ^ r₁ • u = 0` and `y ^ r₀ • u = 0`,
then `(x + y) ^ k • u = 0` whenever `r₁ + r₀ ≤ k + 1`. This is the pointwise form of
`Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero`. -/
theorem add_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero [Semiring A] [Module A M]
    (hxy : Commute x y) (hx : x ^ r₁ • u = 0) (hy : y ^ r₀ • u = 0) (hk : r₁ + r₀ ≤ k + 1) :
    (x + y) ^ k • u = 0 := by
  -- The scalars killing `u` form the left ideal `ker (a ↦ a • u)`, i.e. `Ideal.torsionOf A M u`.
  have hmem (a : A) : a ∈ (LinearMap.toSpanSingleton A M u).ker ↔ a • u = 0 := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  exact (hmem _).1 <|
    Ideal.add_pow_mem_of_pow_mem_of_le_of_commute _ ((hmem _).2 hx) ((hmem _).2 hy) hk hxy

/-- If commuting elements `x` and `y` of a ring satisfy `x ^ r₁ • u = 0` and `y ^ r₀ • u = 0`,
then `(x - y) ^ k • u = 0` whenever `r₁ + r₀ ≤ k + 1`. -/
theorem sub_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero [Ring A] [Module A M]
    (hxy : Commute x y) (hx : x ^ r₁ • u = 0) (hy : y ^ r₀ • u = 0) (hk : r₁ + r₀ ≤ k + 1) :
    (x - y) ^ k • u = 0 := by
  rw [sub_eq_add_neg]
  refine hxy.neg_right.add_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero hx ?_ hk
  rw [neg_pow, mul_smul, hy, smul_zero]

end Commute
