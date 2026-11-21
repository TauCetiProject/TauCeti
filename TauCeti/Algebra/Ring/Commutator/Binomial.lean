/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import TauCeti.Algebra.Ring.Commutator

/-!
# Moving powers across powers under an additive shift

If `a * x = x * (a + c)` and `c` commutes with `x`, then moving `a ^ m` across `x ^ n` accumulates
`n` copies of the shift: `a ^ m * x ^ n = x ^ n * (a + n • c) ^ m`. When the shift is a central
scalar `h` of an algebra, the binomial theorem expands the right-hand side in the ordered products
`x ^ n * a ^ k`.

## Main results

* `TauCeti.Associative.pow_mul_pow_eq_pow_mul_add_nsmul_pow`: moving a power across a power.
* `TauCeti.Associative.pow_mul_pow_eq_sum_smul`: the binomial expansion of `x ^ b * y ^ c` in
  ordered products when `x * y = y * (x + h)` for a scalar `h`.
-/

public section

open Finset

namespace TauCeti.Associative

/-- **Moving a power across a power accumulates the additive shift.** If `a * x = x * (a + c)`
and `c` commutes with `x`, then `a ^ m * x ^ n = x ^ n * (a + n • c) ^ m`. -/
theorem pow_mul_pow_eq_pow_mul_add_nsmul_pow {A : Type*} [Semiring A] {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (m n : ℕ) :
    a ^ m * x ^ n = x ^ n * (a + n • c) ^ m := by
  have hsc : SemiconjBy (x ^ n) (a + n • c) a := (mul_pow_eq_pow_mul_add_nsmul h hc n).symm
  exact (hsc.pow_right m).eq.symm

/-- **Ordered expansion of `x ^ b y ^ c`.** If `x y = y (x + h)` in an `S`-algebra, then
`x ^ b y ^ c` is the combination `∑ n ∈ [0, b], (b choose n) c ^ n h ^ n y ^ c x ^ (b - n)` of
ordered products. -/
theorem pow_mul_pow_eq_sum_smul {S A : Type*} [CommSemiring S] [Semiring A] [Algebra S A]
    {x y : A} {h : S} (hxy : x * y = y * (x + algebraMap S A h)) (b c : ℕ) :
    x ^ b * y ^ c =
      ∑ n ∈ range (b + 1), (b.choose n * c ^ n * h ^ n : S) • (y ^ c * x ^ (b - n)) := by
  -- Move `x ^ b` across `y ^ c`, then expand `(c h + x) ^ b`: its summands commute, as `h` is
  -- central.
  rw [pow_mul_pow_eq_pow_mul_add_nsmul_pow hxy (Algebra.commute_algebraMap_left h y),
    ← map_nsmul, add_comm, (Algebra.commute_algebraMap_left _ x).add_pow, mul_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  simp only [← map_pow, mul_assoc, ← Algebra.smul_def, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul S,
    mul_smul_comm, smul_smul, smul_pow]
  congr 1
  ring

end TauCeti.Associative
