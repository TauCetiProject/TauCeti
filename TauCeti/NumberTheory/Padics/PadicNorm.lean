/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# The `p`-adic norm of a rational prime product

For a product of distinct primes with integer exponents, the norm at `p` reads off
only the exponent at `p`, even when the product has a denominator.
-/

public section

namespace padicNorm

/-- The `p`-adic norm of a finite product of prime powers is `p` raised to the negative
of its exponent in the product, and is `1` if `p` is not among the factors. -/
theorem prod_prime_zpow (p : Nat.Primes) (S : Finset Nat.Primes) (e : Nat.Primes → ℤ) :
    padicNorm (p : ℕ) (∏ q ∈ S, (q.val : ℚ) ^ e q) =
      if p ∈ S then (p.val : ℚ) ^ (-e p) else 1 := by
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  let v := IsAbsoluteValue.toAbsoluteValue (padicNorm (p : ℕ))
  have hv_apply (x : ℚ) : v x = padicNorm (p : ℕ) x :=
    IsAbsoluteValue.toAbsoluteValue_apply _ x
  calc
    _ = v (∏ q ∈ S, (q.val : ℚ) ^ e q) := (hv_apply _).symm
    _ = ∏ q ∈ S, v (q.val : ℚ) ^ e q := by simp only [map_prod, map_zpow₀]
    _ = _ := by
      have hoff (q : Nat.Primes) (hq : q ≠ p) : v (q.val : ℚ) ^ e q = 1 := by
        let : Fact (q : ℕ).Prime := ⟨q.property⟩
        suffices v (q.val : ℚ) = 1 by rw [this, one_zpow]
        rw [hv_apply]
        exact padicNorm_of_prime_of_ne (fun h ↦ hq ((Nat.Primes.coe_nat_inj p q).mp h).symm)
      by_cases hp : p ∈ S
      · rw [ite_eq_left hp, Finset.prod_eq_single_of_mem p hp (fun q _ hq ↦ hoff q hq)]
        rw [hv_apply, padicNorm_p_of_prime, inv_zpow, zpow_neg]
      · rw [ite_eq_right hp, Finset.prod_eq_one fun q hq ↦ hoff q (ne_of_mem_of_not_mem hq hp)]

end padicNorm
