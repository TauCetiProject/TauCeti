/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# The element `ζ - 1` up to units

Let `p` be a prime and `ζ` a primitive `p`-th root of unity in a domain `A`. Evaluating the
cyclotomic polynomial `Φ_p = ∏ (X - η)`, the product over the primitive `p`-th roots `η`, at `1`
gives `p = ∏ (1 - η)`, and each `1 - η` is associated to `ζ - 1`. Hence `p` is associated to
`(ζ - 1) ^ (p - 1)`. In particular every valuation of `A` takes the value `v(ζ - 1) ^ (p - 1)`
at `p`, which is how the valuation normalised by `v(p) = 1` is read off from one normalised by
`v(ζ - 1) = 1`.

Mathlib proves this statement for the ring of integers of a `p`-th cyclotomic field
(`IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime`); the proof here is the same, in an
arbitrary domain.

Away from the order of the root of unity the picture is the opposite: if `ζ ≠ 1` satisfies
`ζ ^ n = 1` and `n` is a unit of `A`, then `ζ - 1` divides `n` (Mathlib's
`sub_one_dvd_natCast_of_pow_eq_one`) and so is itself a unit. For a character `χ` of order prime to
`p` with values in a `p`-adic integer ring, this makes `1 - χ(φ)⁻¹` a unit whenever `χ(φ) ≠ 1`.
Invertibility of `n` is needed: `1 - (-1) = 2` is not a unit of `ℤ_[2]`.

## Main results

* `IsPrimitiveRoot.associated_sub_one_pow_prime`: `(ζ - 1) ^ (p - 1)` is associated to `p`.
* `IsPrimitiveRoot.valuation_natCast_eq_valuation_sub_one_pow`: a valuation `v ≤ 1` on `A`
  satisfies `v(p) = v(ζ - 1) ^ (p - 1)`.
* `TauCeti.isUnit_sub_one_of_pow_eq_one`, `TauCeti.isUnit_one_sub_of_pow_eq_one`: `ζ - 1` and
  `1 - ζ` are units for a root of unity `ζ ≠ 1` of invertible order.
-/

public section

open Polynomial in
/-- If `ζ` is a primitive `p`-th root of unity in a domain `A` and `p` is prime, then
`(ζ - 1) ^ (p - 1)` is associated to `p`. -/
theorem IsPrimitiveRoot.associated_sub_one_pow_prime {A : Type*} [CommRing A] [IsDomain A]
    {p : ℕ} [hp : Fact p.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : A) := by
  rw [← eval_one_cyclotomic_prime (R := A) (p := p), cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη ↦ ?_
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨i, -, hi, rfl⟩ := hζ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

/-- If `ζ` is a primitive `p`-th root of unity in a domain `A` and `p` is prime, then every
valuation `v` of `A` bounded by `1` satisfies `v(p) = v(ζ - 1) ^ (p - 1)`. -/
theorem IsPrimitiveRoot.valuation_natCast_eq_valuation_sub_one_pow {A : Type*} [CommRing A]
    [IsDomain A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {p : ℕ} [Fact p.Prime] {ζ : A}
    (hζ : IsPrimitiveRoot ζ p) (v : Valuation A Γ₀) (hv : ∀ a, v a ≤ 1) :
    v (p : A) = v (ζ - 1) ^ (p - 1) := by
  obtain ⟨u, hu⟩ := hζ.associated_sub_one_pow_prime
  have hu1 : v (u : A) = 1 := by
    refine le_antisymm (hv _) ?_
    calc (1 : Γ₀) = v (u : A) * v (u⁻¹ : Aˣ) := by rw [← map_mul, Units.mul_inv, map_one]
      _ ≤ v (u : A) := mul_le_of_le_one_right' (hv _)
  rw [← hu, map_mul, hu1, mul_one, map_pow]

namespace TauCeti

/-- **`ζ - 1` is a unit for a root of unity `ζ ≠ 1` of invertible order**: in a domain `A`, if
`ζ ^ n = 1`, `ζ ≠ 1` and `n` is a unit of `A`, then `ζ - 1` is a unit, since it divides `n`. -/
theorem isUnit_sub_one_of_pow_eq_one {A : Type*} [CommRing A] [IsDomain A] {ζ : A} {n : ℕ}
    (hζ : ζ ^ n = 1) (hζ1 : ζ ≠ 1) (hn : IsUnit (n : A)) : IsUnit (ζ - 1) :=
  isUnit_of_dvd_unit (sub_one_dvd_natCast_of_pow_eq_one hζ hζ1) hn

/-- **`1 - ζ` is a unit for a root of unity `ζ ≠ 1` of invertible order**: in a domain `A`, if
`ζ ^ n = 1`, `ζ ≠ 1` and `n` is a unit of `A`, then `1 - ζ` is a unit. -/
theorem isUnit_one_sub_of_pow_eq_one {A : Type*} [CommRing A] [IsDomain A] {ζ : A} {n : ℕ}
    (hζ : ζ ^ n = 1) (hζ1 : ζ ≠ 1) (hn : IsUnit (n : A)) : IsUnit (1 - ζ) := by
  simpa using (isUnit_sub_one_of_pow_eq_one hζ hζ1 hn).neg

end TauCeti
