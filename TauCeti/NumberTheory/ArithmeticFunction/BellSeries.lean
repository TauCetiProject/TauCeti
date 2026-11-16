/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.RingTheory.PowerSeries.WellKnown
import TauCeti.NumberTheory.Divisors

/-!
# Bell series of arithmetic functions

The Bell series of an arithmetic function `f : ArithmeticFunction R` at a prime `p` is the formal
power series `∑' k, f (p ^ k) X ^ k` in `PowerSeries R`. Because the divisors of `p ^ k` are
precisely the prime powers `p ^ i` (`0 ≤ i ≤ k`), taking Bell series at `p` is an `R`-algebra
homomorphism from Dirichlet convolution to formal power series multiplication, and is a left
inverse to Mathlib's `ArithmeticFunction.ofPowerSeries p`.

Two multiplicative arithmetic functions coincide if and only if they have the same Bell series at
every prime. This reduces coefficient-level identities between products of multiplicative
arithmetic functions (such as Euler-product factorizations) to finite formal power series
identities at each prime.

## Main definitions

* `ArithmeticFunction.bellSeries`: the Bell series algebra homomorphism
  `ArithmeticFunction R →ₐ[R] PowerSeries R` at a prime `p`.

## Main results

* `ArithmeticFunction.bellSeries_ofPowerSeries`: `bellSeries p hp (ofPowerSeries p F) = F`.
* `ArithmeticFunction.bellSeries_ofPowerSeries_pow`:
  `bellSeries p hp (ofPowerSeries (p ^ m) F) = F.subst (PowerSeries.X ^ m)`.
* `ArithmeticFunction.IsMultiplicative.eq_iff_forall_bellSeries_eq`: two multiplicative arithmetic
  functions are equal if and only if their Bell series agree at every prime.
* `ArithmeticFunction.bellSeries_mul_one_sub_C_mul_X`: if `f (p ^ k) = c ^ k` for all `k`, then
  `bellSeries p hp f * (1 - PowerSeries.C c * PowerSeries.X) = 1`.
* `ArithmeticFunction.bellSeries_ofPowerSeries_mk_one_mul_one_sub_X_pow`:
  `bellSeries p hp (ofPowerSeries (p ^ m) (PowerSeries.mk 1)) * (1 - PowerSeries.X ^ m) = 1`.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, §2.16.
-/

public section

namespace ArithmeticFunction

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The **Bell series** of an arithmetic function at a prime `p`, sending `f` to the formal power
series `∑ k, f (p ^ k) X ^ k`. This is an `R`-algebra homomorphism from Dirichlet convolution to
multiplication of formal power series. -/
noncomputable def bellSeries (p : ℕ) (hp : p.Prime) : ArithmeticFunction R →ₐ[R] PowerSeries R where
  toFun f := PowerSeries.mk fun k ↦ f (p ^ k)
  map_one' := PowerSeries.ext fun k ↦ by
    cases k with
    | zero => simp
    | succ k => simp [ArithmeticFunction.one_apply, hp.ne_one]
  map_mul' f g := PowerSeries.ext fun k ↦ by
    rw [PowerSeries.coeff_mk, ArithmeticFunction.mul_apply, PowerSeries.coeff_mul,
      Nat.divisorsAntidiagonal_prime_pow hp k, Finset.sum_map]
    simp
  map_zero' := PowerSeries.ext fun _ ↦ by simp
  map_add' _ _ := PowerSeries.ext fun _ ↦ by simp
  commutes' r := PowerSeries.ext fun k ↦ by
    cases k with
    | zero => simp [Algebra.algebraMap_eq_smul_one]
    | succ k =>
      simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.one_apply, hp.ne_one]

/-- The `k`-th coefficient of the Bell series of `f` at `p` is `f (p ^ k)`. -/
@[simp]
theorem coeff_bellSeries {p : ℕ} (hp : p.Prime) (f : ArithmeticFunction R) (k : ℕ) :
    PowerSeries.coeff k (bellSeries p hp f) = f (p ^ k) := by
  simp [bellSeries]

/-- The constant coefficient of the Bell series of `f` at any prime is `f 1`. -/
@[simp]
theorem constantCoeff_bellSeries {p : ℕ} (hp : p.Prime) (f : ArithmeticFunction R) :
    PowerSeries.constantCoeff (bellSeries p hp f) = f 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_bellSeries, pow_zero]

/-- Taking the Bell series at `p` is a left inverse to `ArithmeticFunction.ofPowerSeries p`. -/
@[simp]
theorem bellSeries_ofPowerSeries {p : ℕ} (hp : p.Prime) (F : PowerSeries R) :
    bellSeries p hp (ofPowerSeries p F) = F :=
  PowerSeries.ext fun k ↦ by rw [coeff_bellSeries, ofPowerSeries_apply_pow hp.one_lt]

/-- Two multiplicative arithmetic functions are equal if and only if their Bell series coincide at
every prime. -/
theorem IsMultiplicative.eq_iff_forall_bellSeries_eq {f g : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    f = g ↔ ∀ (p : ℕ) (hp : p.Prime), bellSeries p hp f = bellSeries p hp g := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg]
  simp only [PowerSeries.ext_iff, coeff_bellSeries]
  exact ⟨fun h p hp k ↦ h p k hp, fun h p k hp ↦ h p hp k⟩

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- The Bell series at `p` of `ofPowerSeries (p ^ m) F` is obtained by substituting `X ^ m` into
`F`. -/
theorem bellSeries_ofPowerSeries_pow {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (F : PowerSeries R) :
    bellSeries p hp (ofPowerSeries (p ^ m) F) = F.subst (PowerSeries.X ^ m) := by
  rw [ofPowerSeries_pow p hm, bellSeries_ofPowerSeries]

/-- If an arithmetic function is geometric on powers of `p` with ratio `c`, then its Bell series at
`p` is the formal reciprocal of `1 - c X`. -/
theorem bellSeries_mul_one_sub_C_mul_X {p : ℕ} (hp : p.Prime) {f : ArithmeticFunction R} {c : R}
    (hf : ∀ k : ℕ, f (p ^ k) = c ^ k) :
    bellSeries p hp f * (1 - PowerSeries.C c * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale c) (PowerSeries.mk_one_mul_one_sub_eq_one R)
  have hbell : bellSeries p hp f = PowerSeries.rescale c (PowerSeries.mk 1) :=
    PowerSeries.ext fun k ↦ by simp [hf]
  simpa [hbell, map_mul, map_sub, map_one, PowerSeries.rescale_X] using h

/-- The Bell series at `p` of the geometric local factor supported on powers of `p ^ m` (`m ≠ 0`)
is the formal reciprocal of `1 - X ^ m`. -/
theorem bellSeries_ofPowerSeries_mk_one_mul_one_sub_X_pow {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    bellSeries p hp (ofPowerSeries (p ^ m) (PowerSeries.mk 1 : PowerSeries R)) *
      (1 - PowerSeries.X ^ m) = 1 := by
  have hsub : PowerSeries.HasSubst (PowerSeries.X ^ m : PowerSeries R) :=
    PowerSeries.HasSubst.X_pow hm
  have h := congrArg (PowerSeries.substAlgHom hsub)
    (PowerSeries.mk_one_mul_one_sub_eq_one R)
  rw [bellSeries_ofPowerSeries_pow hp hm, ← PowerSeries.coe_substAlgHom hsub]
  simpa [map_mul, map_sub, map_one, PowerSeries.substAlgHom_X] using h

end CommRing

end ArithmeticFunction
