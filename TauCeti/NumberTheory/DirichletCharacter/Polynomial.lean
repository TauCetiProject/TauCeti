/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.Convolution
public import TauCeti.GroupTheory.FiniteAbelian.EulerFactor
import Mathlib.RingTheory.PowerSeries.WellKnown
import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction

/-!
# Products of linear Euler factors over Dirichlet characters

Let `n = p ^ k * m` with `p` prime and `¬ p ∣ m`, so `m` is the prime-to-`p` part of `n`. A
Dirichlet character `χ` modulo `n` factors through `m` if and only if `p` does not divide its
conductor `χ.conductor`. Consequently:

* When `p ∣ χ.conductor`, `p` is a nonunit modulo `χ.conductor` and `χ.primitiveCharacter p = 0`.
* When `¬ p ∣ χ.conductor`, `χ` is the lift from level `m` of a unique character `ψ` modulo `m`,
  and `χ.primitiveCharacter p = ψ p`.

Together with `CommGroup.prod_one_sub_C_monoidHom_mul_X` on the unit group `(ZMod m)ˣ`, this gives
the polynomial Euler-factor identity

`∏ χ : DirichletCharacter R n, (1 - C (χ.primitiveCharacter p) * X) =
  (1 - X ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m))`

over any integral domain `R` with enough roots of unity for `Monoid.exponent (ZMod m)ˣ`, including
at ramified primes `p ∣ n` where `k ≥ 1`. Inverting both sides in `R⟦X⟧` identifies the prime-power
Dirichlet convolution coefficients of `∏ χ, toArithmeticFunction (χ.primitiveCharacter ·)` at
`p ^ r`, providing the character side of the Dedekind zeta factorization for cyclotomic fields.

We also record the prime-power conductor dichotomy `p ∣ χ.conductor ↔ χ ≠ 1` for characters modulo
`p ^ k`, and the consequence that every nontrivial character of prime level is primitive.

## Main results

* `DirichletCharacter.factorsThrough_iff_not_dvd_conductor`: for `n = p ^ k * m` with `p` prime and
  `¬ p ∣ m`, `χ.FactorsThrough m ↔ ¬ p ∣ χ.conductor`.
* `DirichletCharacter.dvd_conductor_iff_ne_one_of_prime_pow`: for `χ` modulo `p ^ k`,
  `p ∣ χ.conductor ↔ χ ≠ 1`.
* `DirichletCharacter.isPrimitive_of_ne_one_of_prime`: every nontrivial character modulo a prime `p`
  is primitive.
* `DirichletCharacter.prod_primitiveCharacter_prime_eq`: if `f 0 = 1`, the product of
  `f (χ.primitiveCharacter p)` over `χ` modulo `n = p ^ k * m` equals the product of `f (ψ p)` over
  `ψ` modulo `m`.
* `DirichletCharacter.prod_one_sub_C_mul_X`, `DirichletCharacter.prod_one_sub_mul`: product of
  `1 - C (ψ a) * X` (and `1 - ψ a * z`) over `ψ : DirichletCharacter R m` at a unit `a : ZMod m`.
* `DirichletCharacter.prod_one_sub_C_primitiveCharacter_prime_mul_X`,
  `DirichletCharacter.prod_one_sub_primitiveCharacter_prime_mul`: product of
  `1 - C (χ.primitiveCharacter p) * X` (and `1 - χ.primitiveCharacter p * z`) over all `χ` modulo
  `n = p ^ k * m`.
* `DirichletCharacter.prod_toArithmeticFunction_primitiveCharacter_apply_prime_pow`: prime-power
  evaluation of the Dirichlet convolution `∏ χ, toArithmeticFunction (χ.primitiveCharacter ·)` via
  `(ArithmeticFunction.ofPowerSeries (p ^ f) (PowerSeries.mk 1)) ^ g`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
-/

public section

open Polynomial

namespace DirichletCharacter

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R]

/-- The conductor of a Dirichlet character of nonzero level is nonzero. -/
instance instNeZeroConductor {n : ℕ} [NeZero n] (χ : DirichletCharacter R n) :
    NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

/-- **Factoring through the prime-to-`p` part of the level.** If `n = p ^ k * m` with `p` prime and
`¬ p ∣ m`, a Dirichlet character `χ` modulo `n` factors through `m` if and only if `p` does not
divide its conductor. -/
theorem factorsThrough_iff_not_dvd_conductor {n p k m : ℕ} (hp : p.Prime) (hn : n = p ^ k * m)
    (hm : ¬ p ∣ m) (χ : DirichletCharacter R n) :
    χ.FactorsThrough m ↔ ¬ p ∣ χ.conductor := by
  have hm0 : m ≠ 0 := fun h ↦ hm (h ▸ dvd_zero p)
  have : NeZero n := ⟨hn ▸ mul_ne_zero (pow_ne_zero k hp.ne_zero) hm0⟩
  have hmn : m ∣ n := ⟨p ^ k, by rw [hn, mul_comm]⟩
  rw [← mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd χ hmn]
  exact ⟨fun hdvd hpc ↦ hm (hpc.trans hdvd), fun hnpc ↦
    ((hp.coprime_iff_not_dvd.mpr hnpc).pow_left k).symm.dvd_of_dvd_mul_left
      (hn ▸ χ.conductor_dvd_level)⟩

/-- **Prime-power conductor dichotomy.** For a prime `p` and a character `χ` modulo `p ^ k`, the
prime `p` divides `χ.conductor` if and only if `χ` is nonprincipal. -/
theorem dvd_conductor_iff_ne_one_of_prime_pow {p k : ℕ} (hp : p.Prime)
    (χ : DirichletCharacter R (p ^ k)) :
    p ∣ χ.conductor ↔ χ ≠ 1 := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp χ.conductor_dvd_level
  rw [Ne, eq_one_iff_conductor_eq_one, hj]
  rcases eq_or_ne j 0 with rfl | hj0
  · simp [hp.not_dvd_one]
  · exact ⟨fun _ ↦ (one_lt_pow₀ hp.one_lt hj0).ne', fun _ ↦ dvd_pow_self p hj0⟩

/-- Every nonprincipal Dirichlet character of prime level is primitive. -/
theorem isPrimitive_of_ne_one_of_prime {p : ℕ} (hp : p.Prime) {χ : DirichletCharacter R p}
    (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [isPrimitive_def]
  rcases hp.eq_one_or_self_of_dvd _ χ.conductor_dvd_level with h1 | hp'
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h1) hχ
  · exact hp'

end CommMonoidWithZero

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Reduction of a primitive-character product at `p` to the prime-to-`p` level.** If
`n = p ^ k * m` with `p` prime and `¬ p ∣ m`, and `f : R → M` sends `0` to `1`, then the product
of `f (χ.primitiveCharacter p)` over all characters `χ` modulo `n` equals the product of `f (ψ p)`
over all characters `ψ` modulo `m`: characters whose conductor is divisible by `p` contribute
`f 0 = 1`, while the remaining characters biject with `DirichletCharacter R m` via
`factorsThroughEquiv`. -/
theorem prod_primitiveCharacter_prime_eq {M : Type*} [CommMonoid M] {n p k m : ℕ}
    (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) {f : R → M} (hf : f 0 = 1) :
    ∏ χ : DirichletCharacter R n, f (χ.primitiveCharacter p) =
      ∏ ψ : DirichletCharacter R m, f (ψ p) := by
  classical
  have hm0 : m ≠ 0 := fun h ↦ hm (h ▸ dvd_zero p)
  have : NeZero m := ⟨hm0⟩
  have : NeZero n := ⟨hn ▸ mul_ne_zero (pow_ne_zero k hp.ne_zero) hm0⟩
  have hmn : m ∣ n := ⟨p ^ k, by rw [hn, mul_comm]⟩
  -- Split off the characters that do not factor through `m`; at those, `p ∣ χ.conductor`.
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun χ : DirichletCharacter R n ↦ χ.FactorsThrough m)]
  have hram : (∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter R n ↦ ¬ χ.FactorsThrough m),
      f (χ.primitiveCharacter p)) = 1 := by
    refine Finset.prod_eq_one fun χ hχ ↦ ?_
    have hpc : p ∣ χ.conductor :=
      by_contra fun hnpc ↦ (Finset.mem_filter.mp hχ).2
        ((factorsThrough_iff_not_dvd_conductor hp hn hm χ).mpr hnpc)
    have hnu : ¬ IsUnit (p : ZMod χ.conductor) := fun hu ↦
      (ZMod.isUnit_prime_iff_not_dvd hp).mp hu hpc
    rw [χ.primitiveCharacter.map_nonunit hnu, hf]
  rw [hram, mul_one,
    Finset.prod_subtype (Finset.univ.filter _) (p := (·.FactorsThrough m)) (fun _ ↦ by simp),
    ← (factorsThroughEquiv hmn).symm.prod_comp]
  refine Finset.prod_congr rfl fun ψ _ ↦ congrArg f ?_
  have hcop : IsCoprime (p : ℤ) m := Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hm)
  rw [coe_factorsThroughEquiv_symm_apply]
  simpa only [Int.cast_natCast] using
    (primitiveCharacter_changeLevel_apply hmn ψ p).trans
      (ψ.primitiveCharacter_apply_of_isCoprime hcop)

/-- **Product of linear Euler factors over `DirichletCharacter R m` at a unit.** For `m ≠ 0` and a
unit `a : ZMod m`, the product of `1 - C (ψ a) * X` over all characters `ψ` modulo `m` equals
`(1 - X ^ orderOf a) ^ (m.totient / orderOf a)` in `R[X]`. -/
theorem prod_one_sub_C_mul_X {m : ℕ} [NeZero m]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)] {a : ZMod m} (ha : IsUnit a) :
    ∏ ψ : DirichletCharacter R m, (1 - C (ψ a) * X) =
      (1 - X ^ orderOf a) ^ (m.totient / orderOf a) := by
  have heval (ψ : DirichletCharacter R m) :
      ψ a = ((MulChar.equivToUnitHom ψ ha.unit : Rˣ) : R) :=
    (congrArg ψ ha.unit_spec.symm).trans (MulChar.coe_equivToUnitHom ψ ha.unit).symm
  simp_rw [heval]
  rw [MulChar.equivToUnitHom.prod_comp
    (fun φ : (ZMod m)ˣ →* Rˣ ↦ (1 : R[X]) - C ((φ ha.unit : Rˣ) : R) * X),
    CommGroup.prod_one_sub_C_monoidHom_mul_X ha.unit, ← orderOf_units, ha.unit_spec,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- **Evaluated product of `1 - ψ a * z` over `DirichletCharacter R m` at a unit.** -/
theorem prod_one_sub_mul {m : ℕ} [NeZero m]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)] {a : ZMod m} (ha : IsUnit a) (z : R) :
    ∏ ψ : DirichletCharacter R m, (1 - ψ a * z) =
      (1 - z ^ orderOf a) ^ (m.totient / orderOf a) := by
  have h := congrArg (Polynomial.eval z) (prod_one_sub_C_mul_X (R := R) ha)
  simpa [eval_prod] using h

/-- **Polynomial Euler-factor product over primitive characters at a prime.** If `n = p ^ k * m`
with `p` prime and `¬ p ∣ m`, the product of `1 - C (χ.primitiveCharacter p) * X` over all
characters `χ : DirichletCharacter R n` equals
`(1 - X ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m))`. -/
theorem prod_one_sub_C_primitiveCharacter_prime_mul_X {n p k m : ℕ} (hp : p.Prime)
    (hn : n = p ^ k * m) (hm : ¬ p ∣ m)
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)] :
    ∏ χ : DirichletCharacter R n, (1 - C (χ.primitiveCharacter p) * X) =
      (1 - X ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m)) := by
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  rw [prod_primitiveCharacter_prime_eq hp hn hm (f := fun r : R ↦ (1 : R[X]) - C r * X) (by simp)]
  exact prod_one_sub_C_mul_X ((ZMod.isUnit_prime_iff_not_dvd hp).mpr hm)

/-- **Scalar Euler-factor product over primitive characters at a prime.** If `n = p ^ k * m` with
`p` prime and `¬ p ∣ m`, the product of `1 - χ.primitiveCharacter p * z` over all characters
`χ : DirichletCharacter R n` equals
`(1 - z ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m))`. -/
theorem prod_one_sub_primitiveCharacter_prime_mul {n p k m : ℕ} (hp : p.Prime)
    (hn : n = p ^ k * m) (hm : ¬ p ∣ m)
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)] (z : R) :
    ∏ χ : DirichletCharacter R n, (1 - χ.primitiveCharacter p * z) =
      (1 - z ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m)) := by
  have h := congrArg (Polynomial.eval z)
    (prod_one_sub_C_primitiveCharacter_prime_mul_X (R := R) hp hn hm)
  simpa [eval_prod] using h

/-- Reciprocal power-series identity at a prime `p`: the product over `χ` modulo `n = p ^ k * m` of
`∑_{i ≥ 0} (χ.primitiveCharacter p) ^ i X ^ i` equals `((1 + X ^ f + X ^ (2 f) + ⋯)) ^ g` in
`R⟦X⟧`, where `f = orderOf (p : ZMod m)` and `g = m.totient / f`. -/
private theorem prod_mk_primitiveCharacter_prime_pow_eq {n p k m : ℕ} (hp : p.Prime)
    (hn : n = p ^ k * m) (hm : ¬ p ∣ m)
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)] :
    (∏ χ : DirichletCharacter R n, PowerSeries.mk fun i ↦ χ.primitiveCharacter p ^ i) =
      (PowerSeries.subst (PowerSeries.X ^ orderOf (p : ZMod m) : PowerSeries R)
        (PowerSeries.mk 1 : PowerSeries R)) ^ (m.totient / orderOf (p : ZMod m)) := by
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  set f := orderOf (p : ZMod m)
  set g := m.totient / f
  have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_prime_iff_not_dvd hp).mpr hm
  have hf0 : f ≠ 0 := by
    rw [show f = orderOf (p : ZMod m) from rfl, ← hu.unit_spec, orderOf_units]
    exact (isOfFinOrder_of_finite hu.unit).orderOf_pos.ne'
  set U : PowerSeries R :=
    PowerSeries.subst (PowerSeries.X ^ f : PowerSeries R) (PowerSeries.mk 1 : PowerSeries R)
  set Z : PowerSeries R := (1 - PowerSeries.X ^ f) ^ g
  have hgeom (a : R) :
      (PowerSeries.mk fun i ↦ a ^ i) * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
    simpa [PowerSeries.rescale_mk] using
      congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one R)
  have hVZ : (∏ χ : DirichletCharacter R n, PowerSeries.mk fun i ↦ χ.primitiveCharacter p ^ i) *
      Z = 1 := by
    have hZ : Z = ∏ χ : DirichletCharacter R n,
        (1 - PowerSeries.C (χ.primitiveCharacter p) * PowerSeries.X) := by
      simpa [Z, map_prod] using (congrArg (Polynomial.coeToPowerSeries.ringHom (R := R))
        (prod_one_sub_C_primitiveCharacter_prime_mul_X (R := R) hp hn hm)).symm
    rw [hZ, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun χ _ ↦ hgeom _
  have hUZ : U ^ g * Z = 1 := by
    have hsub := congrArg
      (PowerSeries.substAlgHom (R := R) (PowerSeries.HasSubst.X_pow (R := R) hf0))
      (PowerSeries.mk_one_mul_one_sub_eq_one R)
    rw [map_mul, map_sub, map_one, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom] at hsub
    rw [← mul_pow, show U * (1 - PowerSeries.X ^ f) = 1 from hsub, one_pow]
  calc (∏ χ : DirichletCharacter R n, PowerSeries.mk fun i ↦ χ.primitiveCharacter p ^ i)
      = (∏ χ : DirichletCharacter R n, PowerSeries.mk fun i ↦ χ.primitiveCharacter p ^ i) *
          (U ^ g * Z) := by rw [hUZ, mul_one]
    _ = (((∏ χ : DirichletCharacter R n, PowerSeries.mk fun i ↦ χ.primitiveCharacter p ^ i) * Z) *
          U ^ g) := by ring
    _ = U ^ g := by rw [hVZ, one_mul]

/-- **Prime-power coefficients of the primitive-character convolution product.** If `n = p ^ k * m`
with `p` prime and `¬ p ∣ m`, the `p ^ r`-th Dirichlet-convolution coefficient of
`∏ χ : DirichletCharacter R n, toArithmeticFunction (χ.primitiveCharacter ·)` coincides with that of
`(ArithmeticFunction.ofPowerSeries (p ^ f) (PowerSeries.mk 1)) ^ g`, the `g`-fold convolution of
the geometric Euler factor of norm `p ^ f`, where `f = orderOf (p : ZMod m)` and
`g = m.totient / f`. -/
theorem prod_toArithmeticFunction_primitiveCharacter_apply_prime_pow {n p k m : ℕ} (hp : p.Prime)
    (hn : n = p ^ k * m) (hm : ¬ p ∣ m)
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)] (r : ℕ) :
    (∏ χ : DirichletCharacter R n, toArithmeticFunction (χ.primitiveCharacter ·)) (p ^ r) =
      ((ArithmeticFunction.ofPowerSeries (p ^ orderOf (p : ZMod m))
          (PowerSeries.mk 1 : PowerSeries R)) ^
        (m.totient / orderOf (p : ZMod m))) (p ^ r) := by
  classical
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_prime_iff_not_dvd hp).mpr hm
  have hf0 : orderOf (p : ZMod m) ≠ 0 := by
    rw [← hu.unit_spec, orderOf_units]
    exact (isOfFinOrder_of_finite hu.unit).orderOf_pos.ne'
  have hcongr (t : Finset (DirichletCharacter R n)) (j : ℕ) :
      (∏ χ ∈ t, toArithmeticFunction (χ.primitiveCharacter ·)) (p ^ j) =
        (∏ χ ∈ t, ArithmeticFunction.ofPowerSeries p
          (PowerSeries.mk fun i ↦ χ.primitiveCharacter p ^ i)) (p ^ j) := by
    induction t using Finset.induction_on generalizing j with
    | empty => simp
    | insert χ t hχ ih =>
      rw [Finset.prod_insert hχ, Finset.prod_insert hχ, ArithmeticFunction.mul_apply,
        ArithmeticFunction.mul_apply]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      obtain ⟨i₁, -, hi₁⟩ := (Nat.dvd_prime_pow hp).mp
        (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hd))
      obtain ⟨i₂, -, hi₂⟩ := (Nat.dvd_prime_pow hp).mp
        (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hd))
      rw [hi₁, hi₂, toArithmeticFunction_apply_pow _ hp.ne_zero,
        ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt, PowerSeries.coeff_mk, ih]
  rw [hcongr Finset.univ r, ← map_prod (ArithmeticFunction.ofPowerSeries p),
    prod_mk_primitiveCharacter_prime_pow_eq hp hn hm, ArithmeticFunction.ofPowerSeries_pow p hf0,
    ← map_pow]

end IsDomain

end DirichletCharacter
