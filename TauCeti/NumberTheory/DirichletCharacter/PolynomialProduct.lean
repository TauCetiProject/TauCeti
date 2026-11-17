/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import TauCeti.GroupTheory.FiniteAbelian.PolynomialProduct
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.RingTheory.PowerSeries.Geometric
import TauCeti.RingTheory.PowerSeries.ProdOneSubXPow

/-!
# Products of Euler-type linear factors over Dirichlet characters

For a positive integer `m`, an integral domain `R` with enough roots of unity for `(ZMod m)ˣ`, and
an integer `a` coprime to `m`, transporting `CommGroup.prod_one_sub_C_monoidHom_mul_X` along
`MulChar.mulEquivToUnitHom` collapses the polynomial product over all Dirichlet characters modulo
`m` to
`∏ χ : DirichletCharacter R m, (1 - C (χ a) * X) = (1 - X ^ f) ^ (φ(m) / f)`,
where `f = orderOf (a : ZMod m)`.

At a prime `p` and any positive level `n = p ^ k * m` with `p ∤ m`, evaluating the primitive
characters `χ.primitiveCharacter` at `p` yields the same formula: characters whose conductor is
divisible by `p` vanish at `p` and contribute factor `1`, while those with conductor coprime to `p`
factor uniquely through `m` via `DirichletCharacter.factorsThroughEquiv`, where their primitive
character agrees with the lowered character at `p`. Inverting in `PowerSeries R` identifies the
product of the geometric series `∑ (χ.primitiveCharacter p) ^ j X ^ j` with the `(φ(m) / f)`-th
power of `(mk 1).subst (X ^ f)`.

## Main results

* `DirichletCharacter.apply_prime_eq_zero_of_dvd`: a Dirichlet character modulo `m` vanishes at any
  prime `p ∣ m` (including `m = 0`).
* `DirichletCharacter.ite_dvd_one_sub_mul`: `if p ∣ m then 1 else 1 - χ p * z` equals
  `1 - χ p * z` for any prime `p`.
* `DirichletCharacter.factorsThrough_of_eq_pow_mul_iff`: for `n = p ^ k * m` with `p` prime and
  `p ∤ m`, a character modulo `n` factors through `m` iff `p ∤ χ.conductor`.
* `DirichletCharacter.prod_one_sub_C_mul_X`: polynomial product over `DirichletCharacter R m` at
  `a` coprime to `m`.
* `DirichletCharacter.prod_one_sub_C_primitiveCharacter_mul_X`: polynomial product of
  `1 - C (χ.primitiveCharacter p) * X` over `DirichletCharacter R n` for `n = p ^ k * m`
  (`p ∤ m`).
* `DirichletCharacter.prod_one_sub_map_primitiveCharacter_mul`: image under any ring homomorphism
  `f : R →+* S` evaluated at `z : S`.
* `DirichletCharacter.prod_one_sub_primitiveCharacter_mul`: scalar specialization at `z : R`.
* `DirichletCharacter.prod_one_sub_primitiveCharacter_mul_prime_pow`: prime-power collapse
  `∏ χ, ∏ q ∈ (p ^ (k + 1)).primeFactors, (1 - χ.primitiveCharacter q * f q) = 1 - f p`.
* `DirichletCharacter.prod_one_sub_C_primitiveCharacter_mul_X_powerSeries`: formal power series
  version in `PowerSeries R`.
* `DirichletCharacter.prod_mk_pow_primitiveCharacter`: inverse geometric-series product in
  `PowerSeries R`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* Built on Mathlib's `MulChar.mulEquivToUnitHom` and `DirichletCharacter.fintype` (by Michael Stoll
  and David Loeffler).
-/

public section

namespace DirichletCharacter

section PrimeVanishing

/-- A Dirichlet character modulo `m` vanishes at any prime `p ∣ m`. This holds even when `m = 0`,
since a prime is not a unit in `ℤ = ZMod 0`. -/
theorem apply_prime_eq_zero_of_dvd {R : Type*} [CommMonoidWithZero R] {m p : ℕ}
    (χ : DirichletCharacter R m) (hp : p.Prime) (hpm : p ∣ m) :
    χ (p : ZMod m) = 0 := by
  refine MulChar.map_nonunit χ fun hu ↦ ?_
  rcases eq_or_ne m 0 with rfl | hm0
  · -- `ZMod 0` is definitionally `ℤ`, so `(p : ZMod 0)` is a prime integer and not a unit.
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit hu
  · have : NeZero m := ⟨hm0⟩
    exact (hp.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p m).mp hu)) hpm

/-- For a prime `p`, guarding `1 - χ p * z` by `if p ∣ m then 1 else ...` is redundant, because
`χ p = 0` whenever `p ∣ m`. -/
theorem ite_dvd_one_sub_mul {R : Type*} [CommRing R] {m p : ℕ}
    (χ : DirichletCharacter R m) (hp : p.Prime) (z : R) :
    (if p ∣ m then (1 : R) else 1 - χ (p : ZMod m) * z) = 1 - χ (p : ZMod m) * z := by
  split_ifs with hpm
  · rw [apply_prime_eq_zero_of_dvd χ hp hpm, zero_mul, sub_zero]
  · rfl

/-- When `n = p ^ k * m` with `p` prime and `p ∤ m`, a Dirichlet character modulo `n` factors
through `m` iff `p` does not divide its conductor. -/
theorem factorsThrough_of_eq_pow_mul_iff {R : Type*} [CommMonoidWithZero R] {n p k m : ℕ}
    [NeZero n] (χ : DirichletCharacter R n) (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    χ.FactorsThrough m ↔ ¬ p ∣ χ.conductor := by
  have hm_dvd : m ∣ n := ⟨p ^ k, by rw [hn, mul_comm]⟩
  rw [← mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd χ hm_dvd]
  constructor
  · exact fun h hpc ↦ hm (hpc.trans h)
  · intro hnpc
    have hcop_c : (p ^ k).Coprime χ.conductor :=
      (hp.coprime_iff_not_dvd.mpr hnpc).pow_left k
    have hdvd : χ.conductor ∣ p ^ k * m := hn ▸ χ.conductor_dvd_level
    exact hcop_c.symm.dvd_of_dvd_mul_left hdvd

end PrimeVanishing

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Product of linear character factors modulo `m`.** For `a` coprime to `m ≠ 0`, the product
`∏ χ : DirichletCharacter R m, (1 - C (χ a) * X)` equals `(1 - X ^ f) ^ (φ(m) / f)`, where
`f = orderOf (a : ZMod m)`. -/
theorem prod_one_sub_C_mul_X {m : ℕ} [NeZero m]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)]
    {a : ℕ} (ha : a.Coprime m) :
    ∏ χ : DirichletCharacter R m, (1 - Polynomial.C (χ a) * Polynomial.X) =
      (1 - Polynomial.X ^ orderOf (a : ZMod m)) ^ (m.totient / orderOf (a : ZMod m)) := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime a ha
  have hu_val : (u : ZMod m) = (a : ZMod m) := ZMod.coe_unitOfCoprime a ha
  have hord : orderOf u = orderOf (a : ZMod m) := by rw [← hu_val, orderOf_units]
  have hcard : Nat.card (ZMod m)ˣ = m.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hprod : ∏ χ : DirichletCharacter R m, (1 - Polynomial.C (χ a) * Polynomial.X) =
      ∏ φ : (ZMod m)ˣ →* Rˣ, (1 - Polynomial.C (φ u : R) * Polynomial.X) := by
    refine Fintype.prod_equiv
      (MulChar.mulEquivToUnitHom : DirichletCharacter R m ≃* _).toEquiv _ _ fun χ ↦ ?_
    simp [← hu_val]
  rw [hprod, CommGroup.prod_one_sub_C_monoidHom_mul_X (R := R) u, hord, hcard]

/-- **Product of linear primitive-character factors at a prime `p`.** For `n = p ^ k * m` with
`p` prime and `p ∤ m`, the product over `χ : DirichletCharacter R n` of
`1 - C (χ.primitiveCharacter p) * X` equals `(1 - X ^ f) ^ (φ(m) / f)`, where
`f = orderOf (p : ZMod m)`. This handles ramified (`k > 0`) and unramified (`k = 0`) primes
uniformly. -/
theorem prod_one_sub_C_primitiveCharacter_mul_X {n p k m : ℕ} [NeZero n]
    [hR : HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    ∏ χ : DirichletCharacter R n,
        (1 - Polynomial.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * Polynomial.X) =
      (1 - Polynomial.X ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m)) := by
  classical
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have hm_dvd : m ∣ n := ⟨p ^ k, by rw [hn, mul_comm]⟩
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hm
  have hnot_fac :
      ∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter R n ↦ ¬ χ.FactorsThrough m),
        (1 - Polynomial.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * Polynomial.X) = 1 := by
    refine Finset.prod_eq_one fun χ hχ ↦ ?_
    have hnf := (Finset.mem_filter.mp hχ).2
    rw [factorsThrough_of_eq_pow_mul_iff χ hp hn hm, not_not] at hnf
    rw [apply_prime_eq_zero_of_dvd χ.primitiveCharacter hp hnf, map_zero, zero_mul, sub_zero]
  have hR_m : HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ) :=
    hR.of_dvd R (MonoidHom.exponent_dvd (ZMod.unitsMap_surjective hm_dvd))
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun χ : DirichletCharacter R n ↦
    χ.FactorsThrough m), hnot_fac, mul_one]
  calc ∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter R n ↦ χ.FactorsThrough m),
        (1 - Polynomial.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * Polynomial.X)
      = ∏ χ : {χ : DirichletCharacter R n // χ.FactorsThrough m},
          (1 - Polynomial.C (χ.1.primitiveCharacter (p : ZMod χ.1.conductor)) * Polynomial.X) :=
        Finset.prod_subtype
          (Finset.univ.filter (fun χ : DirichletCharacter R n ↦ χ.FactorsThrough m))
          (fun _ ↦ by simp)
          (fun χ ↦
            1 - Polynomial.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * Polynomial.X)
    _ = ∏ ψ : DirichletCharacter R m, (1 - Polynomial.C (ψ p) * Polynomial.X) := by
        refine Fintype.prod_equiv (factorsThroughEquiv hm_dvd) _ _ fun χ ↦ ?_
        congr 3
        rw [factorsThroughEquiv_apply]
        let ψ : DirichletCharacter R m := χ.2.χ₀
        have hprim : χ.1.primitiveCharacter ((p : ℤ) : ZMod χ.1.conductor) =
            ψ.primitiveCharacter ((p : ℤ) : ZMod ψ.conductor) := by
          have step : ∀ (η : DirichletCharacter R n), η = changeLevel hm_dvd ψ →
              η.primitiveCharacter ((p : ℤ) : ZMod η.conductor) =
                ψ.primitiveCharacter ((p : ℤ) : ZMod ψ.conductor) := by
            rintro _ rfl
            exact primitiveCharacter_changeLevel_apply hm_dvd ψ (p : ℤ)
          exact step χ.1 χ.2.eq_changeLevel
        have hcast : ψ.primitiveCharacter ((p : ℤ) : ZMod ψ.conductor) = ψ (p : ZMod m) := by
          have h1 := changeLevel_eq_cast_of_dvd' ψ.primitiveCharacter
            ψ.conductor_dvd_level (a := (p : ℤ)) (Nat.isCoprime_iff_coprime.mpr hcop)
          rw [changeLevel_primitiveCharacter, Int.cast_natCast] at h1
          exact h1.symm
        simpa only [Int.cast_natCast] using hprim.trans hcast
    _ = (1 - Polynomial.X ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m)) :=
        prod_one_sub_C_mul_X hcop

/-- **Evaluated primitive-character product along a ring homomorphism.** -/
theorem prod_one_sub_map_primitiveCharacter_mul {S : Type*} [CommRing S] (f : R →+* S)
    {n p k m : ℕ} [NeZero n] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) (z : S) :
    ∏ χ : DirichletCharacter R n,
        (1 - f (χ.primitiveCharacter (p : ZMod χ.conductor)) * z) =
      (1 - z ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m)) := by
  have h := congrArg (Polynomial.eval₂RingHom f z)
    (prod_one_sub_C_primitiveCharacter_mul_X (R := R) hp hn hm)
  simpa only [map_prod, map_pow, map_sub, map_one, map_mul, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.eval₂_X] using h

/-- **Scalar evaluated primitive-character product at a prime `p`.** -/
theorem prod_one_sub_primitiveCharacter_mul {n p k m : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) (z : R) :
    ∏ χ : DirichletCharacter R n,
        (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * z) =
      (1 - z ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m)) :=
  prod_one_sub_map_primitiveCharacter_mul (RingHom.id R) hp hn hm z

/-- **Prime-power collapse of the deleted Euler factors.** At any prime-power level `p ^ (k + 1)`,
the double product of `1 - χ.primitiveCharacter q * f q` over all characters modulo `p ^ (k + 1)`
and prime divisors `q ∣ p ^ (k + 1)` collapses to the single factor `1 - f p`. -/
theorem prod_one_sub_primitiveCharacter_mul_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ)
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod (p ^ (k + 1)))ˣ)] (f : ℕ → R) :
    haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    ∏ χ : DirichletCharacter R (p ^ (k + 1)), ∏ q ∈ (p ^ (k + 1)).primeFactors,
        (1 - χ.primitiveCharacter (q : ZMod χ.conductor) * f q) = 1 - f p := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Nat.primeFactors_pow _ (Nat.succ_ne_zero k), hp.primeFactors]
  simp only [Finset.prod_singleton]
  have hn : p ^ (k + 1) = p ^ (k + 1) * 1 := (mul_one _).symm
  have hp1 : (p : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [prod_one_sub_primitiveCharacter_mul hp hn hp.not_dvd_one (f p), hp1, orderOf_one]
  simp

/-- **Product of linear primitive-character factors in `PowerSeries R`.** -/
theorem prod_one_sub_C_primitiveCharacter_mul_X_powerSeries {n p k m : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    ∏ χ : DirichletCharacter R n,
        (1 - PowerSeries.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * PowerSeries.X) =
      (1 - PowerSeries.X ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m)) :=
  prod_one_sub_map_primitiveCharacter_mul (PowerSeries.C (R := R)) hp hn hm PowerSeries.X

/-- **Product of geometric series of primitive-character values at a prime `p`.** In
`PowerSeries R`, the product of `∑ (χ.primitiveCharacter p) ^ j X ^ j` over all characters
`χ : DirichletCharacter R n` equals `((mk 1).subst (X ^ f)) ^ (φ(m) / f)`, where `n = p ^ k * m`
with `p ∤ m` and `f = orderOf (p : ZMod m)`. -/
theorem prod_mk_pow_primitiveCharacter {n p k m : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    ∏ χ : DirichletCharacter R n,
        PowerSeries.mk (fun j ↦ χ.primitiveCharacter (p : ZMod χ.conductor) ^ j) =
      ((PowerSeries.mk 1 : PowerSeries R).subst (PowerSeries.X ^ orderOf (p : ZMod m))) ^
        (m.totient / orderOf (p : ZMod m)) := by
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hm
  have hord_pos : 0 < orderOf (p : ZMod m) := by
    rw [← ZMod.coe_unitOfCoprime p hcop, orderOf_units]
    exact orderOf_pos _
  let A : PowerSeries R :=
    ∏ χ : DirichletCharacter R n,
      PowerSeries.mk (fun j ↦ χ.primitiveCharacter (p : ZMod χ.conductor) ^ j)
  let B : PowerSeries R :=
    ((PowerSeries.mk 1 : PowerSeries R).subst (PowerSeries.X ^ orderOf (p : ZMod m))) ^
      (m.totient / orderOf (p : ZMod m))
  let C : PowerSeries R :=
    (1 - PowerSeries.X ^ orderOf (p : ZMod m)) ^ (m.totient / orderOf (p : ZMod m))
  have hAC : A * C = 1 := by
    dsimp only [A, C]
    rw [← prod_one_sub_C_primitiveCharacter_mul_X_powerSeries (R := R) hp hn hm,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun χ _ ↦ TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one _
  have hBC : B * C = 1 := by
    dsimp only [B, C]
    rw [← PowerSeries.expand_apply (orderOf (p : ZMod m)) hord_pos.ne', ← mul_pow,
      PowerSeries.expand_mk_one_mul_one_sub_X_pow (orderOf (p : ZMod m)) hord_pos.ne', one_pow]
  calc A = A * 1 := (mul_one A).symm
    _ = A * (B * C) := by rw [hBC]
    _ = B * (A * C) := by ring
    _ = B := by rw [hAC, mul_one]

end DirichletCharacter
