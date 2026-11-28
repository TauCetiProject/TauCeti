/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# The ideal of elements with divided powers

For a commutative ring `R`, `TauCeti.pdIdeal R` is the ideal of elements `x ∈ R` such that
`(n ! : R) ∣ x ^ n` for every `n : ℕ`. No divided power structure is chosen on `R`.

When a prime `p` lies in the Jacobson radical of `R` (for instance, when `R` is `p`-adically
complete), we prove that `(p : R) ∈ pdIdeal R`, that the quotient map `R → R ⧸ pdIdeal R` is a
local ring homomorphism, and that `x ↦ x ^ p` descends to a ring homomorphism
`R ⧸ pdIdeal R →+* R ⧸ Ideal.span {(p : R)}`.

## Main definitions and results

* `TauCeti.pdIdeal`: the ideal `{x : R | ∀ n : ℕ, (n ! : R) ∣ x ^ n}`.
* `TauCeti.pdIdeal_le_comap`: ring homomorphisms map `pdIdeal` into `pdIdeal`.
* `TauCeti.prime_mem_pdIdeal`: if a prime `p` lies in `Ring.jacobson R`, then `(p : R) ∈ pdIdeal R`.
* `TauCeti.isLocalHom_pdIdeal_mk`: if a prime `p` lies in `Ring.jacobson R`, then
  `Ideal.Quotient.mk (pdIdeal R)` is a local homomorphism.
* `TauCeti.frobModPd`: the ring homomorphism `R ⧸ pdIdeal R →+* R ⧸ Ideal.span {(p : R)}` induced
  by `x ↦ x ^ p`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/PadicComparison/Descent/TestCategory.lean`
(`New.Variety.pdIdeal`, `New.Variety.pdIdeal_le_comap`) and
`src/Lib/PadicComparison/Crystalline/DividedPowerEnvelope.lean`
(`New.Variety.IsCompleteTorsionFree.p_mem_pdIdeal`,
`New.Variety.IsCompleteTorsionFree.isLocalHom_pdQuotientMk`, `New.Variety.frobModPd`).
-/

public section

namespace TauCeti

open Nat

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The ideal of elements `x` of a commutative ring `R` such that `(n ! : R)` divides `x ^ n`
for every `n : ℕ`. -/
def pdIdeal (R : Type*) [CommRing R] : Ideal R where
  carrier := {x : R | ∀ n : ℕ, (n ! : R) ∣ x ^ n}
  add_mem' {x y} hx hy n := by
    rw [add_pow]
    refine Finset.dvd_sum fun j hj ↦ ?_
    have h_fact : (n ! : R) = (j ! : R) * ((n - j)! : R) * (n.choose j : R) := by
      rw [← Nat.choose_mul_factorial_mul_factorial (Finset.mem_range_succ_iff.mp hj),
        Nat.cast_mul, Nat.cast_mul, mul_assoc, mul_comm]
    rw [h_fact]
    exact mul_dvd_mul_right (mul_dvd_mul (hx j) (hy (n - j))) _
  zero_mem' n := by cases n <;> simp
  smul_mem' c {x} hx n := by
    simpa [mul_pow] using dvd_mul_of_dvd_right (hx n) (c ^ n)

/-- For a prime `p`, the Frobenius map `x ↦ x ^ p` descends to a ring homomorphism
`R ⧸ pdIdeal R →+* R ⧸ Ideal.span {(p : R)}`. -/
def frobModPd (R : Type*) [CommRing R] (p : ℕ) [hp : Fact p.Prime] :
    R ⧸ pdIdeal R →+* R ⧸ Ideal.span {(p : R)} :=
  Ideal.Quotient.lift (pdIdeal R)
    { toFun := fun x ↦ Ideal.Quotient.mk (Ideal.span {(p : R)}) (x ^ p)
      map_one' := by simp
      map_mul' := fun x y ↦ by simp [mul_pow]
      map_zero' := by simp [zero_pow hp.out.ne_zero]
      map_add' := fun x y ↦ by
        rw [← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
        rw [add_pow, Finset.sum_range_succ, hm, Finset.sum_range_succ', ← hm]
        simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero,
          pow_zero, one_mul, mul_one, Nat.cast_one]
        have hsub : (∑ k ∈ Finset.range m, x ^ (k + 1) * y ^ (p - (k + 1)) * ↑(p.choose (k + 1)) +
            y ^ p) + x ^ p - (x ^ p + y ^ p) =
            ∑ k ∈ Finset.range m, x ^ (k + 1) * y ^ (p - (k + 1)) * ↑(p.choose (k + 1)) := by
          abel
        rw [hsub]
        refine Finset.dvd_sum fun k hk ↦ ?_
        have hkp : k + 1 < p := by
          have := Finset.mem_range.mp hk
          omega
        exact dvd_mul_of_dvd_right (Nat.cast_dvd_cast
          (Nat.Prime.dvd_choose_self hp.out (Nat.succ_ne_zero k) hkp)) _ }
    fun x hx ↦ by
      change Ideal.Quotient.mk (Ideal.span {(p : R)}) (x ^ p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact (Nat.cast_dvd_cast (Nat.dvd_factorial hp.out.pos le_rfl)).trans (hx p)

@[simp]
theorem frobModPd_mk (p : ℕ) [Fact p.Prime] (x : R) :
    frobModPd R p (Ideal.Quotient.mk (pdIdeal R) x) =
      Ideal.Quotient.mk (Ideal.span {(p : R)}) (x ^ p) := by
  rfl

/-- Every ring homomorphism `f : R →+* S` carries `pdIdeal R` into `pdIdeal S`. -/
theorem pdIdeal_le_comap (f : R →+* S) : pdIdeal R ≤ (pdIdeal S).comap f := fun _ hx n ↦ by
  simpa [map_pow, map_natCast] using map_dvd f (hx n)

/-- If a prime `p` lies in the Jacobson radical of `R`, then `(p : R) ∈ pdIdeal R`. -/
theorem prime_mem_pdIdeal {p : ℕ} [hp : Fact p.Prime] (hpJ : (p : R) ∈ Ring.jacobson R) :
    (p : R) ∈ pdIdeal R := by
  intro n
  obtain ⟨a, b, hab⟩ := (Nat.coprime_ordCompl hp.out n.factorial_ne_zero).cast (R := R)
  have h_unit : IsUnit ((p : R) * -a + 1) := Ring.mem_jacobson_iff.mp hpJ (-a)
  have h_fact : (n ! : R) ∣ (p : R) ^ multiplicity p n ! := by
    refine h_unit.dvd_mul_right.mp ⟨b, ?_⟩
    have h_split :
        ((p ^ (n !).factorization p * (n ! / p ^ (n !).factorization p) : ℕ) : R) = (n ! : R) :=
      congrArg (Nat.cast : ℕ → R) (Nat.ordProj_mul_ordCompl_eq_self n ! p)
    grind [Nat.factorization_def, hp.out]
  exact h_fact.trans (pow_dvd_pow _ (multiplicity_factorial_le p n))

/-- If a prime `p` lies in the Jacobson radical of `R`, then the quotient map `R →+* R ⧸ pdIdeal R`
is a local ring homomorphism. -/
theorem isLocalHom_pdIdeal_mk {p : ℕ} [hp : Fact p.Prime] (hpJ : (p : R) ∈ Ring.jacobson R) :
    IsLocalHom (Ideal.Quotient.mk (pdIdeal R)) := by
  refine isLocalHom_of_le_jacobson fun x hx ↦ ?_
  rw [← Ideal.jacobson_bot]
  refine Ideal.isRadical_jacobson (⊥ : Ideal R) ⟨p, ?_⟩
  rw [Ideal.jacobson_bot]
  obtain ⟨c, hc⟩ :=
    (Nat.cast_dvd_cast (Nat.dvd_factorial hp.out.pos le_rfl)).trans (hx p)
  rw [hc]
  exact Ideal.mul_mem_right c (Ring.jacobson R) hpJ

end TauCeti
