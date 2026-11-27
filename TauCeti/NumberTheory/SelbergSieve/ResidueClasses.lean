/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.NumberTheory.SelbergSieve.FiniteFamily
import Mathlib.Data.ZMod.Basic
import TauCeti.Data.Nat.Squarefree
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.SelbergSieve.Legendre

/-!
# Sieving arbitrary residue classes

Many sieve problems remove, for each prime `p` of a finite set `Q`, an arbitrary set
`Ω p ⊆ ZMod p` of residue classes from a weighted population of integers `x a`, rather than the
multiples of `p`. Mathlib's `BoundingSieve` sifts by divisibility, so we encode the local
conditions in a natural number: the *residue label*
`L(b) = ∏_{q ∈ Q, b mod q ∈ Ω q} q`, the product of the primes at which `b` falls into a
removed class. Then a squarefree `d` dividing the prime product divides `L(b)` exactly when `b`
lies in a removed class at every prime factor of `d`, and `b` survives every local condition
exactly when `L(b)` is coprime to the prime product.

`BoundingSieve.ofResidueClasses` is the resulting sieve: its sieving primes are the `p ∈ Q` with
`Ω p` nonempty, its density is the multiplicative function `ν(d) = ∏_{p ∣ d} #(Ω p) / p`, its
approximate mass is an arbitrary real `X`, and its population is the weighted family of labels
`a ↦ L(x a)`. Primes with `Ω p` empty are dropped, since they would have density zero, outside
the range `0 < ν(p) < 1` that `BoundingSieve` demands. Primes with `Ω p` everything are excluded
by the hypothesis `#(Ω p) < p`; for them the avoiding sum simply vanishes
(`TauCeti.sum_filter_forall_notMem_eq_zero_of_card_eq`).

## Main results

* `BoundingSieve.multSum_ofResidueClasses`: the divisibility sum at a divisor `d` of the prime
  product is the weight of the `a` with `x a mod p ∈ Ω p` at every prime `p ∣ d`.
* `BoundingSieve.siftedSum_ofResidueClasses`: the sifted sum is the weight of the `a` with
  `x a mod p ∉ Ω p` for every `p ∈ Q`.
* `BoundingSieve.prod_primeFactors_one_sub_nu_ofResidueClasses`: the Euler product of the sieve
  is `∏_{p ∈ Q} (1 - #(Ω p) / p)`.
* `TauCeti.sum_filter_forall_notMem_eq_mul_prod_add_sum_moebius_mul` and
  `TauCeti.abs_sum_filter_forall_notMem_sub_mul_prod_le_sum_abs`: Legendre's identity and error
  bound for arbitrary local residue conditions and signed weights.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, §11.2 (weighted inclusion-exclusion) and
  §11.4, Definition 11.6.
-/

public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace BoundingSieve

variable {ι : Type*} (A : Finset ι) (x : ι → ℤ) (w : ι → ℝ) (hw : ∀ a ∈ A, 0 ≤ w a)
  (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (Ω : (p : ℕ) → Finset (ZMod p))
  (hΩ : ∀ p ∈ Q, #(Ω p) < p) (X : ℝ)

/-- Every element of a filter of a finite set of primes is prime. -/
private theorem prime_of_mem_filter {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (S : ℕ → Prop)
    [DecidablePred S] : ∀ q ∈ {q ∈ Q | S q}, q.Prime :=
  fun q hq ↦ hQ q (mem_filter.1 hq).1

/-- The sieve removing, at each prime `p ∈ Q`, the residue classes `Ω p` from the integers `x a`
of a weighted finite family. The sieving primes are the `p ∈ Q` with `Ω p` nonempty, the density
is `ν(d) = ∏_{p ∣ d} #(Ω p) / p`, the approximate mass is `X`, and the index `a` is recorded at
its residue label `∏_{q ∈ Q, x a mod q ∈ Ω q} q`. -/
noncomputable def ofResidueClasses : BoundingSieve :=
  ofFiniteFamily
    { support := ∅
      prodPrimes := ∏ p ∈ Q with (Ω p).Nonempty, p
      prodPrimes_squarefree := Nat.squarefree_prod_of_prime (prime_of_mem_filter hQ _)
      weights := 0
      weights_nonneg := fun _ ↦ le_rfl
      totalMass := X
      nu := prodPrimeFactors fun p ↦ (#(Ω p) : ℝ) / p
      nu_mult := IsMultiplicative.prodPrimeFactors _
      nu_pos_of_prime := fun p hp hdvd ↦ by
        have hmem :=
          mem_filter.1 ((Nat.Prime.dvd_prod_iff_mem (prime_of_mem_filter hQ _) hp).1 hdvd)
        rw [prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton]
        exact div_pos (Nat.cast_pos.2 hmem.2.card_pos) (Nat.cast_pos.2 hp.pos)
      nu_lt_one_of_prime := fun p hp hdvd ↦ by
        have hmem :=
          mem_filter.1 ((Nat.Prime.dvd_prod_iff_mem (prime_of_mem_filter hQ _) hp).1 hdvd)
        rw [prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton,
          div_lt_one (Nat.cast_pos.2 hp.pos)]
        exact_mod_cast hΩ p hmem.1 }
    A (fun a ↦ ∏ q ∈ Q with (x a : ZMod q) ∈ Ω q, q) w hw

/-- The support is the set of residue labels of the family. -/
@[simp] theorem ofResidueClasses_support :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).support =
      A.image fun a ↦ ∏ q ∈ Q with (x a : ZMod q) ∈ Ω q, q := by
  rw [ofResidueClasses, ofFiniteFamily_support]

/-- The weight of a label is the total weight of the indices carrying it. -/
@[simp] theorem ofResidueClasses_weights (n : ℕ) :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).weights n =
      ∑ a ∈ A with ∏ q ∈ Q with (x a : ZMod q) ∈ Ω q, q = n, w a := by
  rw [ofResidueClasses, ofFiniteFamily_weights]

/-- The sieving primes are the primes of `Q` at which some residue class is removed. -/
@[simp] theorem ofResidueClasses_prodPrimes :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).prodPrimes = ∏ p ∈ Q with (Ω p).Nonempty, p := by
  rw [ofResidueClasses, ofFiniteFamily_prodPrimes]

/-- The approximate mass is the given real number. -/
@[simp] theorem ofResidueClasses_totalMass :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).totalMass = X := by
  rw [ofResidueClasses, ofFiniteFamily_totalMass]

/-- The density is the multiplicative function `d ↦ ∏_{p ∣ d} #(Ω p) / p`. -/
theorem ofResidueClasses_nu :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).nu = prodPrimeFactors fun p ↦ (#(Ω p) : ℝ) / p := by
  rw [ofResidueClasses, ofFiniteFamily_nu]

/-- At every prime, inside or outside `Q`, the density is the proportion of removed classes. -/
@[simp] theorem ofResidueClasses_nu_apply_prime {p : ℕ} (hp : p.Prime) :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).nu p = #(Ω p) / p := by
  rw [ofResidueClasses_nu, prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton]

/-- A prime at which no residue class is removed is not a sieving prime. -/
theorem not_dvd_ofResidueClasses_prodPrimes {p : ℕ} (hp : p.Prime) (hΩp : Ω p = ∅) :
    ¬p ∣ (ofResidueClasses A x w hw Q hQ Ω hΩ X).prodPrimes := by
  rw [ofResidueClasses_prodPrimes, Nat.Prime.dvd_prod_iff_mem (prime_of_mem_filter hQ _) hp,
    mem_filter, hΩp]
  simp

/-- The divisibility sum at a divisor `d` of the prime product is the weight of the indices whose
integer lies in a removed class at every prime factor of `d`. -/
theorem multSum_ofResidueClasses {d : ℕ}
    (hd : d ∣ (ofResidueClasses A x w hw Q hQ Ω hΩ X).prodPrimes) :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).multSum d =
      ∑ a ∈ A with ∀ p ∈ d.primeFactors, (x a : ZMod p) ∈ Ω p, w a := by
  have hsq : Squarefree d := squarefree_of_dvd_prodPrimes hd
  have hdQ : d.primeFactors ⊆ Q := by
    rw [ofResidueClasses_prodPrimes, Nat.dvd_prod_iff_primeFactors_subset
      (prime_of_mem_filter hQ _) hsq] at hd
    exact hd.trans (filter_subset _ _)
  rw [ofResidueClasses, multSum_ofFiniteFamily]
  refine sum_congr (filter_congr fun a _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.dvd_prod_iff_primeFactors_subset (prime_of_mem_filter hQ _) hsq]
  exact ⟨fun h p hp ↦ (mem_filter.1 (h hp)).2, fun h p hp ↦ mem_filter.2 ⟨hdQ hp, h p hp⟩⟩

/-- The sifted sum is the weight of the indices whose integer avoids the removed classes at every
prime of `Q`. -/
theorem siftedSum_ofResidueClasses :
    (ofResidueClasses A x w hw Q hQ Ω hΩ X).siftedSum =
      ∑ a ∈ A with ∀ p ∈ Q, (x a : ZMod p) ∉ Ω p, w a := by
  rw [ofResidueClasses, siftedSum_ofFiniteFamily]
  refine sum_congr (filter_congr fun a _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.coprime_prod_prod_iff_disjoint (prime_of_mem_filter hQ _)
    (prime_of_mem_filter hQ _), disjoint_filter]
  exact ⟨fun h p hp hx ↦ h p hp ⟨_, hx⟩ hx, fun h p hp _ ↦ h p hp⟩

/-- Dropping the primes with no removed class does not change the Euler product:
`∏_{p ∣ P} (1 - ν(p)) = ∏_{p ∈ Q} (1 - #(Ω p) / p)`. -/
theorem prod_primeFactors_one_sub_nu_ofResidueClasses :
    ∏ p ∈ (ofResidueClasses A x w hw Q hQ Ω hΩ X).prodPrimes.primeFactors,
        (1 - (ofResidueClasses A x w hw Q hQ Ω hΩ X).nu p) =
      ∏ p ∈ Q, (1 - (#(Ω p) : ℝ) / p) := by
  rw [ofResidueClasses_prodPrimes, Nat.primeFactors_prod (prime_of_mem_filter hQ _)]
  refine (prod_congr rfl fun p hp ↦ ?_).trans (prod_filter_of_ne fun p _ hne ↦ ?_)
  · rw [ofResidueClasses_nu_apply_prime (hp := hQ p (mem_filter.1 hp).1)]
  · exact ne_empty_iff_nonempty.1 fun hΩp ↦ hne (by simp [hΩp])

end BoundingSieve

namespace TauCeti

open BoundingSieve

/-- If every residue class modulo some `p ∈ Q` is removed, no index survives, whatever its
weight. -/
theorem sum_filter_forall_notMem_eq_zero_of_card_eq {ι M : Type*} [AddCommMonoid M]
    (A : Finset ι) (x : ι → ℤ) (w : ι → M) {Q : Finset ℕ} (Ω : (p : ℕ) → Finset (ZMod p))
    {p : ℕ} [NeZero p] (hp : p ∈ Q) (hcard : #(Ω p) = p) :
    ∑ a ∈ A with ∀ q ∈ Q, (x a : ZMod q) ∉ Ω q, w a = 0 := by
  have huniv : Ω p = univ := eq_univ_of_card _ (by rw [hcard, ZMod.card])
  refine sum_eq_zero fun a ha ↦ absurd ((mem_filter.1 ha).2 p hp) ?_
  simp [huniv]

/-- Legendre's identity for arbitrary local residue conditions: the weight `S` of the indices
whose integer avoids `Ω p` at every `p ∈ Q` is `X ∏_{p ∈ Q} (1 - #(Ω p) / p)` plus the Möbius
combination, over the squarefree `d` composed of primes of `Q` with `Ω p` nonempty, of the
remainders: the weight of the indices lying in `Ω p` at every `p ∣ d`, minus
`X ∏_{p ∣ d} #(Ω p) / p`. The weights may have either sign. -/
theorem sum_filter_forall_notMem_eq_mul_prod_add_sum_moebius_mul {ι : Type*} (A : Finset ι)
    (x : ι → ℤ) (w : ι → ℝ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (Ω : (p : ℕ) → Finset (ZMod p)) (hΩ : ∀ p ∈ Q, #(Ω p) < p) (X : ℝ) :
    ∑ a ∈ A with ∀ p ∈ Q, (x a : ZMod p) ∉ Ω p, w a =
      X * ∏ p ∈ Q, (1 - (#(Ω p) : ℝ) / p) +
        ∑ d ∈ (∏ p ∈ Q with (Ω p).Nonempty, p).divisors, (μ d : ℝ) *
          (∑ a ∈ A with ∀ p ∈ d.primeFactors, (x a : ZMod p) ∈ Ω p, w a -
            X * ∏ p ∈ d.primeFactors, (#(Ω p) : ℝ) / p) := by
  -- First the case of nonnegative weights, where the sieve `ofResidueClasses` is available.
  have key (v : ι → ℝ) (hv : ∀ a, 0 ≤ v a) (Y : ℝ) :
      ∑ a ∈ A with ∀ p ∈ Q, (x a : ZMod p) ∉ Ω p, v a =
        Y * ∏ p ∈ Q, (1 - (#(Ω p) : ℝ) / p) +
          ∑ d ∈ (∏ p ∈ Q with (Ω p).Nonempty, p).divisors, (μ d : ℝ) *
            (∑ a ∈ A with ∀ p ∈ d.primeFactors, (x a : ZMod p) ∈ Ω p, v a -
              Y * ∏ p ∈ d.primeFactors, (#(Ω p) : ℝ) / p) := by
    set s := ofResidueClasses A x v (fun a _ ↦ hv a) Q hQ Ω hΩ Y
    have h := s.siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem
    rw [siftedSum_ofResidueClasses, ofResidueClasses_totalMass,
      prod_primeFactors_one_sub_nu_ofResidueClasses, ofResidueClasses_prodPrimes] at h
    refine h.trans (congrArg _ (sum_congr rfl fun d hd ↦ ?_))
    have hdP : d ∣ s.prodPrimes := by
      rw [ofResidueClasses_prodPrimes]
      exact Nat.dvd_of_mem_divisors hd
    rw [rem, multSum_ofResidueClasses _ _ _ _ _ _ _ _ _ hdP, ofResidueClasses_totalMass,
      ofResidueClasses_nu,
      prodPrimeFactors_apply (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP), mul_comm Y]
  -- Then split `w` into its positive and negative parts, both nonnegative.
  obtain ⟨u, v, hu, hv, rfl⟩ : ∃ u v : ι → ℝ, (∀ a, 0 ≤ u a) ∧ (∀ a, 0 ≤ v a) ∧ w = u - v :=
    ⟨_, _, fun a ↦ le_max_right (w a) 0, fun a ↦ le_max_right (-w a) 0,
      funext fun a ↦ (max_zero_sub_max_neg_zero_eq_self (w a)).symm⟩
  simp only [Pi.sub_apply, sum_sub_distrib]
  rw [key u hu X, key v hv 0]
  simp only [zero_mul, zero_add, sub_zero]
  rw [add_sub_assoc, ← sum_sub_distrib]
  exact congrArg _ (sum_congr rfl fun d _ ↦ by ring)

/-- The Legendre error bound for arbitrary local residue conditions: the weight `S` of the
indices whose integer avoids `Ω p` at every `p ∈ Q` differs from `X ∏_{p ∈ Q} (1 - #(Ω p) / p)`
by at most the sum, over the squarefree `d` composed of primes of `Q` with `Ω p` nonempty, of the
absolute difference between the weight of the indices lying in `Ω p` at every `p ∣ d` and
`X ∏_{p ∣ d} #(Ω p) / p`. The weights may have either sign. -/
theorem abs_sum_filter_forall_notMem_sub_mul_prod_le_sum_abs {ι : Type*} (A : Finset ι)
    (x : ι → ℤ) (w : ι → ℝ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (Ω : (p : ℕ) → Finset (ZMod p)) (hΩ : ∀ p ∈ Q, #(Ω p) < p) (X : ℝ) :
    |∑ a ∈ A with ∀ p ∈ Q, (x a : ZMod p) ∉ Ω p, w a - X * ∏ p ∈ Q, (1 - (#(Ω p) : ℝ) / p)| ≤
      ∑ d ∈ (∏ p ∈ Q with (Ω p).Nonempty, p).divisors,
        |∑ a ∈ A with ∀ p ∈ d.primeFactors, (x a : ZMod p) ∈ Ω p, w a -
          X * ∏ p ∈ d.primeFactors, (#(Ω p) : ℝ) / p| := by
  rw [sum_filter_forall_notMem_eq_mul_prod_add_sum_moebius_mul A x w Q hQ Ω hΩ X,
    add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ ↦ ?_)
  exact ArithmeticFunction.abs_moebius_mul_le d _

end TauCeti
