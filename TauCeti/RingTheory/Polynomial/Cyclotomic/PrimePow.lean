/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.NumberTheory.Basic
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# The shifted prime-power cyclotomic polynomials

For a prime `p` and `n : ℕ`, write `ξ_n = Φ_{p ^ n}(X + 1)` for the `p ^ n`-th cyclotomic
polynomial in the variable `T = X` with `1 + T` substituted for `X`, and
`ω_n = (1 + X) ^ p ^ n - 1`. Thus `ξ_0 = X` and, for `n ≥ 0`,

```text
ξ_{n+1} = ∑_{i < p} (1 + X) ^ (i p ^ n),        ω_n = ξ_0 ξ_1 ⋯ ξ_n.
```

In Iwasawa theory, with `1 + T` the image of a topological generator of `Γ ≅ ℤ_p` in the Iwasawa
algebra `O⟦T⟧`, `ω_n` cuts out the group ring of `Γ / Γ ^ p ^ n` and the `ξ_n` are its
cyclotomic factors; they are the polynomials appearing in the growth formula for the quotients
`M / ω_n M` of a finitely generated `O⟦T⟧`-module `M`.

This file develops the ring-theoretic facts about the `ξ_n` that this needs, over an arbitrary
commutative ring `R` unless stated otherwise. Each `ξ_n` is monic of degree `φ(p ^ n)`, with
constant coefficient `p` for `n ≥ 1`. In characteristic `p` it is the monomial `X ^ φ(p ^ n)`.
It is distinguished at every ideal containing `p`, so that Weierstrass division by `ξ_n` is
available in `O⟦T⟧`. When `p` is a prime element of a domain `R` (for instance `R = ℤ_p`) every
`ξ_n` is irreducible: `ξ_0 = X`, and for `n ≥ 1` the polynomial `ξ_n` is Eisenstein at `(p)`.

## Main results

* `Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one`: `ω_n = ∏_{m ≤ n} ξ_m`.
* `Polynomial.cyclotomic_prime_pow_comp_X_add_one_eq_X_pow`: in characteristic `p`,
  `ξ_n = X ^ φ(p ^ n)`.
* `Polynomial.cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt`: `ξ_n` is distinguished at
  every ideal containing `p`.
* `Polynomial.irreducible_cyclotomic_prime_pow_comp_X_add_one`: over a domain in which `p` is
  prime, `ξ_n` is irreducible.
* `Polynomial.sq_dvd_eval_cyclotomic_prime_pow_comp_X_add_one_sub`: if `p ∣ t ^ p ^ k`, then
  `ξ_{n+1}(t) ≡ p` modulo `p ^ 2` for every `n > k`.
* `Polynomial.IsDistinguishedAt.sq_dvd_aeval_cyclotomic_prime_pow_comp_X_add_one_sub`: at a root
  `t` of a polynomial `F` distinguished at `I` with `I ^ e ⊆ (p)`, `ξ_{n+1}(t) ≡ p` modulo `p ^ 2`
  for `n > deg F * e`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, §5.3, (5.3.5) and (5.3.13)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §7.1.
-/

public section

namespace Polynomial

open Finset

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- `ξ_{n+1} = Φ_{p ^ (n + 1)}(X + 1)` is the geometric sum `∑_{i < p} (1 + X) ^ (i p ^ n)`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_eq_sum (n : ℕ) :
    (cyclotomic (p ^ (n + 1)) R).comp (X + 1) = ∑ i ∈ range p, (1 + X) ^ (i * p ^ n) := by
  simp [cyclotomic_prime_pow_eq_geom_sum hp.out, ← pow_mul, add_comm, mul_comm]

/-- `ω_{n+1} = ξ_{n+1} ω_n`, that is,
`Φ_{p ^ (n + 1)}(X + 1) ((1 + X) ^ p ^ n - 1) = (1 + X) ^ p ^ (n + 1) - 1`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_mul (n : ℕ) :
    (cyclotomic (p ^ (n + 1)) R).comp (X + 1) * ((1 + X) ^ p ^ n - 1) =
      (1 + X) ^ p ^ (n + 1) - 1 := by
  have := congr_arg (·.comp (X + 1 : R[X])) (cyclotomic_prime_pow_mul_X_pow_sub_one R p n)
  simpa [mul_comp, add_comm] using this

/-- **`ω_n = ξ_0 ξ_1 ⋯ ξ_n`**: `(1 + X) ^ p ^ n - 1 = ∏_{m ≤ n} Φ_{p ^ m}(X + 1)`. -/
theorem prod_range_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ∏ m ∈ range (n + 1), (cyclotomic (p ^ m) R).comp (X + 1) = (1 + X) ^ p ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, mul_comm, cyclotomic_prime_pow_comp_X_add_one_mul]

/-- `ξ_m` divides `ω_n` for `m ≤ n`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_dvd {m n : ℕ} (h : m ≤ n) :
    (cyclotomic (p ^ m) R).comp (X + 1) ∣ (1 + X) ^ p ^ n - 1 := by
  rw [← prod_range_cyclotomic_prime_pow_comp_X_add_one]
  exact dvd_prod_of_mem _ (mem_range.2 (Nat.lt_succ_of_le h))

/-- The constant coefficient of `ξ_{n+1}` is `p`. -/
@[simp]
theorem coeff_zero_cyclotomic_prime_pow_comp_X_add_one (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) R).comp (X + 1)).coeff 0 = p := by
  simp [coeff_zero_eq_eval_zero, eval_comp]

/-- In characteristic `p`, `ξ_n = Φ_{p ^ n}(X + 1)` is the monomial `X ^ φ(p ^ n)`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_eq_X_pow [CharP R p] (n : ℕ) :
    (cyclotomic (p ^ n) R).comp (X + 1) = X ^ (p ^ n).totient := by
  rcases n with _ | n
  · simp
  have h := cyclotomic_mul_prime_pow_eq R (p := p) (m := 1) hp.out.not_dvd_one n.succ_pos
  rw [mul_one] at h
  simp [h, Nat.totient_prime_pow_succ hp.out, Nat.mul_sub_one, ← pow_succ]

/-- **`ξ_n` is distinguished at every ideal containing `p`**: it is monic and its non-leading
coefficients lie in `I`. For `n = 0` this is the statement for `ξ_0 = X`. For `n ≥ 1`, over `ℤ`
it is the Eisenstein property of `Φ_{p ^ n}(X + 1)` at `p`, and the general case is its image. -/
theorem cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt {I : Ideal R} (hI : (p : R) ∈ I)
    (n : ℕ) : ((cyclotomic (p ^ n) R).comp (X + 1)).IsDistinguishedAt I := by
  refine ⟨⟨fun {k} hk ↦ ?_⟩, monic_cyclotomic_comp_X_add_one _⟩
  rcases n with _ | n
  · have hX : (cyclotomic (p ^ 0) R).comp (X + 1) = X := by simp
    rw [hX] at hk ⊢
    rcases subsingleton_or_nontrivial R with hR | hR
    · simp [Subsingleton.elim ((X : R[X]).coeff k) 0]
    · rw [natDegree_X, Nat.lt_one_iff] at hk
      simp [hk]
  · have hZ := (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).isWeaklyEisensteinAt.map
      (Int.castRingHom R)
    have hmap : ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).map (Int.castRingHom R) =
        (cyclotomic (p ^ (n + 1)) R).comp (X + 1) := by
      simp [map_comp]
    rw [hmap] at hZ
    refine Ideal.map_le_iff_le_comap.2 ?_ (hZ.mem hk)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    simpa using hI

/-- Over a domain in which `p` is a prime element, `ξ_{n+1} = Φ_{p ^ (n + 1)}(X + 1)` is Eisenstein
at `(p)`. This generalises Mathlib's `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt` from `ℤ`
to, for instance, `ℤ_p`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_of_prime [IsDomain R]
    (hpR : Prime (p : R)) (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) R).comp (X + 1)).IsEisensteinAt (Ideal.span {(p : R)}) := by
  have hD := cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt p
    (Ideal.mem_span_singleton_self (p : R)) (n + 1)
  refine ⟨?_, hD.mem, ?_⟩
  · rw [hD.monic.leadingCoeff, Ideal.mem_span_singleton]
    exact hpR.not_dvd_one
  · rw [coeff_zero_cyclotomic_prime_pow_comp_X_add_one, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, pow_two]
    intro h
    exact hpR.not_dvd_one ((mul_dvd_mul_iff_left hpR.ne_zero).1 (by simpa using h))

/-- **`ξ_n = Φ_{p ^ n}(X + 1)` is irreducible** over a domain in which `p` is a prime element, such
as `ℤ_p`: `ξ_0 = X`, and for `n ≥ 1` it is Eisenstein at `(p)`. -/
theorem irreducible_cyclotomic_prime_pow_comp_X_add_one [IsDomain R] (hpR : Prime (p : R))
    (n : ℕ) : Irreducible ((cyclotomic (p ^ n) R).comp (X + 1)) := by
  rcases n with _ | n
  · simpa using irreducible_X
  · exact (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_of_prime p hpR n).irreducible
      ((Ideal.span_singleton_prime hpR.ne_zero).2 hpR)
      (monic_cyclotomic_comp_X_add_one _).isPrimitive
      (by simpa using Nat.totient_pos.2 (pow_pos hp.out.pos _))

/-- **`ξ_{n+1}(t) ≡ p` modulo `p ^ 2` once `t ^ p ^ k` is divisible by `p` and `n > k`.**

On a ring in which `p` lies in the Jacobson radical, this says that `ξ_{n+1}(t)` is `p` times a
unit; this is how the cyclotomic factors act on a finite free quotient `O⟦T⟧ ⧸ (F)` of the Iwasawa
algebra by a distinguished polynomial `F` (NSW Lemma 5.3.18). -/
theorem sq_dvd_eval_cyclotomic_prime_pow_comp_X_add_one_sub {t : R} {k n : ℕ}
    (ht : (p : R) ∣ t ^ p ^ k) (hkn : k < n) :
    (p : R) ^ 2 ∣ ((cyclotomic (p ^ (n + 1)) R).comp (X + 1)).eval t - p := by
  have hk : (p : R) ∣ (1 + t) ^ p ^ k - 1 := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out 1 t k
    have hring : 1 ^ p ^ k + t ^ p ^ k + p * 1 * t * r - 1 = t ^ p ^ k + p * (t * r) := by ring
    rw [hr, hring]
    exact dvd_add ht (dvd_mul_right _ _)
  have hn : (p : R) ^ 2 ∣ (1 + t) ^ p ^ n - 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hkn
    have h := dvd_sub_pow_of_dvd_sub hk (j + 1)
    have hkj : k + (j + 1) = k + j + 1 := by omega
    rw [one_pow, ← pow_mul, ← pow_add, hkj] at h
    exact (pow_dvd_pow _ (by omega)).trans h
  have hsum : ((cyclotomic (p ^ (n + 1)) R).comp (X + 1)).eval t - p =
      ∑ i ∈ range p, (((1 + t) ^ p ^ n) ^ i - 1) := by
    rw [cyclotomic_prime_pow_comp_X_add_one_eq_sum, ← coe_evalRingHom, map_sum]
    simp [sum_sub_distrib, ← pow_mul, mul_comm]
  rw [hsum]
  exact dvd_sum fun i _ ↦ hn.trans (sub_one_dvd_pow_sub_one _ i)

end Polynomial

namespace Polynomial.IsDistinguishedAt

variable {O : Type*} [CommRing O] {I : Ideal O} {F : O[X]} {p e : ℕ} [hp : Fact p.Prime]

/-- If `F` is distinguished at `I` and `I ^ e ⊆ (p)`, then at every root `t` of `F` in an
`O`-algebra, `ξ_{n+1}(t) = Φ_{p ^ (n + 1)}(1 + t)` is congruent to `p` modulo `p ^ 2` for every
`n > deg F * e`. -/
theorem sq_dvd_aeval_cyclotomic_prime_pow_comp_X_add_one_sub (hF : F.IsDistinguishedAt I)
    (hI : I ^ e ≤ Ideal.span {(p : O)}) {S : Type*} [CommRing S] [Algebra O S] {t : S}
    (ht : aeval t F = 0) {n : ℕ} (hn : F.natDegree * e < n) :
    (p : S) ^ 2 ∣ aeval t ((cyclotomic (p ^ (n + 1)) O).comp (X + 1)) - p := by
  have hdvd : (p : S) ∣ t ^ p ^ (F.natDegree * e) :=
    (hF.natCast_dvd_pow_of_aeval_eq_zero hI ht).trans
      (pow_dvd_pow _ (Nat.lt_pow_self hp.out.one_lt).le)
  rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_comp, map_cyclotomic, Polynomial.map_add,
    map_X, Polynomial.map_one]
  exact sq_dvd_eval_cyclotomic_prime_pow_comp_X_add_one_sub p hdvd hn

end Polynomial.IsDistinguishedAt
