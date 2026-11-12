/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Satake

/-!
# The bad primes of a newform

Let `f` be a newform of level `N`, weight `k` and nebentypus `χ`, with `χ` extended by zero to
the integers not coprime to `N`. The Euler factor of `L(s, f)` at a prime `p` is the polynomial
`1 - a_p T + χ(p) p^{k-1} T²` in `T = p^{-s}`, and the Hecke recurrence at `p` reads
`a_{p²} = a_p² - χ(p) p^{k-1}`. So the Euler factor is `1 - a_p T + (a_p² - a_{p²}) T²`, a
polynomial determined by the Fourier coefficients of `f` alone.

The **bad primes** of `f` are the primes at which this Euler factor has degree less than two,
that is, the primes `p` with `a_{p²} = a_p²`. Defined this way, the notion depends only on the
`q`-expansion of `f`, and not on the level at which `f` is presented. The main theorem is that
the bad primes are exactly the prime factors of the level. At a prime `p ∣ N` this rests on the
Atkin–Lehner–Li theorem that a newform is a `U_p`-eigenvector with eigenvalue `a_p`
(`HeckeRing.GL2.Newform.heckeUCuspNat_eq_qExpansion_coeff_smul`), which makes the coefficients
along the powers of `p` geometric. At a prime `p ∤ N` the term `χ(p) p^{k-1}` is nonzero.
The LMFDB lists the bad primes of a newform as the prime divisors of its level (knowl
`cmf.bad_prime`), and `HeckeRing.GL2.Newform.badPrimes_eq_primeFactors` identifies the two.

## Main definitions

* `HeckeRing.GL2.Newform.badPrimes`: the primes `p` with `a_{p²}(f) = a_p(f)²`.

## Main results

* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_sq`: `a_{p²} = a_p² - χ(p) p^{k-1}` at every
  prime `p`.
* `HeckeRing.GL2.Newform.badPrimes_eq_primeFactors`: the bad primes of a newform of level `N`
  are the prime factors of `N`.
* `HeckeRing.GL2.Newform.mem_badPrimes_iff_zero_mem_satakeParameters`: a prime is bad exactly
  when one of the Satake parameters there vanishes, so that the Euler factor has degree at most
  one.
* `HeckeRing.GL2.Newform.mem_badPrimes_iff_forall_qExpansion_coeff_prime_pow`: a prime `p` is
  bad exactly when `a_{p^r} = a_p^r` for every `r`.
* `HeckeRing.GL2.Newform.primeFactors_eq_of_forall_qExpansion_coeff_eq`: two newforms whose
  coefficients agree at every prime and every prime square have levels with the same prime
  factors.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5 and Theorem 5.8.2.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13.
* The LMFDB Collaboration, *The L-functions and modular forms database*, knowl `cmf.bad_prime`,
  <https://www.lmfdb.org/knowledge/show/cmf.bad_prime>.
-/

public section

open UpperHalfPlane

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The Hecke recurrence at a prime square**: `a_{p²} = a_p² - χ(p) p^{k-1}` at every prime
`p`, where the nebentypus `χ` is extended by zero, so that `a_{p²} = a_p²` at a prime dividing
the level. -/
theorem qExpansion_coeff_prime_sq (f : Newform N k) {p : ℕ} (hp : p.Prime) :
    (qExpansion 1 f.toCuspForm).coeff (p ^ 2) =
      (qExpansion 1 f.toCuspForm).coeff p ^ 2 - f.dirichletLift p * (p : ℂ) ^ (k - 1) := by
  have h := f.toEigenform.qExpansion_coeff_prime_pow_add_two
    f.toEigenform_qExpansion_coeff_one hp 0
  simpa only [toEigenform_toCuspForm, toEigenform_χ, ← dirichletLift_def, zero_add, pow_one,
    pow_zero, qExpansion_coeff_one, mul_one, ← sq] using h

/-- The **bad primes** of a newform `f`: the primes `p` with `a_{p²}(f) = a_p(f)²`. These are the
primes at which the Euler factor `1 - a_p T + (a_p² - a_{p²}) T²` of `L(s, f)` has degree less
than two; they are the prime factors of the level (`badPrimes_eq_primeFactors`). -/
def badPrimes (f : Newform N k) : Set ℕ :=
  {p | p.Prime ∧
    (qExpansion 1 f.toCuspForm).coeff (p ^ 2) = (qExpansion 1 f.toCuspForm).coeff p ^ 2}

/-- The defining condition of a bad prime: `p` is prime and `a_{p²} = a_p²`. -/
theorem mem_badPrimes_iff (f : Newform N k) {p : ℕ} :
    p ∈ f.badPrimes ↔ p.Prime ∧
      (qExpansion 1 f.toCuspForm).coeff (p ^ 2) = (qExpansion 1 f.toCuspForm).coeff p ^ 2 :=
  Iff.rfl

/-- **A prime is bad exactly when it divides the level.** -/
theorem mem_badPrimes_iff_dvd (f : Newform N k) {p : ℕ} :
    p ∈ f.badPrimes ↔ p.Prime ∧ p ∣ N := by
  refine and_congr_right fun hp ↦ ?_
  have hpow : (p : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [f.qExpansion_coeff_prime_sq hp, sub_eq_self, mul_eq_zero, or_iff_left hpow,
    MulChar.apply_eq_zero_iff, ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd, not_not]

/-- **The bad primes of a newform of level `N` are the prime factors of `N`.** -/
@[simp]
theorem badPrimes_eq_primeFactors (f : Newform N k) : f.badPrimes = N.primeFactors := by
  ext p
  rw [mem_badPrimes_iff_dvd, Finset.mem_coe, Nat.mem_primeFactors, and_iff_left (NeZero.ne N)]

/-- A newform has only finitely many bad primes. -/
theorem finite_badPrimes (f : Newform N k) : f.badPrimes.Finite := by
  rw [badPrimes_eq_primeFactors]
  exact N.primeFactors.finite_toSet

/-- **A prime is bad exactly when a Satake parameter there vanishes**, that is, when the Euler
factor `(1 - α_p T)(1 - β_p T)` of `L(s, f)` at `p` has degree at most one. -/
theorem mem_badPrimes_iff_zero_mem_satakeParameters (f : Newform N k) {p : ℕ} :
    p ∈ f.badPrimes ↔ p.Prime ∧ 0 ∈ f.satakeParameters p := by
  rw [mem_badPrimes_iff_dvd]
  refine and_congr_right fun hp ↦ ⟨fun hpN ↦ ?_, fun h0 ↦ ?_⟩
  · rw [f.satakeParameters_of_not_coprime (hp.dvd_iff_not_coprime.mp hpN)]
    simp
  · by_contra hpN
    exact f.zero_notMem_satakeParameters hp.ne_zero (hp.coprime_iff_not_dvd.mpr hpN) h0

/-- **At a bad prime the coefficients along the powers of `p` are geometric**: `a_{p^r} = a_p^r`
for every `r`. -/
theorem qExpansion_coeff_prime_pow_of_mem_badPrimes (f : Newform N k) {p : ℕ}
    (hp : p ∈ f.badPrimes) (r : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff (p ^ r) = (qExpansion 1 f.toCuspForm).coeff p ^ r := by
  obtain ⟨hp, hpN⟩ := f.mem_badPrimes_iff_dvd.mp hp
  have hχ : f.dirichletLift p = 0 :=
    f.dirichletLift_apply_eq_zero p (hp.dvd_iff_not_coprime.mp hpN)
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r _ ih =>
    have h := f.toEigenform.qExpansion_coeff_prime_pow_add_two
      f.toEigenform_qExpansion_coeff_one hp r
    simp only [toEigenform_toCuspForm, toEigenform_χ, ← dirichletLift_def, hχ, zero_mul,
      sub_zero] at h
    rw [h, ih, pow_succ' _ (r + 1)]

/-- **A prime `p` is bad exactly when `a_{p^r} = a_p^r` for every `r`.** -/
theorem mem_badPrimes_iff_forall_qExpansion_coeff_prime_pow (f : Newform N k) {p : ℕ} :
    p ∈ f.badPrimes ↔ p.Prime ∧
      ∀ r : ℕ, (qExpansion 1 f.toCuspForm).coeff (p ^ r) =
        (qExpansion 1 f.toCuspForm).coeff p ^ r :=
  ⟨fun hp ↦ ⟨hp.1, f.qExpansion_coeff_prime_pow_of_mem_badPrimes hp⟩,
    fun hp ↦ ⟨hp.1, hp.2 2⟩⟩

/-- **The prime factors of the level are determined by the coefficients at primes and prime
squares**: two newforms, of any levels and weights, whose Fourier coefficients agree at every
prime `p` and at every `p²` have levels with the same prime factors. -/
theorem primeFactors_eq_of_forall_qExpansion_coeff_eq {M : ℕ} [NeZero M] {k' : ℤ}
    (f : Newform N k) (g : Newform M k')
    (h : ∀ p : ℕ, p.Prime →
      (qExpansion 1 f.toCuspForm).coeff p = (qExpansion 1 g.toCuspForm).coeff p ∧
        (qExpansion 1 f.toCuspForm).coeff (p ^ 2) = (qExpansion 1 g.toCuspForm).coeff (p ^ 2)) :
    N.primeFactors = M.primeFactors := by
  have hfg : f.badPrimes = g.badPrimes := by
    ext p
    simp only [mem_badPrimes_iff]
    exact and_congr_right fun hp ↦ by rw [(h p hp).1, (h p hp).2]
  rw [badPrimes_eq_primeFactors, badPrimes_eq_primeFactors] at hfg
  exact_mod_cast hfg

end HeckeRing.GL2.Newform
