/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Removing prime-power factors

For a natural number `n`, `n.minFac` lies in `n.primeFactors` exactly when `1 < n` (at `n = 1`,
`Nat.minFac` returns `1`, which is not prime). Removing the full multiplicity of `p` makes `n`
strictly smaller exactly when `p ∈ n.primeFactors`. This is prime-factor membership, not prime
divisibility: `Nat.primeFactors 0` is empty, and `ordCompl[p] 0 = 0` although every prime divides
`0`. Removing the `p`-part erases `p` from the prime factors, and coprimality excludes prime factors
of one number from dividing the other. These facts support induction by successively removing
prime-power blocks. For a divisor `n ∣ m`, the `p`-free parts are related by
`m / n * ordCompl[p] n = ordCompl[p] m * p ^ (v_p(m) - v_p(n))`, which is how a power map
`x ↦ x ^ (m / n)` between groups of roots of unity acts on their `p`-primary parts. For a prime `p`,
a divisor of `p * k` with the same `p`-free part as `k` either divides `k` or is `p * k`, and a
divisor of `n` that does not divide `n / p` is divisible by the full `p`-part `p ^ v_p(n)` of `n`.
The product of any set of prime factors of `n` divides `n`, and for `n ≠ 0` a number is coprime to
the product of all the prime factors of `n` exactly when it is coprime to `n`. Monomial products of
an injective family of primes (or fixed positive powers of their casts in characteristic zero) are
injective on finitely supported exponent tuples.

Conversely, a nonzero `n` is coprime to `q` once no prime factor of `n` divides `q`. Thus, for a
set `S`, the nonzero `n` all of whose prime factors lie in `S` (the `S`-factored numbers) are all
nonzero `n` when `S` contains every prime, only `1` when `S = ∅`, and the `n` coprime to `q` when
`S = {p | ¬ p ∣ q}`.

## Provenance

`Nat.coprime_prod_primeFactors_right_iff` restates `coprime_prod_primeFactors_iff_coprime` of
AINTLIB's `LeanModularForms` project (Chris Birkbeck, <https://github.com/CBirkbeck/AINTLIB>,
Apache-2.0, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, file `StrongMultiplicityOne.lean`).
-/

public section

namespace Nat

/-- The product of a set of prime factors of `n` divides `n`. -/
theorem prod_dvd_of_subset_primeFactors {n : ℕ} {s : Finset ℕ} (h : s ⊆ n.primeFactors) :
    ∏ p ∈ s, p ∣ n :=
  (Finset.prod_dvd_prod_of_subset _ _ id h).trans (prod_primeFactors_dvd n)

/-- **Coprimality only sees the prime factors.** For nonzero `L`, a number is coprime to the
product of the prime factors of `L` exactly when it is coprime to `L`. -/
@[simp]
theorem coprime_prod_primeFactors_right_iff {n L : ℕ} (hL : L ≠ 0) :
    Coprime n (∏ p ∈ L.primeFactors, p) ↔ Coprime n L :=
  ⟨fun h ↦ (h.pow_right L).coprime_dvd_right (dvd_prod_primeFactors_pow_self hL),
    fun h ↦ h.coprime_dvd_right (prod_primeFactors_dvd L)⟩

/-- **Coprimality only sees the prime factors.** For nonzero `L`, the product of the prime factors
of `L` is coprime to a number exactly when `L` is. -/
@[simp]
theorem coprime_prod_primeFactors_left_iff {n L : ℕ} (hL : L ≠ 0) :
    Coprime (∏ p ∈ L.primeFactors, p) n ↔ Coprime L n := by
  rw [coprime_comm, coprime_prod_primeFactors_right_iff hL, coprime_comm]

/-- Removing the `p`-part of a natural number removes `p` from its prime factors. -/
@[simp]
theorem primeFactors_ordCompl (n p : ℕ) :
    (ordCompl[p] n).primeFactors = n.primeFactors.erase p := by
  rw [← support_factorization, factorization_ordCompl, Finsupp.support_erase,
    support_factorization]

/-- For a divisor `n ∣ m`, the cofactor `m / n` times the `p`-free part of `n` is the `p`-free
part of `m` times the power of `p` by which the `p`-parts of `m` and `n` differ. -/
theorem div_mul_ordCompl_of_dvd {m n : ℕ} (p : ℕ) (h : n ∣ m) :
    m / n * ordCompl[p] n = ordCompl[p] m * p ^ (m.factorization p - n.factorization p) :=
  calc m / n * ordCompl[p] n
      = ordProj[p] (m / n) * ordCompl[p] (m / n) * ordCompl[p] n :=
        congrArg (· * ordCompl[p] n) (ordProj_mul_ordCompl_eq_self (m / n) p).symm
    _ = ordCompl[p] (m / n * n) * ordProj[p] (m / n) := by rw [ordCompl_mul]; ac_rfl
    _ = ordCompl[p] m * p ^ (m.factorization p - n.factorization p) := by
        rw [Nat.div_mul_cancel h, factorization_div h, Finsupp.tsub_apply]

/-- For a prime `p`, a divisor `d` of `p * k` with the same `p`-free part as `k` that does not
divide `k` is `p * k`. -/
theorem Prime.eq_mul_of_dvd_mul_of_not_dvd_of_ordCompl_eq {p d k : ℕ} (hp : p.Prime)
    (hd : d ∣ p * k) (hdk : ¬d ∣ k) (h : ordCompl[p] d = ordCompl[p] k) : d = p * k := by
  have hk : k ≠ 0 := fun hk ↦ hdk (hk ▸ dvd_zero d)
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (mul_ne_zero hp.ne_zero hk) hd
  have hle : d.factorization p ≤ k.factorization p + 1 := by
    simpa [factorization_mul hp.ne_zero hk, hp.factorization_self, add_comm] using
      (factorization_le_iff_dvd hd0 (mul_ne_zero hp.ne_zero hk)).2 hd p
  -- If the `p`-part of `d` were at most that of `k`, then `d` would divide `k`.
  have hlt : k.factorization p < d.factorization p := by
    by_contra hge
    refine hdk ?_
    rw [← ordProj_mul_ordCompl_eq_self d p, ← ordProj_mul_ordCompl_eq_self k p, h]
    exact mul_dvd_mul_right (Nat.pow_dvd_pow p (not_lt.1 hge)) _
  -- So the `p`-part of `d` is `p` times that of `k`, while the `p`-free parts agree.
  have hdp : d.factorization p = k.factorization p + 1 := by omega
  rw [← ordProj_mul_ordCompl_eq_self d p, h, hdp, pow_succ', mul_assoc,
    ordProj_mul_ordCompl_eq_self]

/-- For a prime `p`, a divisor `d` of `n` that does not divide `n / p` is divisible by
`p ^ v_p(n)`. -/
theorem Prime.pow_multiplicity_dvd_of_dvd_of_not_dvd_div {p n d : ℕ} (hp : p.Prime) (hd : d ∣ n)
    (hdp : ¬d ∣ n / p) : p ^ multiplicity p n ∣ d := by
  obtain ⟨c, rfl⟩ := hd
  have hc : ¬p ∣ c := by
    rintro ⟨c', rfl⟩
    exact hdp ⟨c', by rw [mul_left_comm, Nat.mul_div_cancel_left _ hp.pos]⟩
  exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hc)).dvd_of_dvd_mul_right
    (pow_multiplicity_dvd p (d * c))

/-- No prime factor of `n` divides `p` when `n` and `p` are coprime. -/
theorem Coprime.not_dvd_of_mem_primeFactors {n p q : ℕ} (hcop : n.Coprime p)
    (hq : q ∈ n.primeFactors) : ¬ q ∣ p :=
  (prime_of_mem_primeFactors hq).coprime_iff_not_dvd.mp
    (hcop.coprime_dvd_left (dvd_of_mem_primeFactors hq))

/-- A natural number `n > 1` coprime to `p` has a prime factor not dividing `p`. -/
theorem Coprime.exists_mem_primeFactors_not_dvd {n p : ℕ} (hcop : n.Coprime p) (hn : 1 < n) :
    ∃ q ∈ n.primeFactors, ¬ q ∣ p :=
  let ⟨q, hq⟩ := nonempty_primeFactors.2 hn
  ⟨q, hq, hcop.not_dvd_of_mem_primeFactors hq⟩

/-- A nonzero `n` is coprime to `q` exactly when no prime factor of `n` divides `q`: the nonzero
`n` coprime to `q` are those all of whose prime factors lie in `{p | ¬ p ∣ q}`. -/
theorem coprime_iff_forall_mem_primeFactors_not_dvd {n q : ℕ} (hn : n ≠ 0) :
    n.Coprime q ↔ ∀ p ∈ n.primeFactors, ¬ p ∣ q :=
  ⟨fun h _ hp ↦ h.not_dvd_of_mem_primeFactors hp,
    fun h ↦ coprime_of_dvd fun p hp hpn ↦ h p (mem_primeFactors.2 ⟨hp, hpn, hn⟩)⟩

/-- If `S` contains every prime, every prime factor of every `n` lies in `S`. -/
theorem forall_mem_primeFactors_mem_of_setOf_prime_subset {S : Set ℕ}
    (hS : {p : ℕ | p.Prime} ⊆ S) (n : ℕ) : ∀ p ∈ n.primeFactors, p ∈ S :=
  fun _ hp ↦ hS (prime_of_mem_primeFactors hp)

/-- A nonzero `n` has all of its prime factors in `∅` exactly when `n = 1`. -/
theorem forall_mem_primeFactors_mem_empty_iff {n : ℕ} (hn : n ≠ 0) :
    (∀ p ∈ n.primeFactors, p ∈ (∅ : Set ℕ)) ↔ n = 1 := by
  simp only [Set.mem_empty_iff_false, imp_false, ← Finset.eq_empty_iff_forall_notMem,
    primeFactors_eq_empty]
  omega

end Nat

namespace TauCeti

/-- `n.minFac` lies in `n.primeFactors` exactly when `1 < n`. At `n = 1`, `Nat.minFac` returns `1`,
which is not prime, and `Nat.primeFactors 0` is empty. -/
theorem minFac_mem_primeFactors_iff {n : ℕ} : n.minFac ∈ n.primeFactors ↔ 1 < n := by
  rw [Nat.mem_primeFactors, Nat.minFac_prime_iff]
  simp only [Nat.minFac_dvd, true_and]
  omega

/-- Removing the `p`-part of `n` makes `n` strictly smaller exactly when `p ∈ n.primeFactors`.
This is stronger than `p` being a prime divisor of `n`: every prime divides `0`, but
`ordCompl[p] 0 = 0` and `Nat.primeFactors 0` is empty. -/
@[simp]
theorem ordCompl_lt_self_iff {n p : ℕ} : ordCompl[p] n < n ↔ p ∈ n.primeFactors := by
  by_cases hp : p.Prime
  · rw [(Nat.ordCompl_le n p).lt_iff_ne, Ne, Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hp,
      Nat.mem_primeFactors]
    tauto
  · rw [Nat.ordCompl_of_not_prime n p hp]
    simp [hp]

/-- Monomial products of an injective family of prime natural numbers are injective on finitely
supported exponent tuples. -/
theorem finsuppProd_prime_pow_injective {ι : Type*} {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) :
    Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun i k ↦ p i ^ k := by
  classical
  intro d₁ d₂ h
  have hmap (d : ι →₀ ℕ) : (d.prod fun i k ↦ p i ^ k).factorization = d.mapDomain p := by
    rw [← Finsupp.prod_mapDomain_index_inj hinj]
    exact Nat.factorization_prod_pow_eq_self fun q hq ↦ by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hq)
      exact hp i
  exact Finsupp.mapDomain_injective hinj
    ((hmap d₁).symm.trans ((congrArg Nat.factorization h).trans (hmap d₂)))

/-- In a characteristic-zero commutative semiring `R`, monomial products of fixed positive powers
`(p i : R) ^ m` (`m ≠ 0`) of an injective family of primes are injective on finitely supported
exponent tuples. -/
theorem finsuppProd_natCast_prime_pow_injective {R ι : Type*} [CommSemiring R] [CharZero R]
    {p : ι → ℕ} (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) {m : ℕ}
    (hm : m ≠ 0) :
    Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun i k ↦ ((p i : R) ^ m) ^ k := by
  have hcast (d : ι →₀ ℕ) :
      (d.prod fun i k ↦ ((p i : R) ^ m) ^ k) =
        (((d.mapRange (m * ·) (mul_zero m)).prod fun i k ↦ p i ^ k : ℕ) : R) := by
    rw [Finsupp.prod_mapRange_index (fun _ ↦ rfl), Nat.cast_finsuppProd]
    exact Finsupp.prod_congr fun i _ ↦ by simp [pow_mul]
  intro d₁ d₂ h
  exact Finsupp.mapRange_injective (m * ·) (mul_zero m) (mul_right_injective₀ hm)
    (finsuppProd_prime_pow_injective hp hinj
      (Nat.cast_injective ((hcast d₁).symm.trans (h.trans (hcast d₂)))))

end TauCeti
