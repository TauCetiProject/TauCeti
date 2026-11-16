/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime-power factors and exact valuation counts

The least prime belongs to the prime factors of a natural number greater than one, and removing
its full multiplicity gives a smaller number. Removing the `p`-part erases `p` from the prime
factors. These facts support induction by successively removing prime-power blocks. For a
divisor `n ∣ m`, the `p`-free parts are related by `m / n * ordCompl[p] n =
ordCompl[p] m * p ^ (v_p(m) - v_p(n))`, which is how a power map `x ↦ x ^ (m / n)` between groups
of roots of unity acts on their `p`-primary parts. For a prime `p`, a divisor of `p * k` with the
same `p`-free part as `k` either divides `k` or is `p * k`. The product of any set of prime
factors of `n` divides `n`, and for `n ≠ 0` a number is coprime to the product of all the prime
factors of `n` exactly when it is coprime to `n`.

For a prime `p` and `n ≠ 0`, `n.factorization p = k` holds precisely when `p ^ k ∣ n` and
`¬p ^ (k + 1) ∣ n`, giving exact inclusion–exclusion counts on `Finset.Icc 1 N` for one prime
(`N / p ^ k - N / p ^ (k + 1)`) and for two distinct primes (`p ≠ q`). Moreover, if two prime
powers `p ^ k` and `q ^ l` divide `n ≠ 0` with `n < p ^ k * q ^ l`, coprimality forces `p = q`.
Monomial products of an injective family of primes (or fixed positive powers of their casts in
characteristic zero) are injective on finitely supported exponent tuples.

## Provenance

`Nat.coprime_prod_primeFactors_right_iff` restates `coprime_prod_primeFactors_iff_coprime` of
AINTLIB's `LeanModularForms` project (Chris Birkbeck, <https://github.com/CBirkbeck/AINTLIB>,
Apache-2.0, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, file `StrongMultiplicityOne.lean`).
-/

public section

open scoped Finset

namespace Nat

/-- For `1 < n` the least prime factor of `n` is one of its primes. -/
theorem minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) : n.minFac ∈ n.primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn.ne', n.minFac_dvd, by omega⟩

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

/-- Peeling the block at the least prime factor makes `n` strictly smaller. -/
theorem ordCompl_minFac_lt {n : ℕ} (hn : 1 < n) : ordCompl[n.minFac] n < n :=
  Nat.div_lt_self (by omega) (Nat.one_lt_pow
    ((Nat.minFac_prime hn.ne').factorization_pos_of_dvd (by omega) n.minFac_dvd).ne'
    (Nat.minFac_prime hn.ne').one_lt)

/-- Removing the `p`-part of a natural number removes `p` from its prime factors. -/
@[simp]
theorem primeFactors_ordCompl (n p : ℕ) :
    (ordCompl[p] n).primeFactors = n.primeFactors.erase p := by
  rw [← support_factorization, factorization_ordCompl, Finsupp.support_erase,
    support_factorization]

/-- For a divisor `n ∣ m`, the cofactor `m / n` times the `p`-free part of `n` is the `p`-free
part of `m` times the power of `p` by which the `p`-parts of `m` and `n` differ. -/
theorem div_mul_ordCompl_of_dvd {m n : ℕ} (p : ℕ) (h : n ∣ m) :
    m / n * ordCompl[p] n = ordCompl[p] m * p ^ (m.factorization p - n.factorization p) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero hm h
  have hle : n.factorization p ≤ m.factorization p := (factorization_le_iff_dvd hn hm).2 h p
  refine Nat.eq_of_mul_eq_mul_right (ordProj_pos n p) ?_
  rw [mul_assoc, mul_comm (ordCompl[p] n), ordProj_mul_ordCompl_eq_self, Nat.div_mul_cancel h,
    mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_comm, ordProj_mul_ordCompl_eq_self]

/-- For a prime `p`, a divisor `d` of `p * k` with the same `p`-free part as `k` that does not
divide `k` is `p * k`. -/
theorem Prime.eq_mul_of_dvd_mul_of_not_dvd_of_ordCompl_eq {p d k : ℕ} (hp : p.Prime)
    (hd : d ∣ p * k) (hdk : ¬d ∣ k) (h : ordCompl[p] d = ordCompl[p] k) : d = p * k := by
  have hk : k ≠ 0 := by
    rintro rfl
    exact hdk (dvd_zero d)
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (mul_ne_zero hp.ne_zero hk) hd
  have hpk : (p * k).factorization p = k.factorization p + 1 := by
    simp [factorization_mul hp.ne_zero hk, hp.factorization_self, add_comm]
  have hle : d.factorization p ≤ k.factorization p + 1 :=
    hpk ▸ (factorization_le_iff_dvd hd0 (mul_ne_zero hp.ne_zero hk)).2 hd p
  -- If the `p`-part of `d` were at most that of `k`, then `d` would divide `k`.
  have hlt : k.factorization p < d.factorization p := by
    by_contra hge
    refine hdk ?_
    rw [← ordProj_mul_ordCompl_eq_self d p, ← ordProj_mul_ordCompl_eq_self k p, h]
    exact mul_dvd_mul_right (Nat.pow_dvd_pow p (not_lt.1 hge)) _
  rw [← ordProj_mul_ordCompl_eq_self d p, h, ← ordProj_mul_ordCompl_eq_self (p * k) p,
    ordCompl_mul, hpk, show d.factorization p = k.factorization p + 1 by omega]
  simp [hp.factorization_self, Nat.div_self hp.pos]

/-- For a prime `p` and nonzero `n`, the `p`-adic valuation `n.factorization p` equals `k` if and
only if `p ^ k ∣ n` and `¬p ^ (k + 1) ∣ n`. -/
theorem Prime.factorization_eq_iff_pow_dvd_and_not_pow_dvd {p n k : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) : n.factorization p = k ↔ p ^ k ∣ n ∧ ¬p ^ (k + 1) ∣ n := by
  rw [hp.pow_dvd_iff_le_factorization hn, hp.pow_dvd_iff_le_factorization hn]
  omega

/-- If two prime powers `p ^ k` and `q ^ l` divide `n ≠ 0` and their product exceeds `n`, then
`p = q`. -/
theorem Prime.eq_of_pow_dvd_of_lt_mul {p q k l n : ℕ} (hp : p.Prime) (hq : q.Prime) (hn : n ≠ 0)
    (hp_dvd : p ^ k ∣ n) (hq_dvd : q ^ l ∣ n) (hlt : n < p ^ k * q ^ l) : p = q := by
  by_contra hpq
  exact hlt.not_ge (le_of_dvd (pos_of_ne_zero hn)
    ((((coprime_primes hp hq).mpr hpq).pow k l).mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd))

/-- For distinct primes `p ≠ q` and any `M : ℕ`, `M / p + M / q ≤ M` (since one of `p, q` is at
least `2` and the other is at least `3`). -/
theorem Prime.div_add_div_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (M : ℕ) :
    M / p + M / q ≤ M := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have h3 : 3 ≤ p ∨ 3 ≤ q := by omega
  rcases h3 with hp3 | hq3
  · have := Nat.div_le_div_left hp3 (by decide : 0 < 3) (a := M)
    have := Nat.div_le_div_left hq2 (by decide : 0 < 2) (a := M)
    omega
  · have := Nat.div_le_div_left hp2 (by decide : 0 < 2) (a := M)
    have := Nat.div_le_div_left hq3 (by decide : 0 < 3) (a := M)
    omega

/-- Exactly `N / d` natural numbers in `[1, N]` are multiples of `d`. -/
theorem card_filter_Icc_one_dvd (N d : ℕ) : #{n ∈ Finset.Icc 1 N | d ∣ n} = N / d := by
  have h : Finset.Icc 1 N = Finset.Ioc 0 N := by ext; simp; omega
  rw [h, Ioc_filter_dvd_card_eq_div]

/-- For a prime `p`, the number of `n ∈ [1, N]` with `n.factorization p = k` equals
`N / p ^ k - N / p ^ (k + 1)`. -/
theorem card_filter_Icc_factorization_eq (N : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    #{n ∈ Finset.Icc 1 N | n.factorization p = k} = N / p ^ k - N / p ^ (k + 1) := by
  have hsdiff : ({n ∈ Finset.Icc 1 N | n.factorization p = k} : Finset ℕ) =
      {n ∈ Finset.Icc 1 N | p ^ k ∣ n} \ {n ∈ Finset.Icc 1 N | p ^ (k + 1) ∣ n} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    refine ⟨fun ⟨hn, hval⟩ ↦ ?_, fun ⟨⟨hn, hk⟩, hnk⟩ ↦ ⟨hn, ?_⟩⟩
    · obtain ⟨hk, hnk⟩ := (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd (by omega)).mp hval
      exact ⟨⟨hn, hk⟩, fun ⟨_, h⟩ ↦ hnk h⟩
    · exact (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd (by omega)).mpr
        ⟨hk, fun h ↦ hnk ⟨hn, h⟩⟩
  have hsub : ({n ∈ Finset.Icc 1 N | p ^ (k + 1) ∣ n} : Finset ℕ) ⊆
      {n ∈ Finset.Icc 1 N | p ^ k ∣ n} := fun n hn ↦ by
    obtain ⟨hn', hdvd⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn', (pow_dvd_pow p (Nat.le_succ k)).trans hdvd⟩
  rw [hsdiff, Finset.card_sdiff_of_subset hsub, card_filter_Icc_one_dvd, card_filter_Icc_one_dvd]

/-- For distinct primes `p ≠ q`, the number of `n ∈ [1, N]` with `n.factorization p = k` and
`n.factorization q = l` is given by inclusion–exclusion over multiples of `p ^ i * q ^ j`
(`i ∈ {k, k + 1}`, `j ∈ {l, l + 1}`). -/
theorem card_filter_Icc_factorization_eq_and_eq (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (k l : ℕ) :
    #{n ∈ Finset.Icc 1 N | n.factorization p = k ∧ n.factorization q = l} =
      N / (p ^ k * q ^ l) - N / (p ^ k * q ^ (l + 1)) - N / (p ^ (k + 1) * q ^ l) +
        N / (p ^ (k + 1) * q ^ (l + 1)) := by
  have hiff : ∀ i j n : ℕ, p ^ i * q ^ j ∣ n ↔ p ^ i ∣ n ∧ q ^ j ∣ n := fun i j n ↦
    ⟨fun h ↦ ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩, fun ⟨h1, h2⟩ ↦
      (((coprime_primes hp hq).mpr hpq).pow i j).mul_dvd_of_dvd_of_dvd h1 h2⟩
  let s : ℕ → ℕ → Finset ℕ := fun i j ↦ {n ∈ Finset.Icc 1 N | p ^ i * q ^ j ∣ n}
  have hs_card : ∀ i j, #(s i j) = N / (p ^ i * q ^ j) := fun i j ↦ card_filter_Icc_one_dvd N _
  have htarget : ({n ∈ Finset.Icc 1 N | n.factorization p = k ∧ n.factorization q = l} : Finset ℕ) =
      s k l \ (s k (l + 1) ∪ s (k + 1) l) := by
    ext n
    simp only [s, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_union, hiff]
    refine ⟨fun ⟨hn, hvp, hvq⟩ ↦ ?_, fun ⟨⟨hn, hpk, hql⟩, hnot⟩ ↦ ⟨hn, ?_, ?_⟩⟩
    · have hn0 : n ≠ 0 := by omega
      obtain ⟨hpk, hnpk⟩ := (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mp hvp
      obtain ⟨hql, hnql⟩ := (hq.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mp hvq
      exact ⟨⟨hn, hpk, hql⟩, fun h ↦ h.elim (fun ⟨_, _, h'⟩ ↦ hnql h') (fun ⟨_, h', _⟩ ↦ hnpk h')⟩
    · have hn0 : n ≠ 0 := by omega
      exact (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mpr
        ⟨hpk, fun h ↦ hnot (Or.inr ⟨hn, h, hql⟩)⟩
    · have hn0 : n ≠ 0 := by omega
      exact (hq.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mpr
        ⟨hql, fun h ↦ hnot (Or.inl ⟨hn, hpk, h⟩)⟩
  have hsub : s k (l + 1) ∪ s (k + 1) l ⊆ s k l := Finset.union_subset
    (fun n hn ↦ by
      simp only [s, Finset.mem_filter, hiff] at hn ⊢
      exact ⟨hn.1, hn.2.1, (pow_dvd_pow q (Nat.le_succ l)).trans hn.2.2⟩)
    (fun n hn ↦ by
      simp only [s, Finset.mem_filter, hiff] at hn ⊢
      exact ⟨hn.1, (pow_dvd_pow p (Nat.le_succ k)).trans hn.2.1, hn.2.2⟩)
  have hinter : s k (l + 1) ∩ s (k + 1) l = s (k + 1) (l + 1) := by
    ext n
    simp only [s, Finset.mem_inter, Finset.mem_filter, hiff]
    exact ⟨fun ⟨⟨hn, _, hql1⟩, _, hpk1, _⟩ ↦ ⟨hn, hpk1, hql1⟩, fun ⟨hn, hpk1, hql1⟩ ↦
      ⟨⟨hn, (pow_dvd_pow p (Nat.le_succ k)).trans hpk1, hql1⟩,
        hn, hpk1, (pow_dvd_pow q (Nat.le_succ l)).trans hql1⟩⟩
  have h1 := Finset.card_sdiff_add_card_eq_card hsub
  have h2 := Finset.card_union_add_card_inter (s k (l + 1)) (s (k + 1) l)
  rw [← htarget, hs_card] at h1
  rw [hinter, hs_card, hs_card, hs_card] at h2
  have hdiv_q : N / (p ^ k * q ^ (l + 1)) = N / (p ^ k * q ^ l) / q := by
    rw [pow_succ, ← mul_assoc, Nat.div_div_eq_div_mul]
  have hdiv_p : N / (p ^ (k + 1) * q ^ l) = N / (p ^ k * q ^ l) / p := by
    rw [pow_succ, mul_right_comm, Nat.div_div_eq_div_mul]
  have hle : N / (p ^ k * q ^ (l + 1)) + N / (p ^ (k + 1) * q ^ l) ≤ N / (p ^ k * q ^ l) := by
    rw [hdiv_q, hdiv_p, add_comm]
    exact hp.div_add_div_le hq hpq _
  omega

end Nat

namespace TauCeti

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
    have hhom := map_finsuppProd (Nat.castRingHom R) d fun i k ↦ p i ^ (m * k)
    simp only [Nat.coe_castRingHom] at hhom
    rw [Finsupp.prod_mapRange_index (fun _ ↦ rfl), hhom]
    exact Finsupp.prod_congr fun i _ ↦ by simp [pow_mul]
  intro d₁ d₂ h
  have hmap := finsuppProd_prime_pow_injective hp hinj
    (Nat.cast_injective ((hcast d₁).symm.trans (h.trans (hcast d₂))))
  ext i
  exact mul_left_cancel₀ hm (DFunLike.congr_fun hmap i)

end TauCeti
