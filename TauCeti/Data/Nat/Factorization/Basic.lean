/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Data.Nat.Cast.Order.Field

/-!
# Prime-power factors and exact valuation counts

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

For a prime `p` and `n ≠ 0`, `n.factorization p = k` holds precisely when `p ^ k ∣ n` and
`¬p ^ (k + 1) ∣ n`, giving exact inclusion–exclusion counts on `Finset.Icc 1 N` for one prime
(`N / p ^ k - N / p ^ (k + 1)`) and for two distinct primes (`p ≠ q`). Casting these counts to
an `AddCommGroupWithOne`, `Semifield`, or linearly ordered `Field` yields exact indicator-sum
identities, the unconditional upper bound `≤ N / p ^ k`, single-prime and two-prime discrepancy
bounds `< 1` and `< 2` around the asymptotic densities `1 / p ^ k - 1 / p ^ (k + 1)`, and the
centered pairwise correlation bound `< 3` for distinct primes `p ≠ q` across all `k, l : ℕ`.

## Provenance

`Nat.coprime_prod_primeFactors_right_iff` restates `coprime_prod_primeFactors_iff_coprime` of
AINTLIB's `LeanModularForms` project (Chris Birkbeck, <https://github.com/CBirkbeck/AINTLIB>,
Apache-2.0, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, file `StrongMultiplicityOne.lean`).
-/

public section

open scoped Finset

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

/-- For a prime `p` and nonzero `n`, the `p`-adic valuation `n.factorization p` equals `k` if and
only if `p ^ k ∣ n` and `¬p ^ (k + 1) ∣ n`. -/
theorem Prime.factorization_eq_iff_pow_dvd_and_not_pow_dvd {p n k : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) : n.factorization p = k ↔ p ^ k ∣ n ∧ ¬p ^ (k + 1) ∣ n := by
  rw [hp.pow_dvd_iff_le_factorization hn, hp.pow_dvd_iff_le_factorization hn]
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

/-- For all `N, p, k : ℕ` (without assuming `p` is prime), at most `N / p ^ k` numbers in `[1, N]`
satisfy `n.factorization p = k`. -/
theorem card_filter_Icc_factorization_eq_le (N p k : ℕ) :
    #{n ∈ Finset.Icc 1 N | n.factorization p = k} ≤ N / p ^ k := by
  by_cases hp : p.Prime
  · rw [card_filter_Icc_factorization_eq N hp k]
    exact Nat.sub_le _ _
  · have hzero : ∀ n : ℕ, n.factorization p = 0 := fun n ↦
      factorization_eq_zero_of_not_prime n hp
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hzero]
    · simp [hzero, hk.symm]

/-- Helper for `Nat.card_filter_Icc_factorization_eq_and_eq` and
`Nat.sum_Icc_ite_factorization_eq_and_eq`: when `2 ≤ p` and `2 ≤ q`, subtracting the two single-step
refinement counts from `N / (p ^ k * q ^ l)` does not underflow in `ℕ`. -/
private lemma div_pow_mul_pow_succ_add_le (N : ℕ) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (k l : ℕ) :
    N / (p ^ k * q ^ (l + 1)) + N / (p ^ (k + 1) * q ^ l) ≤ N / (p ^ k * q ^ l) := by
  have hq2 : N / (p ^ k * q ^ (l + 1)) ≤ N / (p ^ k * q ^ l) / 2 := by
    rw [pow_succ, ← mul_assoc, ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left hq zero_lt_two
  have hp2 : N / (p ^ (k + 1) * q ^ l) ≤ N / (p ^ k * q ^ l) / 2 := by
    rw [pow_succ, mul_right_comm, ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left hp zero_lt_two
  omega

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
  have hle := div_pow_mul_pow_succ_add_le N hp.two_le hq.two_le k l
  omega

/-- Indicator-sum form of `Nat.card_filter_Icc_factorization_eq` in any `AddCommGroupWithOne`. -/
theorem sum_Icc_ite_factorization_eq {α : Type*} [AddCommGroupWithOne α] (N : ℕ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) =
      ((N / p ^ k : ℕ) : α) - ((N / p ^ (k + 1) : ℕ) : α) := by
  have hle : N / p ^ (k + 1) ≤ N / p ^ k :=
    Nat.div_le_div_left (Nat.pow_le_pow_right hp.pos (Nat.le_succ k)) (pow_pos hp.pos k)
  rw [Finset.sum_boole, card_filter_Icc_factorization_eq N hp k, Nat.cast_sub hle]

/-- For all `N, p, k : ℕ` (without assuming `p` is prime), the indicator sum of
`n.factorization p = k` over `Finset.Icc 1 N` in a linearly ordered semifield is at most
`N / p ^ k`. -/
theorem sum_Icc_ite_factorization_le {α : Type*} [Semifield α] [LinearOrder α]
    [IsStrictOrderedRing α] (N p k : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) ≤
      (N : α) / (p : α) ^ k := by
  rw [Finset.sum_boole]
  exact (Nat.cast_le.mpr (card_filter_Icc_factorization_eq_le N p k)).trans
    (by simpa [Nat.cast_pow] using Nat.cast_div_le (α := α) (m := N) (n := p ^ k))

/-- Indicator-sum form of `Nat.card_filter_Icc_factorization_eq_and_eq` in any
`AddCommGroupWithOne`. -/
theorem sum_Icc_ite_factorization_eq_and_eq {α : Type*} [AddCommGroupWithOne α] (N : ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k l : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
        (if n.factorization p = k ∧ n.factorization q = l then (1 : α) else 0) =
      ((N / (p ^ k * q ^ l) : ℕ) : α) - ((N / (p ^ k * q ^ (l + 1)) : ℕ) : α) -
        ((N / (p ^ (k + 1) * q ^ l) : ℕ) : α) +
          ((N / (p ^ (k + 1) * q ^ (l + 1)) : ℕ) : α) := by
  have hle := div_pow_mul_pow_succ_add_le N hp.two_le hq.two_le k l
  rw [Finset.sum_boole, card_filter_Icc_factorization_eq_and_eq N hp hq hpq k l, Nat.cast_add,
    Nat.cast_sub (Nat.le_sub_of_add_le' hle), Nat.cast_sub (Nat.le_of_add_right_le hle)]

/-- For a prime `p`, the exact-valuation indicator sum over `Finset.Icc 1 N` is strictly within `1`
of `N * (1 / p ^ k - 1 / p ^ (k + 1))` in any linearly ordered field. -/
theorem abs_sum_Icc_ite_factorization_sub_lt_one {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (N : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1))| < 1 := by
  have hr1_0 : (0 : α) ≤ (N : α) / ((p ^ k : ℕ) : α) - ((N / p ^ k : ℕ) : α) :=
    sub_nonneg.mpr Nat.cast_div_le
  have hr1_1 : (N : α) / ((p ^ k : ℕ) : α) - ((N / p ^ k : ℕ) : α) < 1 :=
    Nat.div_sub_cast_div_lt_one N (p ^ k)
  have hr2_0 : (0 : α) ≤ (N : α) / ((p ^ (k + 1) : ℕ) : α) - ((N / p ^ (k + 1) : ℕ) : α) :=
    sub_nonneg.mpr Nat.cast_div_le
  have hr2_1 : (N : α) / ((p ^ (k + 1) : ℕ) : α) - ((N / p ^ (k + 1) : ℕ) : α) < 1 :=
    Nat.div_sub_cast_div_lt_one N (p ^ (k + 1))
  push_cast at hr1_0 hr1_1 hr2_0 hr2_1
  have hdiff : (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)) =
      ((N : α) / (p : α) ^ (k + 1) - ((N / p ^ (k + 1) : ℕ) : α)) -
        ((N : α) / (p : α) ^ k - ((N / p ^ k : ℕ) : α)) := by
    rw [sum_Icc_ite_factorization_eq N hp k]; ring
  rw [hdiff, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- For distinct primes `p ≠ q`, the joint exact-valuation indicator sum over `Finset.Icc 1 N` is
strictly within `2` of `N * (1 / p ^ k - 1 / p ^ (k + 1)) * (1 / q ^ l - 1 / q ^ (l + 1))` in any
linearly ordered field. -/
theorem abs_sum_Icc_ite_factorization_mul_sub_lt_two {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k l : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
        (if n.factorization q = l then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)) *
        (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1))| < 2 := by
  have hboole : ∀ n : ℕ, (if n.factorization p = k then (1 : α) else 0) *
      (if n.factorization q = l then (1 : α) else 0) =
      if n.factorization p = k ∧ n.factorization q = l then (1 : α) else 0 := fun n ↦ by
    split_ifs <;> simp_all
  have hsum : (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
        (if n.factorization q = l then (1 : α) else 0)) =
      ((N / (p ^ k * q ^ l) : ℕ) : α) - ((N / (p ^ k * q ^ (l + 1)) : ℕ) : α) -
        ((N / (p ^ (k + 1) * q ^ l) : ℕ) : α) +
          ((N / (p ^ (k + 1) * q ^ (l + 1)) : ℕ) : α) := by
    simp_rw [hboole]
    exact sum_Icc_ite_factorization_eq_and_eq N hp hq hpq k l
  set r : ℕ → α := fun d ↦ (N : α) / (d : α) - ((N / d : ℕ) : α)
  have hr0 : ∀ d, 0 ≤ r d := fun _ ↦ sub_nonneg.mpr Nat.cast_div_le
  have hr1 : ∀ d, r d < 1 := fun d ↦ Nat.div_sub_cast_div_lt_one N d
  have hdiff : (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
        (if n.factorization q = l then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)) *
        (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)) =
      (r (p ^ k * q ^ (l + 1)) - r (p ^ k * q ^ l)) +
        (r (p ^ (k + 1) * q ^ l) - r (p ^ (k + 1) * q ^ (l + 1))) := by
    simp only [hsum, r, Nat.cast_mul, Nat.cast_pow]; ring
  rw [hdiff, abs_lt]
  constructor
  · linarith [hr0 (p ^ k * q ^ (l + 1)), hr1 (p ^ k * q ^ l),
      hr0 (p ^ (k + 1) * q ^ l), hr1 (p ^ (k + 1) * q ^ (l + 1))]
  · linarith [hr1 (p ^ k * q ^ (l + 1)), hr0 (p ^ k * q ^ l),
      hr1 (p ^ (k + 1) * q ^ l), hr0 (p ^ (k + 1) * q ^ (l + 1))]

/-- Helper for `Nat.abs_sum_Icc_ite_factorization_sub_mul_sub_lt_three`: the `k = 0` case, where
`1 - (1 - 1 / p) = 1 / p` cancels the `q`-only remainder term. -/
private lemma abs_sum_Icc_ite_factorization_zero_sub_mul_sub_lt_three {α : Type*} [Field α]
    [LinearOrder α] [IsStrictOrderedRing α] (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (l : ℕ) :
    |∑ n ∈ Finset.Icc 1 N,
        ((if n.factorization p = 0 then (1 : α) else 0) -
          (1 / (p : α) ^ 0 - 1 / (p : α) ^ (0 + 1))) *
        ((if n.factorization q = l then (1 : α) else 0) -
          (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)))| < 3 := by
  set dq : α := 1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)
  set r : ℕ → α := fun d ↦ (N : α) / (d : α) - ((N / d : ℕ) : α)
  have hr0 : ∀ d, 0 ≤ r d := fun _ ↦ sub_nonneg.mpr Nat.cast_div_le
  have hr1 : ∀ d, r d < 1 := fun d ↦ Nat.div_sub_cast_div_lt_one N d
  have hboole : ∀ n : ℕ, (if n.factorization p = 0 then (1 : α) else 0) *
      (if n.factorization q = l then (1 : α) else 0) =
      if n.factorization p = 0 ∧ n.factorization q = l then (1 : α) else 0 := fun _ ↦ by
    split_ifs <;> simp_all
  have hval : ∑ n ∈ Finset.Icc 1 N,
      ((if n.factorization p = 0 then (1 : α) else 0) -
        (1 / (p : α) ^ 0 - 1 / (p : α) ^ (0 + 1))) *
      ((if n.factorization q = l then (1 : α) else 0) - dq) =
      1 / (p : α) * (r (q ^ (l + 1)) - r (q ^ l)) +
        (r (p * q ^ l) - r (p * q ^ (l + 1))) - dq * r p := by
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, hboole]
    rw [sum_Icc_ite_factorization_eq_and_eq N hp hq hpq 0 l,
      sum_Icc_ite_factorization_eq N hp 0, sum_Icc_ite_factorization_eq N hq l]
    simp only [dq, r, pow_zero, one_mul, pow_one, Nat.div_one, Nat.cast_mul, Nat.cast_pow,
      zero_add, div_one]; ring
  have hp1 : (1 : α) ≤ p := Nat.one_le_cast.mpr hp.one_lt.le
  have hq1 : (1 : α) ≤ q := Nat.one_le_cast.mpr hq.one_lt.le
  have ht1 : |1 / (p : α) * (r (q ^ (l + 1)) - r (q ^ l))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (div_le_one_of_le₀ hp1 (by linarith))).trans
      (abs_le.mpr ⟨by linarith [hr0 (q ^ (l + 1)), hr1 (q ^ l)],
        by linarith [hr1 (q ^ (l + 1)), hr0 (q ^ l)]⟩)
  have hdq0 : 0 ≤ dq := sub_nonneg.mpr (one_div_le_one_div_of_le (pow_pos (by linarith) l)
    (pow_le_pow_right₀ hq1 (Nat.le_succ l)))
  have hdq1 : dq ≤ 1 := (sub_le_self _ (div_nonneg zero_le_one
    (pow_nonneg (by linarith) _))).trans (div_le_one_of_le₀ (one_le_pow₀ hq1)
      (pow_nonneg (by linarith) _))
  have hmul0 : 0 ≤ dq * r p := mul_nonneg hdq0 (hr0 p)
  have hmul1 : dq * r p < 1 := (mul_le_of_le_one_left (hr0 p) hdq1).trans_lt (hr1 p)
  rw [hval, abs_lt]
  rw [abs_le] at ht1
  exact ⟨by linarith [hr0 (p * q ^ l), hr1 (p * q ^ (l + 1))],
    by linarith [hr1 (p * q ^ l), hr0 (p * q ^ (l + 1))]⟩

/-- Centered valuation indicators at distinct primes `p ≠ q` have empirical correlation strictly
bounded by `3` over `Finset.Icc 1 N` in any linearly ordered field, for all `k, l : ℕ`. -/
theorem abs_sum_Icc_ite_factorization_sub_mul_sub_lt_three {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k l : ℕ) :
    |∑ n ∈ Finset.Icc 1 N,
        ((if n.factorization p = k then (1 : α) else 0) -
          (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1))) *
        ((if n.factorization q = l then (1 : α) else 0) -
          (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)))| < 3 := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact abs_sum_Icc_ite_factorization_zero_sub_mul_sub_lt_three N hp hq hpq l
  rcases eq_or_ne l 0 with rfl | hl
  · rw [Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    exact abs_sum_Icc_ite_factorization_zero_sub_mul_sub_lt_three N hq hp hpq.symm k
  -- Main case `k ≠ 0`, `l ≠ 0`: `dp, dq ≤ 1 / 2` gives `|E12 - dq * E1 - dp * E2| < 2 + 1/2 + 1/2`.
  have hdens {r m : ℕ} (hr : r.Prime) (hm : m ≠ 0) :
      (0 : α) ≤ 1 / (r : α) ^ m - 1 / (r : α) ^ (m + 1) ∧
        1 / (r : α) ^ m - 1 / (r : α) ^ (m + 1) ≤ 1 / 2 := by
    have hr1 : (1 : α) ≤ r := Nat.one_le_cast.mpr hr.one_lt.le
    have hr2 : (2 : α) ≤ r := by exact_mod_cast hr.two_le
    exact ⟨sub_nonneg.mpr (one_div_le_one_div_of_le (pow_pos (by linarith) m)
        (pow_le_pow_right₀ hr1 (Nat.le_succ m))),
      (sub_le_self _ (div_nonneg zero_le_one (pow_nonneg (by linarith) _))).trans
        (one_div_le_one_div_of_le zero_lt_two (hr2.trans (le_self_pow₀ hr1 hm)))⟩
  set dp : α := 1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)
  set dq : α := 1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)
  obtain ⟨hdp0, hdp⟩ := hdens hp hk
  obtain ⟨hdq0, hdq⟩ := hdens hq hl
  have hJ := abs_sum_Icc_ite_factorization_mul_sub_lt_two (α := α) N hp hq hpq k l
  have hCp := abs_sum_Icc_ite_factorization_sub_lt_one (α := α) N hp k
  have hCq := abs_sum_Icc_ite_factorization_sub_lt_one (α := α) N hq l
  set E12 := (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
      (if n.factorization q = l then (1 : α) else 0)) - (N : α) * dp * dq
  set E1 := (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0)) - (N : α) * dp
  set E2 := (∑ n ∈ Finset.Icc 1 N, (if n.factorization q = l then (1 : α) else 0)) - (N : α) * dq
  have hid : ∑ n ∈ Finset.Icc 1 N,
      ((if n.factorization p = k then (1 : α) else 0) - dp) *
      ((if n.factorization q = l then (1 : α) else 0) - dq) =
      E12 - dq * E1 - dp * E2 := by
    simp_rw [E12, E1, E2, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    ring
  rw [hid]
  have h1 := abs_sub (E12 - dq * E1) (dp * E2)
  have h2 := abs_sub E12 (dq * E1)
  rw [abs_mul, abs_of_nonneg hdp0] at h1
  rw [abs_mul, abs_of_nonneg hdq0] at h2
  have hm1 : dq * |E1| ≤ 1 / 2 := (mul_le_of_le_one_right hdq0 hCp.le).trans hdq
  have hm2 : dp * |E2| ≤ 1 / 2 := (mul_le_of_le_one_right hdp0 hCq.le).trans hdp
  linarith

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
