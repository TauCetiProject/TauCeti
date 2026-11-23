/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SmoothNumbers

/-!
# `P`-numbers

For a set `P` of natural numbers, a natural number `n` is a `P`-number when it is positive and
every prime divisor of `n` lies in `P` (Temkin, *Tame distillation and desingularization by
`p`-alterations*, Annals of Mathematics 186 (2017), §2.1.1). The set `P` may be infinite, as the
set of all primes is, and only its primes matter. For a finite set `s` the `s`-numbers are
Mathlib's `Nat.factoredNumbers s`.

`P`-numbers are the degrees allowed in a `P`-extension of fields (`TauCeti.IsPExtension`), the
notion in which Temkin's tameness theorem for `p`-closed valued fields is stated.

## Main definitions and results

* `TauCeti.IsPNumber P n`: `n` is positive and all its prime divisors lie in `P`;
* `TauCeti.isPNumber_mul_iff`: a product is a `P`-number exactly when both factors are;
* `TauCeti.isPNumber_pow_iff`: a power `n ^ k` is a `P`-number exactly when `k = 0` or `n` is;
* `TauCeti.IsPNumber.of_dvd`: divisors of `P`-numbers are `P`-numbers;
* `TauCeti.isPNumber_singleton_iff`: for a prime `p`, the `{p}`-numbers are the powers of `p`;
* `TauCeti.isPNumber_inter_setOf_prime_iff`: only the primes of `P` matter;
* `TauCeti.isPNumber_coe_finset_iff`: for a finset `s`, the `s`-numbers are
  `Nat.factoredNumbers s`.
-/

public section

namespace TauCeti

/-- A natural number `n` is a `P`-number, for a set `P` of natural numbers, when it is positive
and every prime divisor of `n` lies in `P`. Zero is never a `P`-number, and for `P = ∅` the only
`P`-number is `1`. -/
def IsPNumber (P : Set ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ∈ P

variable {P Q : Set ℕ} {a b n : ℕ}

theorem isPNumber_iff : IsPNumber P n ↔ 0 < n ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ∈ P :=
  Iff.rfl

theorem IsPNumber.pos (h : IsPNumber P n) : 0 < n :=
  h.1

theorem IsPNumber.ne_zero (h : IsPNumber P n) : n ≠ 0 :=
  h.pos.ne'

theorem IsPNumber.mem_of_prime_of_dvd (h : IsPNumber P n) {q : ℕ} (hq : q.Prime) (hqn : q ∣ n) :
    q ∈ P :=
  h.2 q hq hqn

/-- Zero is not a `P`-number, even when `P` contains every prime. -/
@[simp]
theorem not_isPNumber_zero : ¬IsPNumber P 0 :=
  fun h ↦ h.ne_zero rfl

/-- One is a `P`-number for every `P`. -/
@[simp]
theorem isPNumber_one : IsPNumber P 1 :=
  ⟨Nat.one_pos, fun _ hq hq1 ↦ absurd (Nat.eq_one_of_dvd_one hq1) hq.ne_one⟩

theorem isPNumber_iff_primeFactors_subset : IsPNumber P n ↔ n ≠ 0 ∧ ↑n.primeFactors ⊆ P := by
  refine ⟨fun h ↦ ⟨h.ne_zero, fun q hq ↦ ?_⟩, fun ⟨hn, h⟩ ↦ ⟨Nat.pos_of_ne_zero hn, fun q hq hqn ↦
    h (Nat.mem_primeFactors.2 ⟨hq, hqn, hn⟩)⟩⟩
  obtain ⟨hq, hqn, -⟩ := Nat.mem_primeFactors.1 hq
  exact h.mem_of_prime_of_dvd hq hqn

/-- A divisor of a `P`-number is a `P`-number. -/
theorem IsPNumber.of_dvd (h : IsPNumber P n) (ha : a ∣ n) : IsPNumber P a :=
  ⟨Nat.pos_of_dvd_of_pos ha h.pos, fun _ hq hqa ↦ h.mem_of_prime_of_dvd hq (hqa.trans ha)⟩

theorem IsPNumber.mul (ha : IsPNumber P a) (hb : IsPNumber P b) : IsPNumber P (a * b) :=
  ⟨Nat.mul_pos ha.pos hb.pos, fun _ hq hqab ↦ (hq.dvd_mul.1 hqab).elim
    (ha.mem_of_prime_of_dvd hq) (hb.mem_of_prime_of_dvd hq)⟩

/-- A product is a `P`-number exactly when both factors are. No positivity hypothesis is needed:
if a factor is zero, both sides fail. -/
@[simp]
theorem isPNumber_mul_iff : IsPNumber P (a * b) ↔ IsPNumber P a ∧ IsPNumber P b :=
  ⟨fun h ↦ ⟨h.of_dvd (dvd_mul_right a b), h.of_dvd (dvd_mul_left b a)⟩, fun h ↦ h.1.mul h.2⟩

/-- A power `n ^ k` is a `P`-number exactly when `k = 0` or `n` is a `P`-number. -/
@[simp]
theorem isPNumber_pow_iff {k : ℕ} : IsPNumber P (n ^ k) ↔ k = 0 ∨ IsPNumber P n := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hk ↦ h.of_dvd (dvd_pow_self n hk), ?_⟩
  rintro (rfl | h)
  · simp
  · induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; exact ih.mul h

theorem IsPNumber.pow (h : IsPNumber P n) (k : ℕ) : IsPNumber P (n ^ k) :=
  isPNumber_pow_iff.2 (.inr h)

/-- Enlarging `P` preserves `P`-numbers. -/
theorem IsPNumber.mono (hPQ : P ⊆ Q) (h : IsPNumber P n) : IsPNumber Q n :=
  ⟨h.pos, fun _ hq hqn ↦ hPQ (h.mem_of_prime_of_dvd hq hqn)⟩

/-- A prime `q` is a `P`-number exactly when it lies in `P`. -/
@[simp]
theorem isPNumber_prime_iff {q : ℕ} (hq : q.Prime) : IsPNumber P q ↔ q ∈ P :=
  ⟨fun h ↦ h.mem_of_prime_of_dvd hq dvd_rfl, fun h ↦ ⟨hq.pos, fun _ hr hrq ↦
    ((Nat.prime_dvd_prime_iff_eq hr hq).1 hrq) ▸ h⟩⟩

/-- Only the primes of `P` matter: `n` is a `P`-number exactly when it is a
`(P ∩ primes)`-number. -/
@[simp]
theorem isPNumber_inter_setOf_prime_iff :
    IsPNumber (P ∩ {q | q.Prime}) n ↔ IsPNumber P n :=
  ⟨IsPNumber.mono Set.inter_subset_left, fun h ↦ ⟨h.pos, fun _ hq hqn ↦
    ⟨h.mem_of_prime_of_dvd hq hqn, hq⟩⟩⟩

/-- For `P = ∅` the only `P`-number is `1`. -/
@[simp]
theorem isPNumber_empty_iff : IsPNumber ∅ n ↔ n = 1 := by
  refine ⟨fun h ↦ Nat.eq_one_iff_not_exists_prime_dvd.2 fun q hq hqn ↦
    h.mem_of_prime_of_dvd hq hqn, ?_⟩
  rintro rfl
  exact isPNumber_one

/-- For a prime `p`, the `{p}`-numbers are exactly the powers of `p`. -/
theorem isPNumber_singleton_iff {p : ℕ} (hp : p.Prime) : IsPNumber {p} n ↔ ∃ r, n = p ^ r := by
  refine ⟨fun h ↦ ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd h.ne_zero fun hq hqn ↦
    h.mem_of_prime_of_dvd hq hqn⟩, ?_⟩
  rintro ⟨r, rfl⟩
  exact ((isPNumber_prime_iff hp).2 rfl).pow r

/-- For a finite set `s`, the `s`-numbers are Mathlib's `s`-factored numbers. -/
theorem isPNumber_coe_finset_iff {s : Finset ℕ} : IsPNumber ↑s n ↔ n ∈ Nat.factoredNumbers s := by
  rw [isPNumber_iff_primeFactors_subset, Nat.mem_factoredNumbers_iff_primeFactors_subset,
    Finset.coe_subset]

end TauCeti
