/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.PrimitivePrimeDivisors.Order
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Homogeneous
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Estimates
import TauCeti.NumberTheory.PrimitivePrimeDivisors.SmallExponents
import TauCeti.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# The Bang–Zsigmondy theorem and its multiplicative-order corollaries

For coprime natural numbers `0 < b < a` and an exponent `n ≥ 2`, a primitive prime divisor of
`a ^ n - b ^ n` is a prime dividing `a ^ n - b ^ n` and none of the earlier differences
`a ^ k - b ^ k` (`0 < k < n`). The Bang–Zsigmondy theorem states that such a prime exists except
in two cases: `n = 2` with `a + b` a power of two, and `(a, b, n) = (2, 1, 6)`.

Behind the existence theorem is a sharp lower bound on homogeneous cyclotomic values: for any
natural bases `0 < b < a` and `n ≠ 0`, every prime factor `p` of `n` satisfies
`p < Φ_n(a, b)` except at `(p, a, b, n) = (3, 2, 1, 6)`, where `Φ_6(2, 1) = 3`. Combining the
existence theorem with the nonexistence results at `n = 2` and `(2, 1, 6)` yields the exact
characterization `TauCeti.exists_prime_dvd_pow_sub_pow_iff`, together with its reformulations in
terms of `orderOf` in `ZMod p` (including Bang's base-two theorem) and primitive prime divisors of
sums of powers `a ^ n + b ^ n`.

## Main results

* `TauCeti.exists_prime_dvd_pow_sub_pow`, `TauCeti.exists_prime_dvd_pow_sub_pow_iff`: the
  Bang–Zsigmondy theorem and the exact characterization of when `a ^ n - b ^ n` has a primitive
  prime divisor.
* `Nat.Prime.lt_homogeneousCyclotomic_iff`,
  `TauCeti.forall_prime_dvd_lt_homogeneousCyclotomic_iff`: for `0 < b < a` and `n ≠ 0`, every
  prime divisor of `n` is strictly smaller than `Φ_n(a, b)` except `3` at `(a, b, n) = (2, 1, 6)`.
* `TauCeti.exists_prime_orderOf_div_eq`, `TauCeti.exists_prime_orderOf_div_eq_iff`: existence and
  characterization of primes `p ∤ a * b` modulo which `a / b` has multiplicative order `n`.
* `TauCeti.exists_prime_orderOf_eq_iff`, `TauCeti.exists_prime_orderOf_eq`,
  `TauCeti.exists_prime_orderOf_two_eq`: the base-one specializations for `orderOf (a : ZMod p)`.
* `TauCeti.exists_prime_dvd_pow_add_pow`, `TauCeti.exists_prime_dvd_pow_add_pow_iff`: existence
  and characterization of primes dividing `a ^ n + b ^ n` and no `a ^ k - b ^ k` with
  `0 < k < 2 * n`.

## References

* A. S. Bang, *Taltheoretiske Undersøgelser*, Tidsskr. Math. (5) 4 (1886), 70–80 and 130–137.
* K. Zsigmondy, *Zur Theorie der Potenzreste*, Monatsh. Math. Phys. 3 (1892), 265–284, p. 283.
* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*, Ann. of Math.
  (2) 5 (1904), 173–180, Theorem V, pp. 178–179.
* M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919, Lemma 1,
  Proposition 2, and Theorem 3.
* Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023), p. 1.
-/

public section

open TauCeti

/-! ### Cyclotomic estimates and the Bang–Zsigmondy theorem -/

private theorem le_two_pow_totient_of_prime_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : n ≠ 0) : p ≤ 2 ^ n.totient := by
  have hφ : p - 1 ≤ n.totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.le_of_dvd (Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)) (Nat.totient_dvd_of_dvd hpn)
  exact le_trans (by have := (p - 1).lt_two_pow_self; have := hp.one_le; omega)
    (Nat.pow_le_pow_right two_pos hφ)

private theorem two_pow_totient_lt_homogeneousCyclotomic {a b n : ℕ} (hb : 0 < b)
    (hba : b + 2 ≤ a) (hn : 2 ≤ n) :
    (2 : ℤ) ^ n.totient < homogeneousCyclotomic n (a : ℤ) b :=
  lt_of_le_of_lt (pow_le_pow_left₀ (by norm_num) (by omega) _)
    (Int.sub_pow_totient_lt_homogeneousCyclotomic hn (by exact_mod_cast hb)
      (by exact_mod_cast (by omega : b < a)))

private theorem lt_homogeneousCyclotomic_of_sq_dvd {p a b n : ℕ} (hp : p.Prime)
    (hp2 : p ^ 2 ∣ n) (hb : 0 < b) (hba : b < a) (hn : n ≠ 0) :
    (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b := by
  -- Trading `p ^ (e - 1)` (`e ≥ 2`) into the bases separates them by at least `2`.
  set e := n.factorization p
  set m := ordCompl[p] n
  have hdecomp : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have he2 : 2 ≤ e := (hp.pow_dvd_iff_le_factorization hn).1 hp2
  obtain ⟨d, hed⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
  have hΦ : homogeneousCyclotomic n (a : ℤ) b =
      homogeneousCyclotomic (p * m) ((a ^ p ^ (d + 1) : ℕ) : ℤ) ((b ^ p ^ (d + 1) : ℕ) : ℤ) := by
    rw [← hdecomp, hed, homogeneousCyclotomic_prime_pow_mul hp (d + 1) m]
    push_cast
    rfl
  set k := p ^ (d + 1)
  have hk2 : 2 ≤ k := le_trans hp.two_le (Nat.le_self_pow (Nat.succ_ne_zero d) p)
  have ha2 : 2 ≤ a ^ (k - 1) := le_trans (by omega : 2 ≤ a) (Nat.le_self_pow (by omega) a)
  have hbk : b ^ k + 2 ≤ a ^ k := calc
    b ^ k + 2 = b ^ (k - 1) * b + 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    _ ≤ a ^ (k - 1) * b + a ^ (k - 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right b (Nat.pow_le_pow_left hba.le _)) ha2
    _ = a ^ (k - 1) * (b + 1) := by ring
    _ ≤ a ^ (k - 1) * a := Nat.mul_le_mul_left _ hba
    _ = a ^ k := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hpm0 : p * m ≠ 0 := mul_ne_zero hp.ne_zero (Nat.ordCompl_pos p hn).ne'
  rw [hΦ]
  exact lt_of_le_of_lt
    (by exact_mod_cast le_two_pow_totient_of_prime_dvd hp (dvd_mul_right p m) hpm0)
    (two_pow_totient_lt_homogeneousCyclotomic (pow_pos hb _) hbk
      (le_trans hp.two_le (Nat.le_mul_of_pos_right p (Nat.ordCompl_pos p hn))))

namespace TauCeti

/-- **The Bang–Zsigmondy theorem.** For coprime natural numbers `0 < b < a` and `2 ≤ n`, the
difference `a ^ n - b ^ n` has a primitive prime divisor unless `n = 2` and `a + b` is a power of
two, or `(a, b, n) = (2, 1, 6)`. -/
theorem exists_prime_dvd_pow_sub_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬ ∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k := by
  rcases eq_or_ne n 2 with rfl | hn2
  · exact (exists_prime_dvd_sq_sub_sq_iff hba.le hab).2 (h₂ rfl)
  by_contra hno
  -- Without a primitive prime divisor, `Φ_n(a, b)` is `1` or the largest prime factor `p` of `n`.
  rcases hab.homogeneousCyclotomic_eq_one_or_eq_prime_of_not_exists_prime_dvd_pow_sub_pow hba hn2
      hno with h1 | ⟨p, hp, hpn, -, hpΦ⟩
  · have hlt := Int.sub_pow_totient_lt_homogeneousCyclotomic hn (a := a) (b := b)
      (by exact_mod_cast hb) (by exact_mod_cast hba)
    have hge : (1 : ℤ) ≤ ((a : ℤ) - b) ^ n.totient := one_le_pow₀ (by omega)
    omega
  · have hn0 : n ≠ 0 := by omega
    suffices hlt : (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b by omega
    by_cases hp2 : p ^ 2 ∣ n
    · exact lt_homogeneousCyclotomic_of_sq_dvd hp hp2 hb hba hn0
    have he : n.factorization p = 1 := by
      have := hp.factorization_pos_of_dvd hn0 hpn
      have := mt (hp.pow_dvd_iff_le_factorization hn0).2 hp2
      omega
    set m := ordCompl[p] n
    have hdecomp : p ^ n.factorization p * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hpm_eq : p * m = n := by simpa [he] using hdecomp
    rcases eq_or_ne m 1 with hm1 | hm1
    · rw [← hpm_eq, hm1, mul_one]
      exact natCast_lt_homogeneousCyclotomic_prime hp (by exact_mod_cast (by omega : 1 < a))
        (by exact_mod_cast hb)
    · have hm0 : 0 < m := Nat.ordCompl_pos p hn0
      have hdvd : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b := ⟨1, by rw [hpΦ, mul_one]⟩
      have hpb : ¬(p : ℤ) ∣ (b : ℤ) := fun h =>
        hab.not_dvd_mul_of_dvd_homogeneousCyclotomic hp hdvd
          (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.1 h) a)
      have hord : m ∣ p - 1 := hp.ordCompl_dvd_sub_one_of_dvd_homogeneousCyclotomic hpb hdvd
      have hp3 : 3 ≤ p := by
        have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hord
        omega
      have hex : ¬(a = 2 ∧ b = 1 ∧ p = 3) := by
        rintro ⟨rfl, rfl, rfl⟩
        have hm2 : m ≤ 2 := Nat.le_of_dvd two_pos hord
        rcases h₆ (by omega) with h | h <;> exact h rfl
      have hreal : ((p : ℤ) : ℝ) < ((homogeneousCyclotomic (p * m) (a : ℤ) b : ℤ) : ℝ) := by
        rw [Int.cast_homogeneousCyclotomic]
        push_cast
        exact (lt_pow_sub_pow_div_add_pow hb hba hp3 hex (Nat.totient_pos.2 hm0)).trans
          (pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic hp
            (Nat.not_dvd_ordCompl hp hn0) (by exact_mod_cast hb) (by exact_mod_cast hba))
      rw [← hpm_eq]
      exact Int.cast_lt.1 hreal

/-- **Exact characterization of primitive prime divisors.** For coprime natural numbers
`0 < b < a` and `2 ≤ n`, `a ^ n - b ^ n` has a primitive prime divisor if and only if neither
`n = 2` with `a + b` a power of two nor `(a, b, n) = (2, 1, 6)` holds. -/
theorem exists_prime_dvd_pow_sub_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ (n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬ (a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, hk⟩
      exact (exists_prime_dvd_sq_sub_sq_iff hba.le hab).1 h hk
    · rintro ⟨rfl, rfl, rfl⟩
      exact not_exists_prime_dvd_two_pow_six_sub_one_pow_six h
  · rintro ⟨h₂, h₆⟩
    exact exists_prime_dvd_pow_sub_pow hb hba hab hn (fun hn2 hk => h₂ ⟨hn2, hk⟩)
      (fun hn6 => by by_contra!; exact h₆ ⟨this.1, this.2, hn6⟩)

end TauCeti

/-- For natural bases `0 < b < a`, `n ≠ 0`, and a prime `p ∣ n`, the homogeneous cyclotomic value
`Φ_n(a, b)` strictly exceeds `p` if and only if `(p, a, b, n) ≠ (3, 2, 1, 6)`, where
`Φ_6(2, 1) = 3`. Coprimality of `a` and `b` is not needed. -/
theorem Nat.Prime.lt_homogeneousCyclotomic_iff {p a b n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hb : 0 < b) (hba : b < a) (hn : n ≠ 0) :
    (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b ↔ ¬(p = 3 ∧ a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl, rfl⟩
    rw [homogeneousCyclotomic_six] at h
    norm_num at h
  · intro h₆
    rcases eq_or_ne n 1 with rfl | hn1
    · exact absurd hpn hp.not_dvd_one
    rcases eq_or_ne n 2 with rfl | hn2
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpn
      rw [homogeneousCyclotomic_two]
      omega
    by_cases h₆' : a = 2 ∧ b = 1 ∧ n = 6
    · obtain ⟨rfl, rfl, rfl⟩ := h₆'
      have hp6 : p ∣ 2 * 3 := hpn
      rcases hp.dvd_mul.1 hp6 with hp2 | hp3
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2
        rw [homogeneousCyclotomic_six]
        norm_num
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hp3
        exact absurd ⟨rfl, rfl, rfl, rfl⟩ h₆
    rcases le_or_gt (b + 2) a with hba2 | hba1
    · exact lt_of_le_of_lt (by exact_mod_cast le_two_pow_totient_of_prime_dvd hp hpn hn)
        (two_pow_totient_lt_homogeneousCyclotomic hb hba2 (by omega))
    · -- Consecutive bases `a = b + 1` are coprime, so a primitive prime divisor `r > n ≥ p`
      -- divides the positive integer `Φ_n(a, b)`.
      have hab : a.Coprime b := by
        obtain rfl : a = b + 1 := by omega
        simp
      obtain ⟨r, hr, hrdvd, hrprev⟩ := exists_prime_dvd_pow_sub_pow hb hba hab (by omega)
        (fun h => absurd h hn2) (fun hn6 => by by_contra!; exact h₆' ⟨this.1, this.2, hn6⟩)
      have hrΦ : (r : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b :=
        ((hr.primitive_divisor_iff_dvd_homogeneousCyclotomic hab hba.le (by omega)).1
          ⟨hrdvd, hrprev⟩).1
      have hrlt : n < r := hr.exponent_lt_of_primitive hrdvd hrprev
      have hpn_le : p ≤ n := Nat.le_of_dvd (by omega) hpn
      have hpos : 0 < homogeneousCyclotomic n (a : ℤ) b :=
        homogeneousCyclotomic_pos (Int.natCast_nonneg b) (by exact_mod_cast hba) n
      have hrle : (r : ℤ) ≤ homogeneousCyclotomic n (a : ℤ) b := Int.le_of_dvd hpos hrΦ
      omega

namespace TauCeti

/-- For natural bases `0 < b < a` and `n ≠ 0`, `Φ_n(a, b)` strictly exceeds every prime divisor of
`n` if and only if `(a, b, n) ≠ (2, 1, 6)`. -/
theorem forall_prime_dvd_lt_homogeneousCyclotomic_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hn : n ≠ 0) :
    (∀ p : ℕ, p.Prime → p ∣ n → (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b) ↔
      ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl⟩
    have h3 := h 3 Nat.prime_three (by decide)
    rw [homogeneousCyclotomic_six] at h3
    norm_num at h3
  · intro h₆ p hp hpn
    exact (hp.lt_homogeneousCyclotomic_iff hpn hb hba hn).2
      fun ⟨_, ha, hb', hn'⟩ => h₆ ⟨ha, hb', hn'⟩

/-! ### Multiplicative-order and sum-of-powers corollaries -/

/-- For coprime natural numbers `0 < b < a` and `2 ≤ n`, there is a prime `p` not dividing `a * b`
modulo which `a / b` has multiplicative order `n` if and only if neither `n = 2` with `a + b` a
power of two nor `(a, b, n) = (2, 1, 6)` holds. The inverse is `ZMod.inv`. -/
theorem exists_prime_orderOf_div_eq_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n) ↔
      ¬ (n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬ (a = 2 ∧ b = 1 ∧ n = 6) := by
  rw [← exists_prime_dvd_pow_sub_pow_iff hb hba hab hn]
  exact exists_congr fun p => and_congr_right fun hp =>
    (hp.primitive_divisor_iff_orderOf_eq hab hba.le (by omega)).symm

/-- **Two-variable order form of the Bang–Zsigmondy theorem.** Outside the two exceptional cases,
there is a prime `p` not dividing `a * b` at which `a / b` has multiplicative order `n` in
`ZMod p`. -/
theorem exists_prime_orderOf_div_eq {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬ ∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n :=
  (exists_prime_orderOf_div_eq_iff hb hba hab hn).2
    ⟨fun ⟨hn2, hk⟩ => h₂ hn2 hk, fun ⟨ha, hb', hn6⟩ => (h₆ hn6).elim (· ha) (· hb')⟩

/-- For `2 ≤ a` and `2 ≤ n`, there is a prime `p` at which `a` has multiplicative order `n` in
`ZMod p` if and only if neither `n = 2` with `a + 1` a power of two nor `(a, n) = (2, 6)` holds.
Nondivisibility `¬ p ∣ a` is automatic since `orderOf 0 = 0 < n`. -/
theorem exists_prime_orderOf_eq_iff {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n) ↔
      ¬ (n = 2 ∧ ∃ k : ℕ, a + 1 = 2 ^ k) ∧ ¬ (a = 2 ∧ n = 6) := by
  have h1 := exists_prime_orderOf_div_eq_iff one_pos ha (Nat.coprime_one_right a) hn
  simp only [mul_one, true_and] at h1
  rw [← h1]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  have := Fact.mk hp
  simp only [Nat.cast_one, inv_one, mul_one]
  exact ⟨fun hord => ⟨fun hpa => by
    rw [(ZMod.natCast_eq_zero_iff a p).2 hpa, orderOf_zero] at hord; omega, hord⟩, And.right⟩

/-- For `3 ≤ a` and `3 ≤ n`, there is a prime `p` at which `a` has multiplicative order `n` in
`ZMod p`. Both `3 ≤ a` and `3 ≤ n` are needed, because `(a, n) = (2, 6)` and `(a, n) = (3, 2)`
have no such prime. -/
theorem exists_prime_orderOf_eq {a n : ℕ} (ha : 3 ≤ a) (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n :=
  (exists_prime_orderOf_eq_iff (by omega) (by omega)).2 ⟨by omega, by omega⟩

/-- **Bang's theorem.** For `2 ≤ n` with `n ≠ 6`, there is a prime `p` at which `2` has
multiplicative order `n` in `ZMod p`. -/
theorem exists_prime_orderOf_two_eq {n : ℕ} (hn : 2 ≤ n) (h₆ : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = n := by
  refine (exists_prime_orderOf_eq_iff le_rfl hn).2 ⟨?_, fun ⟨_, h⟩ => h₆ h⟩
  rintro ⟨-, (_ | _ | k), hk⟩ <;> simp [pow_succ] at hk
  omega

/-- For coprime natural numbers `0 < b < a` and any `n : ℕ`, there is a prime dividing
`a ^ n + b ^ n` and no `a ^ k - b ^ k` with `0 < k < 2 * n` if and only if neither `n = 1` with
`a + b` a power of two nor `(a, b, n) = (2, 1, 3)` holds. At `n = 0`, `a ^ 0 + b ^ 0 = 2` is
divisible by `2` and the range `0 < k < 0` is empty. -/
theorem exists_prime_dvd_pow_add_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ (n = 1 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬ (a = 2 ∧ b = 1 ∧ n = 3) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · refine ⟨fun _ => by simp, fun _ => ⟨2, Nat.prime_two, by simp, fun k hk hk0 => by omega⟩⟩
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hcongr : (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
        ∀ k : ℕ, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k) ↔
      ∃ p : ℕ, p.Prime ∧ p ∣ a ^ (2 * n) - b ^ (2 * n) ∧
        ∀ k : ℕ, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k :=
    exists_congr fun p => and_congr_right fun hp => hp.dvd_pow_add_pow_and_not_dvd_iff hn_pos
  rw [hcongr, exists_prime_dvd_pow_sub_pow_iff hb hba hab (by omega)]
  exact ⟨fun ⟨h₂, h₆⟩ => ⟨fun ⟨hn1, hk⟩ => h₂ ⟨congrArg (2 * ·) hn1, hk⟩,
      fun ⟨ha, hb', hn3⟩ => h₆ ⟨ha, hb', congrArg (2 * ·) hn3⟩⟩,
    fun ⟨h₁, h₃⟩ => ⟨fun ⟨h2n, hk⟩ => h₁ ⟨Nat.mul_left_cancel two_pos h2n, hk⟩,
      fun ⟨ha, hb', h2n⟩ => h₃ ⟨ha, hb', Nat.mul_left_cancel two_pos h2n⟩⟩⟩

/-- **Primitive prime divisors of `a ^ n + b ^ n`.** For coprime natural numbers `0 < b < a` and
any `n : ℕ`, unless `n = 1` with `a + b` a power of two or `(a, b, n) = (2, 1, 3)`, there is a
prime dividing `a ^ n + b ^ n` and no `a ^ k - b ^ k` with `0 < k < 2 * n`. -/
theorem exists_prime_dvd_pow_add_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b)
    (h₁ : n = 1 → ¬ ∃ k : ℕ, a + b = 2 ^ k)
    (h₃ : n = 3 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k :=
  (exists_prime_dvd_pow_add_pow_iff hb hba hab).2
    ⟨fun ⟨hn1, hk⟩ => h₁ hn1 hk, fun ⟨ha, hb', hn3⟩ => (h₃ hn3).elim (· ha) (· hb')⟩

end TauCeti
