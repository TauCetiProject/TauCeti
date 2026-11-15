/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.MaxPrimeFac
public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Homogeneous
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Estimates
import TauCeti.NumberTheory.PrimitivePrimeDivisors.SmallExponents
import TauCeti.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# The Bang–Zsigmondy theorem and primes of prescribed multiplicative order

For coprime natural numbers `0 < b < a` and `2 ≤ n`, a **primitive prime divisor** of
`a ^ n - b ^ n` is a prime dividing `a ^ n - b ^ n` and none of the earlier differences
`a ^ k - b ^ k` with `0 < k < n`. The **Bang–Zsigmondy theorem** states that such a prime exists
except in two cases: `n = 2` with `a + b` a power of two, and `(a, b, n) = (2, 1, 6)`.

For `n ≥ 3`, if `a ^ n - b ^ n` had no primitive prime divisor, its `n`-th homogeneous cyclotomic
factor `Φ_n(a, b)` could have at most one prime divisor—the largest prime factor `p` of `n`—with
multiplicity one, while `(a - b) ^ φ(n) < Φ_n(a, b)` rules out `Φ_n(a, b) = 1`. Writing
`n = p ^ e m` with `p ∤ m`, the size bounds on `Φ_n(a, b)` force `p < Φ_n(a, b)` in every case
except `(a, b, n) = (2, 1, 6)`, where `Φ_6(2, 1) = 3`. Consequently `a ^ n - b ^ n` has a
primitive prime divisor `q` outside `(2, 1, 6)`; since `n < q` and `q ∣ Φ_n(a, b)`, it follows
for arbitrary (not necessarily coprime) bases `0 < b < a` and `n ≠ 1` that `n < Φ_n(a, b)` and
`n.maxPrimeFac < Φ_n(a, b)` outside `(a, b, n) = (2, 1, 6)`.

Because a prime is primitive for `a ^ n - b ^ n` exactly when it is prime to `a * b` and `a / b`
has multiplicative order `n` in `ZMod p`, the theorem characterizes when a prime of prescribed
multiplicative order exists for `a / b`, for an integer base `a ≥ 2` (`b = 1`), and in particular
for `a ≥ 3, n ≥ 3` (always) and `a = 2` (iff `n ≠ 1` and `n ≠ 6`). Applying the order-`2 n` case
yields the existence and exact exceptions of primes dividing `a ^ n + b ^ n` and no
`a ^ k - b ^ k` with `0 < k < 2 * n`.

## Main results

* `TauCeti.exists_prime_dvd_pow_sub_pow`, `TauCeti.exists_prime_dvd_pow_sub_pow_iff`:
  the Bang–Zsigmondy theorem and its exact equivalence characterization.
* `TauCeti.natCast_lt_homogeneousCyclotomic_iff`,
  `TauCeti.maxPrimeFac_lt_homogeneousCyclotomic_iff`,
  `Nat.Prime.lt_homogeneousCyclotomic_iff_of_dvd`: for `0 < b < a` and `n ≠ 1`,
  `n < Φ_n(a, b)` and `n.maxPrimeFac < Φ_n(a, b)` hold iff `(a, b, n) ≠ (2, 1, 6)`, and for a
  prime `p ∣ n` (`n ≠ 0`), `p < Φ_n(a, b)` holds iff `(a, b, n, p) ≠ (2, 1, 6, 3)`.
* `TauCeti.exists_prime_orderOf_div_eq`, `TauCeti.exists_prime_orderOf_div_eq_iff`:
  existence and characterization of primes at which `a / b` has order `n` in `ZMod p`.
* `TauCeti.exists_prime_orderOf_eq_iff`, `TauCeti.exists_prime_orderOf_eq`,
  `TauCeti.exists_prime_orderOf_two_eq_iff`, `TauCeti.exists_prime_orderOf_two_eq`:
  primes at which `a` (and `2`) has multiplicative order `n` in `ZMod p`.
* `TauCeti.exists_prime_dvd_pow_add_pow`, `TauCeti.exists_prime_dvd_pow_add_pow_iff`:
  primes dividing `a ^ n + b ^ n` and no `a ^ k - b ^ k` for `0 < k < 2 * n`.

## References

* [K. Zsigmondy, *Zur Theorie der Potenzreste*, Monatsh. Math. Phys. 3 (1892), 265–284], p. 283.
* [G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*,
  Ann. of Math. (2) 5 (1904), 173–180], Theorem V, pp. 178–179.
* [M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919],
  Lemma 1 and Theorem 3, pp. 1913–1915.
* [Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023)], p. 1.
-/

public section

namespace TauCeti

/-! ### Cyclotomic contradiction step and the Bang–Zsigmondy theorem -/

/-- For positive natural bases `0 < b < a` and `2 ≤ r`, `a ^ r - b ^ r ≥ 2`. -/
private theorem two_le_pow_sub_pow {a b r : ℕ} (hb : 0 < b) (hba : b < a) (hr : 2 ≤ r) :
    2 ≤ a ^ r - b ^ r := by
  have h1 : b ^ r < b ^ (r - 1) * a := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ r), pow_succ]
    exact Nat.mul_lt_mul_of_pos_left hba (pow_pos hb _)
  have h2 : b ^ (r - 1) * a < a ^ r := by
    conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ r), pow_succ]
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hba (by omega)) (hb.trans hba)
  omega

/-- When `a - b ≥ 2` and `n ≠ 0`, any prime `p ∣ n` satisfies
`p ≤ 2 ^ (p - 1) ≤ (a - b) ^ φ(n)`. -/
private theorem le_sub_pow_totient_of_dvd {p a b n : ℕ} (hp : p.Prime)
    (hsub : 2 ≤ a - b) (hn : n ≠ 0) (hpn : p ∣ n) :
    p ≤ (a - b) ^ n.totient := by
  have htot : p - 1 ≤ n.totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.le_of_dvd (Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)) (Nat.totient_dvd_of_dvd hpn)
  have hp2 : p ≤ 2 ^ (p - 1) := by
    have := (p - 1).lt_two_pow_self
    have := hp.pos
    omega
  exact hp2.trans ((Nat.pow_le_pow_right (by decide) htot).trans (Nat.pow_le_pow_left hsub _))

/-- **The Bang–Zsigmondy theorem.** For coprime natural numbers `0 < b < a` and `2 ≤ n`, the
difference `a ^ n - b ^ n` has a prime divisor dividing none of `a ^ k - b ^ k` for `0 < k < n`,
unless `n = 2` and `a + b` is a power of two, or `(a, b, n) = (2, 1, 6)`. -/
theorem exists_prime_dvd_pow_sub_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬ ∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k := by
  rcases eq_or_lt_of_le hn with rfl | hn3
  · exact (exists_prime_dvd_sq_sub_sq_iff hba.le hab).2 (h₂ rfl)
  by_contra hnot
  rcases hab.homogeneousCyclotomic_eq_one_or_eq_prime_of_not_exists_prime_dvd_pow_sub_pow hba
      (by omega) hnot with h1 | ⟨p, hp, hpn, -, hΦ⟩
  · have hgt := Int.sub_pow_totient_lt_homogeneousCyclotomic (a := a) (b := b) (by omega)
      (by positivity) (by exact_mod_cast hba)
    have hone : (1 : ℤ) ≤ ((a : ℤ) - b) ^ n.totient := one_le_pow₀ (by omega)
    omega
  have hdvd : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b := dvd_of_eq hΦ.symm
  set e := n.factorization p
  set m := ordCompl[p] n
  have hfact : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have he : 1 ≤ e := hp.factorization_pos_of_dvd (by omega) hpn
  have hpm : ¬p ∣ m := Nat.not_dvd_ordCompl hp (by omega)
  have hm_pos : 0 < m := Nat.ordCompl_pos p (by omega)
  -- In every `(e, m)` regime outside `(2, 1, 6)`, the size estimates give `p < Φ_n(a, b) = p`.
  suffices hlt : (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b by omega
  rcases eq_or_lt_of_le he with he1 | he2
  · have hnm : p * m = n := by rw [← hfact, ← he1, pow_one]
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hm_pos.ne') with hm1 | hm2
    · rw [← hnm, ← hm1, mul_one]
      exact natCast_lt_homogeneousCyclotomic_prime hp (by omega) (by omega)
    · have hpb : ¬(p : ℤ) ∣ (b : ℤ) := fun h =>
        hab.not_dvd_mul_of_dvd_homogeneousCyclotomic hp hdvd
          (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.1 h) a)
      have hmp : m ∣ p - 1 := hp.ordCompl_dvd_sub_one_of_dvd_homogeneousCyclotomic hpb hdvd
      have hp3 : 3 ≤ p := by have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hmp; omega
      have hexp : ¬ (a = 2 ∧ b = 1 ∧ p = 3) := by
        rintro ⟨rfl, rfl, rfl⟩
        have hm_le : m ≤ 2 := Nat.le_of_dvd (by decide) hmp
        rcases h₆ (by omega) with h | h <;> exact h rfl
      have hreal : (((p : ℤ) : ℝ)) < ((homogeneousCyclotomic (p * m) (a : ℤ) b : ℤ) : ℝ) := by
        simpa using (lt_pow_sub_pow_div_add_pow hb hba hp3 hexp (Nat.totient_pos.2 hm_pos)).trans
          (pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic hp hpm
            (by positivity) (by exact_mod_cast hba))
      exact hnm ▸ Int.cast_lt.1 hreal
  · set r := p ^ (e - 1)
    have hr : 2 ≤ r := hp.two_le.trans (Nat.le_self_pow (by omega : e - 1 ≠ 0) p)
    have hpow := le_sub_pow_totient_of_dvd hp (two_le_pow_sub_pow hb hba hr)
      (mul_ne_zero hp.ne_zero hm_pos.ne') (dvd_mul_right p m)
    have hn_eq : n = p ^ (e - 1 + 1) * m := by rw [Nat.sub_add_cancel he, hfact]
    rw [hn_eq, homogeneousCyclotomic_prime_pow_mul hp (e - 1) m]
    refine lt_of_le_of_lt ?_ (Int.sub_pow_totient_lt_homogeneousCyclotomic
      (hp.two_le.trans (Nat.le_mul_of_pos_right p hm_pos)) (by positivity)
      (by exact_mod_cast Nat.pow_lt_pow_left hba (by omega : r ≠ 0)))
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub (Nat.pow_le_pow_left hba.le r),
      ← Nat.cast_pow]
    exact Int.ofNat_le.2 hpow

/-- **Characterization of primitive prime divisors.** For coprime natural numbers `0 < b < a` and
`2 ≤ n`, `a ^ n - b ^ n` has a primitive prime divisor if and only if neither `n = 2` with `a + b`
a power of two nor `(a, b, n) = (2, 1, 6)` holds. -/
theorem exists_prime_dvd_pow_sub_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ (n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬ (a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, hk⟩
      exact (exists_prime_dvd_sq_sub_sq_iff hba.le hab).1 h hk
    · rintro ⟨rfl, rfl, rfl⟩
      exact not_exists_prime_dvd_two_pow_six_sub_one_pow_six h
  · rintro ⟨h₂, h₆⟩
    exact exists_prime_dvd_pow_sub_pow hb hba hab hn (fun hn2 hk => h₂ ⟨hn2, hk⟩)
      (fun hn6 => by by_contra! h; exact h₆ ⟨h.1, h.2, hn6⟩)

/-! ### Lower bounds on homogeneous cyclotomic values -/

/-- For natural bases `0 < b < a` and `n ≠ 1` (without assuming coprimality), the homogeneous
cyclotomic value `Φ_n(a, b)` exceeds `n` except at `(a, b, n) = (2, 1, 6)`, where
`Φ_6(2, 1) = 3`. At `n = 1` this fails for consecutive bases since `Φ_1(a, b) = a - b`. -/
theorem natCast_lt_homogeneousCyclotomic_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hn : n ≠ 1) :
    (n : ℤ) < homogeneousCyclotomic n (a : ℤ) b ↔ ¬ (a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl⟩
    rw [homogeneousCyclotomic_six] at h
    norm_num at h
  · intro hex
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rcases eq_or_lt_of_le (by omega : 2 ≤ n) with rfl | hn3
    · rw [homogeneousCyclotomic_two]
      omega
    -- Factor out `g = gcd(a, b)` using `Φ_n(g a', g b') = g ^ φ(n) Φ_n(a', b')`.
    set g := a.gcd b
    have hg : 0 < g := Nat.gcd_pos_of_pos_right a hb
    set a' := a / g
    set b' := b / g
    have ha : g * a' = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have hb_eq : g * b' = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have hb' : 0 < b' := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
    have hba' : b' < a' := lt_of_mul_lt_mul_left' (a := g) (by omega)
    have hab' : a'.Coprime b' := Nat.coprime_div_gcd_div_gcd hg
    rw [← ha, ← hb_eq, Nat.cast_mul, Nat.cast_mul, homogeneousCyclotomic_mul_mul]
    by_cases h216 : a' = 2 ∧ b' = 1 ∧ n = 6
    · obtain ⟨ha'2, hb'1, rfl⟩ := h216
      have hg2 : (2 : ℤ) ≤ g := by
        by_contra! hg1
        have hg_eq : g = 1 := by omega
        exact hex ⟨by rw [← ha, hg_eq, ha'2], by rw [← hb_eq, hg_eq, hb'1], rfl⟩
      have h6 : Nat.totient 6 = 2 := by decide
      rw [ha'2, hb'1, h6, homogeneousCyclotomic_six]
      norm_num
      nlinarith
    · obtain ⟨q, hq, hdvd, hprim⟩ := exists_prime_dvd_pow_sub_pow hb' hba' hab' hn3.le
        (by omega) (fun hn6 => by by_contra! h; exact h216 ⟨h.1, h.2, hn6⟩)
      have hnq : n < q := hq.exponent_lt_of_primitive hdvd hprim
      have hqΦ : (q : ℤ) ∣ homogeneousCyclotomic n (a' : ℤ) b' :=
        ((hq.primitive_divisor_iff_dvd_homogeneousCyclotomic hab' hba'.le (by omega)).1
          ⟨hdvd, hprim⟩).1
      have hpos := homogeneousCyclotomic_pos (Int.natCast_nonneg b') (Int.ofNat_lt.2 hba') n
      have hg_pow : (1 : ℤ) ≤ (g : ℤ) ^ n.totient := one_le_pow₀ (by omega)
      calc (n : ℤ) < q := by exact_mod_cast hnq
        _ ≤ homogeneousCyclotomic n (a' : ℤ) b' := Int.le_of_dvd hpos hqΦ
        _ ≤ (g : ℤ) ^ n.totient * homogeneousCyclotomic n (a' : ℤ) b' :=
          le_mul_of_one_le_left hpos.le hg_pow

/-- For natural bases `0 < b < a` and `n ≠ 1`, the homogeneous cyclotomic value `Φ_n(a, b)`
exceeds the greatest prime factor `n.maxPrimeFac` of `n` except at `(a, b, n) = (2, 1, 6)`,
where `Φ_6(2, 1) = 3 = 6.maxPrimeFac`. -/
theorem maxPrimeFac_lt_homogeneousCyclotomic_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hn : n ≠ 1) :
    (n.maxPrimeFac : ℤ) < homogeneousCyclotomic n (a : ℤ) b ↔ ¬ (a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl⟩
    have h6_eq : (6 : ℕ) = 2 * 3 := rfl
    have h6 : (6 : ℕ).maxPrimeFac = 3 := by
      rw [h6_eq, Nat.maxPrimeFac_mul (by decide) (by decide),
        Nat.Prime.maxPrimeFac_eq_self Nat.prime_two, Nat.Prime.maxPrimeFac_eq_self Nat.prime_three]
      decide
    rw [h6, homogeneousCyclotomic_six] at h
    norm_num at h
  · intro hex
    exact lt_of_le_of_lt (by exact_mod_cast Nat.maxPrimeFac_le)
      ((natCast_lt_homogeneousCyclotomic_iff hb hba hn).2 hex)

end TauCeti

/-- For natural bases `0 < b < a`, `n ≠ 0` and a prime `p ∣ n`, `p < Φ_n(a, b)` except at the
single quadruple `(a, b, n, p) = (2, 1, 6, 3)`, where `Φ_6(2, 1) = 3` (while `2 < Φ_6(2, 1)`
still holds at `p = 2`). -/
theorem Nat.Prime.lt_homogeneousCyclotomic_iff_of_dvd {p : ℕ} (hp : p.Prime)
    {a b n : ℕ} (hb : 0 < b) (hba : b < a) (hn : n ≠ 0) (hpn : p ∣ n) :
    (p : ℤ) < TauCeti.homogeneousCyclotomic n (a : ℤ) b ↔ ¬ (a = 2 ∧ b = 1 ∧ n = 6 ∧ p = 3) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl, rfl⟩
    rw [TauCeti.homogeneousCyclotomic_six] at h
    norm_num at h
  · intro hex
    have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn
    by_cases h216 : a = 2 ∧ b = 1 ∧ n = 6
    · obtain ⟨rfl, rfl, rfl⟩ := h216
      have h6_eq : (6 : ℕ) = 2 * 3 := rfl
      rw [h6_eq] at hpn
      have hp23 : p = 2 ∨ p = 3 := by
        rcases hp.dvd_mul.1 hpn with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
      rcases hp23 with rfl | rfl
      · rw [TauCeti.homogeneousCyclotomic_six]
        norm_num
      · exact absurd ⟨rfl, rfl, rfl, rfl⟩ hex
    · have hn2 : 2 ≤ n := hp.two_le.trans hple
      exact lt_of_le_of_lt (by exact_mod_cast hple)
        ((TauCeti.natCast_lt_homogeneousCyclotomic_iff hb hba (by omega)).2 h216)

namespace TauCeti

/-! ### Primes of prescribed multiplicative order -/

/-- For coprime natural numbers `0 < b < a` and `2 ≤ n`, there exists a prime `p` not dividing
`a * b` at which `a * b⁻¹` has multiplicative order `n` in `ZMod p` if and only if neither `n = 2`
with `a + b` a power of two nor `(a, b, n) = (2, 1, 6)` holds. For any such prime, `n ∣ p - 1`
(`Nat.Prime.orderOf_ratio_dvd_sub_one`) and `n < p` (`ZMod.orderOf_lt`). -/
theorem exists_prime_orderOf_div_eq_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n) ↔
      ¬ (n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬ (a = 2 ∧ b = 1 ∧ n = 6) := by
  rw [← exists_prime_dvd_pow_sub_pow_iff hb hba hab hn]
  exact exists_congr fun p => and_congr_right fun hp =>
    (hp.primitive_divisor_iff_orderOf_eq hab hba.le (by omega)).symm

/-- Outside the two Bang–Zsigmondy exceptions, for coprime `0 < b < a` and `2 ≤ n` there exists a
prime `p` not dividing `a * b` at which `a * b⁻¹` has multiplicative order `n` in `ZMod p`. -/
theorem exists_prime_orderOf_div_eq {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬ ∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n :=
  (exists_prime_orderOf_div_eq_iff hb hba hab hn).2
    ⟨fun ⟨hn2, hk⟩ => h₂ hn2 hk, fun ⟨ha, hb1, hn6⟩ => by
      rcases h₆ hn6 with h | h <;> [exact h ha; exact h hb1]⟩

/-- For `2 ≤ a` and `2 ≤ n`, there exists a prime `p` at which `a` has multiplicative order `n` in
`ZMod p` if and only if neither `n = 2` with `a + 1` a power of two nor `(a, n) = (2, 6)` holds. -/
theorem exists_prime_orderOf_eq_iff {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n) ↔
      ¬ (n = 2 ∧ ∃ k : ℕ, a + 1 = 2 ^ k) ∧ ¬ (a = 2 ∧ n = 6) := by
  have hiff := exists_prime_orderOf_div_eq_iff Nat.one_pos ha (Nat.coprime_one_right a) hn
  refine (exists_congr fun p => and_congr_right fun hp => ?_).trans (hiff.trans ?_)
  · have hcast : ((a : ZMod p) * ((1 : ℕ) : ZMod p)⁻¹) = (a : ZMod p) := by simp
    refine ⟨fun hord => ⟨?_, ?_⟩, fun h => ?_⟩
    · exact hp.orderOf_ratio_ne_zero_iff.mp (by rw [hcast, hord]; omega)
    · rwa [hcast]
    · rw [← hcast]
      exact h.2
  · simp only [true_and]

/-- For `3 ≤ a` and `3 ≤ n`, there exists a prime `p` at which `a` has multiplicative order `n`
in `ZMod p`. -/
theorem exists_prime_orderOf_eq {a n : ℕ} (ha : 3 ≤ a) (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n :=
  (exists_prime_orderOf_eq_iff (by omega) (by omega)).2 ⟨by omega, by omega⟩

/-- For any natural number `n`, there exists a prime `p` at which `2` has multiplicative order `n`
in `ZMod p` if and only if `n ≠ 1` and `n ≠ 6` (at `n = 0`, `p = 2` gives `0 : ZMod 2`). -/
theorem exists_prime_orderOf_two_eq_iff {n : ℕ} :
    (∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = n) ↔ n ≠ 1 ∧ n ≠ 6 := by
  rcases n with _ | _ | n
  · refine ⟨fun _ => by decide, fun _ => ⟨2, Nat.prime_two, ?_⟩⟩
    have : Fact (1 < 2) := ⟨by decide⟩
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, orderOf_zero]
  · refine ⟨?_, fun h => absurd rfl h.1⟩
    rintro ⟨p, hp, h1⟩
    let : Fact p.Prime := ⟨hp⟩
    have h21 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.1 h1
    have h10 : (1 : ZMod p) = 0 := by linear_combination h21
    exact absurd h10 one_ne_zero
  · have hiff := exists_prime_orderOf_eq_iff (a := 2) le_rfl (Nat.le_add_left 2 n)
    simp only [Nat.cast_ofNat, true_and] at hiff
    refine hiff.trans ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨?_, h.2⟩⟩
    rintro ⟨-, k, hk⟩
    rcases k with _ | k
    · omega
    · have : 2 ∣ 2 + 1 := hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)
      omega

/-- For `2 ≤ n` with `n ≠ 6`, there exists a prime `p` at which `2` has multiplicative order `n`
in `ZMod p`. -/
theorem exists_prime_orderOf_two_eq {n : ℕ} (hn : 2 ≤ n) (h₆ : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = n :=
  exists_prime_orderOf_two_eq_iff.2 ⟨by omega, h₆⟩

/-! ### Primitive prime divisors of sums of powers -/

/-- For coprime natural numbers `0 < b < a` and any `n`, there exists a prime dividing
`a ^ n + b ^ n` and none of `a ^ k - b ^ k` for `0 < k < 2 * n` if and only if neither `n = 1`
with `a + b` a power of two nor `(a, b, n) = (2, 1, 3)` holds (at `n = 0`, `p = 2` divides
`a ^ 0 + b ^ 0 = 2`). -/
theorem exists_prime_dvd_pow_add_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k) ↔
      ¬ (n = 1 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬ (a = 2 ∧ b = 1 ∧ n = 3) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact ⟨fun _ => ⟨by omega, by omega⟩,
      fun _ => ⟨2, Nat.prime_two, by simp, fun k _ hk => by omega⟩⟩
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hiff := exists_prime_orderOf_div_eq_iff hb hba hab (by omega : 2 ≤ 2 * n)
  refine (exists_congr fun p => and_congr_right fun hp =>
    hp.dvd_pow_add_pow_and_not_dvd_iff_orderOf_eq hba.le hn).trans (hiff.trans ?_)
  exact and_congr (not_congr (and_congr_left' (by omega)))
    (not_congr (and_congr_right' (and_congr_right' (by omega))))

/-- **Primitive prime divisors of `a ^ n + b ^ n`.** For coprime natural numbers `0 < b < a` and
any `n`, there exists a prime dividing `a ^ n + b ^ n` and none of `a ^ k - b ^ k` for
`0 < k < 2 * n`, unless `n = 1` and `a + b` is a power of two, or `(a, b, n) = (2, 1, 3)`. -/
theorem exists_prime_dvd_pow_add_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b)
    (h₁ : n = 1 → ¬ ∃ k : ℕ, a + b = 2 ^ k)
    (h₃ : n = 3 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬ p ∣ a ^ k - b ^ k :=
  (exists_prime_dvd_pow_add_pow_iff hb hba hab).2
    ⟨fun ⟨hn1, hk⟩ => h₁ hn1 hk, fun ⟨ha, hb1, hn3⟩ => by
      rcases h₃ hn3 with h | h <;> [exact h ha; exact h hb1]⟩

end TauCeti
