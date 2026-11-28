/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.SelbergSieve
public import TauCeti.NumberTheory.Chebyshev.ResidueClass
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Data.Int.CardIntervalMod
import TauCeti.Data.Nat.Squarefree
import TauCeti.NumberTheory.SelbergSieve.CoprimeDiagonal

/-!
# Selberg's sieve for primes in an arithmetic progression

Sift the positive integers `n ≤ x` with `n ≡ a (mod k)` by the primes at most `z` that do not
divide `k`, with local density `1 / d` and approximate mass `x / k`. For `d` coprime to `k` the
members of the progression divisible by `d` form one residue class modulo `d k`, so the remainders
are bounded by `2`, uniformly in the modulus, the class and the index. Every prime of the
progression greater than `z` survives the sieve.

Selberg's upper bound, with the diagonal mass bounded below by `(φ(k) / k) log z`
(`BoundingSieve.totient_div_mul_log_le_diagonalMass`), gives

`π(x; k, a) ≤ x / (φ(k) log z) + 2 z² (1 + 2 log z)² + z`

for every modulus `k ≥ 1`, every `x ≥ 0` and every `z > 1`. With `z = (x / k) ^ (1 / 3)` this is
the Brun–Titchmarsh bound

`π(x; k, a) ≤ C x / (φ(k) log (x / k))` for `k ≥ 1` and `x ≥ 4 k`,

with an absolute constant `C` (the proof gives `C = 906`; the classical constant `2 + o(1)` needs
a sharper treatment of the remainder and is not claimed). The class `a` need not be reduced.

## Main definitions

* `BoundingSieve.primeProgression k a x z`: the sieve.

## Main results

* `BoundingSieve.abs_rem_primeProgression_le`: the remainders are at most `2` in absolute value,
  for every modulus including `0`.
* `BoundingSieve.card_primesLE_filter_modEq_le`: the primes of the progression are counted by the
  sifted sum, up to `⌊z⌋₊`.
* `TauCeti.primeCountAP_le_div_log_add`: the bound at an arbitrary sieving level `z > 1`, for
  `k ≥ 1`.
* `TauCeti.exists_primeCountAP_le_mul_div_totient_mul_log`: the Brun–Titchmarsh bound for `k ≥ 1`
  and `x ≥ 4 k`, for a class in `ZMod k`.
* `TauCeti.exists_card_primesLE_filter_modEq_le_mul_div_totient_mul_log`: the same bound for the
  number of primes `p ≤ x` with `p ≡ a (mod k)`, `a` a natural number.

## References

* D. R. Heath-Brown, *Lectures on sieves*, arXiv:math/0209360, §3, the second application of
  Corollary 3.1, estimates (3.5)–(3.6).
-/

public noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace BoundingSieve

/-- Sift the positive integers `n ≤ x` with `n ≡ a (mod k)` by the primes at most `z` that do not
divide `k`, with reciprocal densities and approximate mass `x / k`. -/
def primeProgression (k a : ℕ) (x z : ℝ) : BoundingSieve where
  support := (Ioc 0 ⌊x⌋₊).filter (· ≡ a [MOD k])
  prodPrimes := ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (¬· ∣ k), p
  prodPrimes_squarefree := Nat.squarefree_prod_of_prime fun _ hp ↦
    (Nat.mem_primesLE.1 (mem_filter.1 hp).1).2
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := x / k
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := by
    intro p hp _
    simp [ite_eq_right hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := by
    intro p hp _
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

variable (k a : ℕ) (x z : ℝ)

/-- The progression sieve is supported on the positive `n ≤ x` congruent to `a` modulo `k`. -/
@[simp]
theorem primeProgression_support :
    (primeProgression k a x z).support = (Ioc 0 ⌊x⌋₊).filter (· ≡ a [MOD k]) := by
  rfl

/-- The progression sieve removes the primes at most its cutoff that do not divide the modulus. -/
@[simp]
theorem primeProgression_prodPrimes :
    (primeProgression k a x z).prodPrimes =
      ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (¬· ∣ k), p := by
  rfl

/-- Every member of a progression sieve has unit weight. -/
@[simp]
theorem primeProgression_weights : (primeProgression k a x z).weights = fun _ ↦ 1 := by
  rfl

/-- The main-term mass of a progression sieve is `x / k`. -/
@[simp]
theorem primeProgression_totalMass : (primeProgression k a x z).totalMass = x / k := by
  rfl

/-- The local density is the reciprocal of the natural index, including zero. -/
@[simp]
theorem primeProgression_nu_apply (d : ℕ) : (primeProgression k a x z).nu d = (d : ℝ)⁻¹ := by
  by_cases hd : d = 0 <;> simp [primeProgression, hd]

variable {k a x z}

/-- A prime divides the sieving product of a progression sieve exactly when it is at most the
cutoff and does not divide the modulus. -/
theorem prime_dvd_primeProgression_prodPrimes_iff {p : ℕ} (hp : p.Prime) :
    p ∣ (primeProgression k a x z).prodPrimes ↔ p ≤ ⌊z⌋₊ ∧ ¬p ∣ k := by
  rw [primeProgression_prodPrimes]
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hp.prime h
    obtain ⟨hq, hqk⟩ := mem_filter.1 hq
    obtain ⟨hqz, hqp⟩ := Nat.mem_primesLE.1 hq
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hqp).1 hpq
    exact ⟨hqz, hqk⟩
  · rintro ⟨hpz, hpk⟩
    exact dvd_prod_of_mem _ (mem_filter.2 ⟨Nat.mem_primesLE.2 ⟨hpz, hp⟩, hpk⟩)

/-- A divisor of the sieving product of a progression sieve is coprime to the modulus. -/
theorem coprime_of_dvd_primeProgression_prodPrimes {d : ℕ}
    (hd : d ∣ (primeProgression k a x z).prodPrimes) : d.Coprime k := by
  rw [primeProgression_prodPrimes] at hd
  refine Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.prod_left fun p hp ↦ ?_)
  obtain ⟨hp, hpk⟩ := mem_filter.1 hp
  exact ((Nat.mem_primesLE.1 hp).2.coprime_iff_not_dvd).2 hpk

/-- For the modulus `0` the progression is the single number `a`, the sieving product is `1`, and
the remainder at `d = 1` is `0` or `1`. -/
private theorem abs_rem_primeProgression_zero_le {d : ℕ}
    (hd : d ∣ (primeProgression 0 a x z).prodPrimes) :
    |(primeProgression 0 a x z).rem d| ≤ 2 := by
  have hP : (primeProgression 0 a x z).prodPrimes = 1 := by
    rw [primeProgression_prodPrimes,
      filter_false_of_mem fun p _ ↦ not_not.2 (dvd_zero p), prod_empty]
  obtain rfl : d = 1 := Nat.dvd_one.1 (hP ▸ hd)
  have hcard : #((Ioc 0 ⌊x⌋₊).filter (· ≡ a [MOD 0])) ≤ 1 := card_le_one.2 fun m hm n hn ↦
    (Nat.modEq_zero_iff.1 (mem_filter.1 hm).2).trans (Nat.modEq_zero_iff.1 (mem_filter.1 hn).2).symm
  have hmult : (primeProgression 0 a x z).multSum 1 =
      (#((Ioc 0 ⌊x⌋₊).filter (· ≡ a [MOD 0])) : ℝ) := by
    simp [multSum]
  rw [rem, hmult, primeProgression_totalMass, Nat.cast_zero, div_zero, mul_zero, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hcard.trans one_le_two

/-- **The remainder of the progression sieve is bounded.** For `0 ≤ x` and `d` dividing the
sieving product, the number of `n ≤ x` with `n ≡ a (mod k)` and `d ∣ n` differs from `x / (d k)`
by at most `2`: these `n` form one residue class modulo `d k`. -/
theorem abs_rem_primeProgression_le (hx : 0 ≤ x) {d : ℕ}
    (hd : d ∣ (primeProgression k a x z).prodPrimes) :
    |(primeProgression k a x z).rem d| ≤ 2 := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact abs_rem_primeProgression_zero_le hd
  have hcop : d.Coprime k := coprime_of_dvd_primeProgression_prodPrimes hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (primeProgression k a x z).prodPrimes_ne_zero hd
  obtain ⟨c, hcd, hck⟩ := Nat.chineseRemainder hcop 0 a
  have hfilter : ((Ioc 0 ⌊x⌋₊).filter (· ≡ a [MOD k])).filter (d ∣ ·) =
      (Ioc 0 ⌊x⌋₊).filter (· ≡ c [MOD d * k]) := by
    rw [filter_filter]
    refine filter_congr fun n _ ↦ ?_
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h2.trans hcd.symm, h1.trans hck.symm⟩,
      fun ⟨h1, h2⟩ ↦ ⟨h2.trans hck, h1.trans hcd⟩⟩
  have hmult : (primeProgression k a x z).multSum d =
      (#((Ioc 0 ⌊x⌋₊).filter (· ≡ c [MOD d * k])) : ℝ) := by
    simp only [multSum, primeProgression_support, primeProgression_weights, sum_boole,
      hfilter]
  have hdk : 0 < d * k := Nat.mul_pos (Nat.pos_of_ne_zero hd0) (Nat.pos_of_ne_zero hk)
  have hcount := Nat.abs_card_Ioc_filter_modEq_sub_div_lt hdk (Nat.zero_le ⌊x⌋₊) c
  have hcount' : |(#((Ioc 0 ⌊x⌋₊).filter (· ≡ c [MOD d * k])) : ℝ) -
      (⌊x⌋₊ : ℝ) / ((d * k : ℕ) : ℝ)| < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hcount
    push_cast at h
    simpa using h
  have hdk' : (1 : ℝ) ≤ ((d * k : ℕ) : ℝ) := by exact_mod_cast hdk
  have hfloor : |(⌊x⌋₊ : ℝ) / ((d * k : ℕ) : ℝ) - x / ((d * k : ℕ) : ℝ)| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((d * k : ℕ) : ℝ)),
      div_le_one (by linarith)]
    have h1 := Nat.floor_le hx
    have h2 := Nat.lt_floor_add_one x
    rw [abs_le]
    constructor <;> linarith
  have hrem : (primeProgression k a x z).rem d =
      ((#((Ioc 0 ⌊x⌋₊).filter (· ≡ c [MOD d * k])) : ℝ) - (⌊x⌋₊ : ℝ) / ((d * k : ℕ) : ℝ)) +
        ((⌊x⌋₊ : ℝ) / ((d * k : ℕ) : ℝ) - x / ((d * k : ℕ) : ℝ)) := by
    rw [rem, hmult, primeProgression_nu_apply, primeProgression_totalMass, Nat.cast_mul]
    field_simp
    ring
  rw [hrem]
  exact (abs_add_le _ _).trans (by linarith)

/-- The sifted sum of a progression sieve counts the members of the progression coprime to the
sieving product. -/
theorem siftedSum_primeProgression :
    (primeProgression k a x z).siftedSum =
      (#(((Ioc 0 ⌊x⌋₊).filter (· ≡ a [MOD k])).filter
        (Nat.Coprime (primeProgression k a x z).prodPrimes)) : ℝ) := by
  simp only [siftedSum, primeProgression_support, primeProgression_weights]
  exact (natCast_card_filter _ _).symm

/-- **Primes of a progression survive its sieve, except for those at most the cutoff.** The
number of primes `p ≤ x` with `p ≡ a (mod k)` is at most the sifted sum plus `⌊z⌋₊`. No
coprimality of `a` and `k` is needed. -/
theorem card_primesLE_filter_modEq_le :
    (#((Nat.primesLE ⌊x⌋₊).filter (· ≡ a [MOD k])) : ℝ) ≤
      (primeProgression k a x z).siftedSum + ⌊z⌋₊ := by
  rw [siftedSum_primeProgression]
  have hsub : (Nat.primesLE ⌊x⌋₊).filter (· ≡ a [MOD k]) ⊆
      ((Ioc 0 ⌊x⌋₊).filter (· ≡ a [MOD k])).filter
        (Nat.Coprime (primeProgression k a x z).prodPrimes) ∪ Ioc 0 ⌊z⌋₊ := by
    intro p hp
    obtain ⟨hp, hpa⟩ := mem_filter.1 hp
    obtain ⟨hpx, hpp⟩ := Nat.mem_primesLE.1 hp
    by_cases hpz : p ≤ ⌊z⌋₊
    · exact mem_union_right _ (mem_Ioc.2 ⟨hpp.pos, hpz⟩)
    · refine mem_union_left _ (mem_filter.2 ⟨mem_filter.2 ⟨mem_Ioc.2 ⟨hpp.pos, hpx⟩, hpa⟩, ?_⟩)
      apply Nat.Coprime.symm
      rw [hpp.coprime_iff_not_dvd, prime_dvd_primeProgression_prodPrimes_iff hpp]
      exact fun h ↦ hpz h.1
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.card_Ioc, Nat.sub_zero] at hcard
  exact_mod_cast hcard

end BoundingSieve

namespace TauCeti

open scoped ArithmeticFunction.omega

/-- **Selberg's sieve for primes in an arithmetic progression.** For every modulus `k ≥ 1`, every
residue class `a` modulo `k`, every real `x ≥ 0` and every sieving level `z > 1`,
`π(x; k, a) ≤ x / (φ(k) log z) + 2 z² (1 + 2 log z)² + z`. -/
theorem primeCountAP_le_div_log_add (k : ℕ) [NeZero k] (a : ZMod k) {x z : ℝ} (hx : 0 ≤ x)
    (hz : 1 < z) :
    (Chebyshev.primeCountAP k a x : ℝ) ≤
      x / (k.totient * Real.log z) + 2 * (z ^ 2 * (1 + 2 * Real.log z) ^ 2) + z := by
  set s := BoundingSieve.primeProgression k a.val x z
  have hk : k ≠ 0 := NeZero.ne k
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hφ : (0 : ℝ) < k.totient := Nat.cast_pos.2 (Nat.totient_pos.2 (Nat.pos_of_ne_zero hk))
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hcount : (Chebyshev.primeCountAP k a x : ℝ) =
      #((Nat.primesLE ⌊x⌋₊).filter (· ≡ a.val [MOD k])) := by
    rw [← Chebyshev.primeCountAP_natCast, ZMod.natCast_zmod_val]
  have hG : (k.totient : ℝ) / k * Real.log z ≤ s.diagonalMass z :=
    s.totient_div_mul_log_le_diagonalMass k (by linarith)
      (fun p hp hpz hpk ↦ (BoundingSieve.prime_dvd_primeProgression_prodPrimes_iff hp).2
        ⟨Nat.le_floor hpz.le, hpk⟩)
      fun p _ _ _ ↦ by rw [BoundingSieve.primeProgression_nu_apply]
  have hmain : s.totalMass / s.diagonalMass z ≤ x / (k.totient * Real.log z) := by
    rw [BoundingSieve.primeProgression_totalMass]
    calc x / k / s.diagonalMass z ≤ x / k / ((k.totient : ℝ) / k * Real.log z) :=
          div_le_div_of_nonneg_left (div_nonneg hx hk0.le)
            (mul_pos (div_pos hφ hk0) hlog) hG
      _ = x / (k.totient * Real.log z) := by
          field_simp
  calc (Chebyshev.primeCountAP k a x : ℝ) ≤ s.siftedSum + ⌊z⌋₊ :=
        hcount ▸ BoundingSieve.card_primesLE_filter_modEq_le
    _ ≤ (s.totalMass / s.diagonalMass z +
          ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < z ^ 2),
            (3 : ℝ) ^ ω d * |s.rem d|) + z :=
        add_le_add (s.siftedSum_le_totalMass_div_diagonalMass_add_sum_three_pow hz)
          (Nat.floor_le (by linarith))
    _ ≤ x / (k.totient * Real.log z) + 2 * (z ^ 2 * (1 + 2 * Real.log z) ^ 2) + z :=
        add_le_add_left (add_le_add hmain
          (s.sum_three_pow_mul_abs_rem_le_mul fun d hd ↦
            BoundingSieve.abs_rem_primeProgression_le hx (Nat.dvd_of_mem_divisors hd))) z

/-- With `E = exp (L / 3)` and `L ≥ 1`, the remainder and small-prime terms of the level
`z = E` are at most `903 exp L / L`: `L (1 + 2 L / 3)² ≤ 450 E` and `E L ≤ 3 E²`. -/
private theorem two_mul_exp_sq_mul_add_exp_le {L : ℝ} (hL : 1 ≤ L) :
    2 * (Real.exp (L / 3) ^ 2 * (1 + 2 * (L / 3)) ^ 2) + Real.exp (L / 3) ≤
      903 * (Real.exp L / L) := by
  set E := Real.exp (L / 3) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hE3 : E ^ 3 = Real.exp L := by
    rw [hEdef, ← Real.exp_natCast_mul, Nat.cast_ofNat, mul_div_cancel₀ _ (by norm_num)]
  have hcube : L ^ 3 / 162 ≤ E := by
    have h := Real.pow_div_factorial_le_exp (L / 3) (by linarith) 3
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6] at h
    calc L ^ 3 / 162 = (L / 3) ^ 3 / 6 := by ring
      _ ≤ E := h
  have h2 : 2 * (E ^ 2 * (1 + 2 * (L / 3)) ^ 2) ≤ 900 * Real.exp L / L := by
    rw [le_div_iff₀ (by linarith)]
    have hsq : (1 + 2 * (L / 3)) ^ 2 ≤ (5 * L / 3) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc 2 * (E ^ 2 * (1 + 2 * (L / 3)) ^ 2) * L ≤ 2 * (E ^ 2 * (5 * L / 3) ^ 2) * L := by
          gcongr
      _ = 900 * E ^ 2 * (L ^ 3 / 162) := by ring
      _ ≤ 900 * E ^ 2 * E := by gcongr
      _ = 900 * Real.exp L := by rw [← hE3]; ring
  have h3 : E ≤ 3 * Real.exp L / L := by
    rw [le_div_iff₀ (by linarith)]
    have hLE : L / 3 ≤ E := by linarith [Real.add_one_le_exp (L / 3)]
    calc E * L ≤ E * (3 * E) := by gcongr; linarith
      _ = 3 * E ^ 2 := by ring
      _ ≤ 3 * E ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hE1 (by norm_num)) (by norm_num)
      _ = 3 * Real.exp L := by rw [hE3]
  rw [mul_div_assoc] at h2 h3
  linarith

/-- **The Brun–Titchmarsh bound for primes in arithmetic progressions.** There is an absolute
constant `C` such that for every modulus `k ≥ 1`, every residue class `a` modulo `k` and every
real `x ≥ 4 k`, `π(x; k, a) ≤ C x / (φ(k) log (x / k))`. The class need not be reduced. -/
theorem exists_primeCountAP_le_mul_div_totient_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) [NeZero k] (a : ZMod k) (x : ℝ), 4 * (k : ℝ) ≤ x →
      (Chebyshev.primeCountAP k a x : ℝ) ≤ C * x / (k.totient * Real.log (x / k)) := by
  refine ⟨906, by norm_num, fun k _ a x hx ↦ ?_⟩
  have hk : k ≠ 0 := NeZero.ne k
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hφ : (0 : ℝ) < k.totient := Nat.cast_pos.2 (Nat.totient_pos.2 (Nat.pos_of_ne_zero hk))
  have hφk : (k.totient : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hu : 4 ≤ x / k := (le_div_iff₀ hk0).2 hx
  set L := Real.log (x / k) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans (by linarith [Real.exp_one_lt_three]) hu)
  have hexp : Real.exp L = x / k := Real.exp_log (by linarith)
  have hlevel := primeCountAP_le_div_log_add k a hx0
    (Real.one_lt_exp_iff.2 (by linarith : 0 < L / 3))
  rw [Real.log_exp] at hlevel
  have haux := two_mul_exp_sq_mul_add_exp_le hL
  rw [hexp] at haux
  have h1 : x / (k.totient * (L / 3)) = 3 * (x / (k.totient * L)) := by
    field_simp
  have h4 : x / k / L ≤ x / (k.totient * L) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hx0 (mul_pos hφ (by linarith))
      (mul_le_mul_of_nonneg_right hφk (by linarith))
  calc (Chebyshev.primeCountAP k a x : ℝ)
      ≤ 3 * (x / (k.totient * L)) + 903 * (x / k / L) := by
        rw [← h1]
        linarith
    _ ≤ 906 * (x / (k.totient * L)) := by linarith
    _ = 906 * x / (k.totient * L) := by rw [mul_div_assoc]

/-- **The Brun–Titchmarsh bound, for natural residues.** There is an absolute constant `C` such
that for every modulus `k ≥ 1`, every natural number `a` and every real `x ≥ 4 k`, the number of
primes `p ≤ x` with `p ≡ a (mod k)` is at most `C x / (φ(k) log (x / k))`. The number `a` need
not be coprime to `k`. -/
theorem exists_card_primesLE_filter_modEq_le_mul_div_totient_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (k a : ℕ) (x : ℝ), k ≠ 0 → 4 * (k : ℝ) ≤ x →
      (#{p ∈ Nat.primesLE ⌊x⌋₊ | p ≡ a [MOD k]} : ℝ) ≤
        C * x / (k.totient * Real.log (x / k)) := by
  obtain ⟨C, hC, h⟩ := exists_primeCountAP_le_mul_div_totient_mul_log
  refine ⟨C, hC, fun k a x hk hx ↦ ?_⟩
  have : NeZero k := ⟨hk⟩
  rw [← Chebyshev.primeCountAP_natCast]
  exact h k a x hx

end TauCeti
