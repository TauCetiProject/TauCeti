/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import TauCeti.Data.Nat.ModEq
import Mathlib.Tactic.NormNum.Prime
import TauCeti.Algebra.Group.Pow
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Parameters of the one-sided prime sum bound

The one-sided bound for the prime sums of the imaginary quadratic field `K = ℚ(√-d)` works with
fixed *parameters* `(q₀, d)`: a natural number `q₀` divisible by `18480 = 16 · 3 · 5 · 7 · 11`
and a prime `d` with `q₀ ∣ 2 (d + 1)` and `q₀ ∤ d + 1`, that is `d ≡ q₀ / 2 - 1 (mod q₀)`
(`TauCeti.OneSidedBound.Parameters.modEq_div_two_sub_one`, and `Parameters.ofModEq` for the
converse). The character `χ_K = (· / d)` is written `legendreSym P.d`. An
exponent `s : ℕ` then determines the numbers

* `l₀ s = 3 ^ (⌊log₃ s⌋ + 4)`, the least power of `3` above `27 s` for `s ≥ 1`
  (with `⌊log₃ 0⌋ = 0`, as for `Nat.log`);
* `towerDeg s = 3 · l₀ s · 2 ^ s`;
* `P.q₁ s = q₀ · towerDeg s`, the order of the roots of unity adjoined to `K`;
* `P.q₂ s = (q₀ d) ^ (s + 6)`.

This file proves the elementary facts about them: `d ≡ 7 (mod 8)` and `d > 64`; the bounds
`27 s < l₀ s ≤ 81 s`; every prime `p` of `q₁ s` divides `q₀`, divides `(d + 1) / 4` and has
`(p / d) = 1` (by reciprocity for the Jacobi symbol, since `d ≡ -1 (mod 4p)`), so a prime with
`(p / d) ≠ 1` is at least `13`; `q₁ s` is prime to `d` and `q₁ s · d ∣ q₂ s`; and no power of
`d` is `-1` modulo `q₀`, since `d ^ 2 ≡ 1` but `d ≢ -1`.

## Main definitions

* `TauCeti.OneSidedBound.Parameters`: the parameters `(q₀, d)`.
* `TauCeti.OneSidedBound.l₀`, `TauCeti.OneSidedBound.towerDeg`,
  `TauCeti.OneSidedBound.Parameters.q₁`, `TauCeti.OneSidedBound.Parameters.q₂`.

## Main results

* `coprime_div_two_sub_one_of_dvd`, `div_two_sub_one_modEq_seven`: the designated residue
  class at every positive multiple of `18480` is reduced and is `7` modulo `8`.
* `TauCeti.OneSidedBound.Parameters.modEq_div_two_sub_one`, `Parameters.ofModEq`.
* `Parameters.q₀_pos`, `Parameters.d_mod_eight`, `Parameters.sixty_four_lt_d`.
* `TauCeti.OneSidedBound.towerDeg_eq`: `towerDeg s = 3 ^ (⌊log₃ s⌋ + 5) · 2 ^ s`.
* `TauCeti.OneSidedBound.lt_l₀`, `TauCeti.OneSidedBound.l₀_le`, `Parameters.two_pow_succ_dvd_q₁`.
* `Parameters.dvd_q₀_of_dvd_q₁`, `Parameters.four_mul_dvd_d_add_one`,
  `Parameters.dvd_d_add_one_div_four`, `Parameters.legendreSym_eq_one_of_dvd_q₁`,
  `Parameters.thirteen_le_of_legendreSym_ne_one`.
* `Parameters.coprime_q₁_d`, `Parameters.q₁_mul_d_dvd_q₂`.
* `Parameters.d_pow_ne_neg_one`.

## References

* The statements follow the formal proof in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207:
  `New.Parameters`, `New.Parameters.instPrimeSevenModEight`, `New.Parameters.sixty_four_lt_d`,
  `New.l₀`, `New.towerDeg`, `New.Parameters.q₁`, `New.Parameters.q₂`,
  `New.Parameters.chiK_eq_one_of_dvd`, `New.Parameters.thirteen_le_of_chiK_ne_one`,
  `New.Parameters.coprime_q₁_d`, `New.Parameters.q₁_mul_d_dvd_q₂`,
  `New.Parameters.d_pow_ne_neg_one` and `New.dvd_two_mul_succ_and_not_dvd_succ`.
-/

public section

namespace TauCeti.OneSidedBound

/-- `l₀ s = 3 ^ (⌊log₃ s⌋ + 4)`, with `⌊log₃ 0⌋ = 0`: for `s ≥ 1` the least power of `3` above
`27 s` (`lt_l₀`, `l₀_le`). The `3`-part of `towerDeg s` is `3 · l₀ s`. -/
def l₀ (s : ℕ) : ℕ := 3 ^ (Nat.log 3 s + 4)

/-- The definition of `l₀`. -/
theorem l₀_def (s : ℕ) : l₀ s = 3 ^ (Nat.log 3 s + 4) := (rfl)

/-- The degree of the tower: `towerDeg s = 3 · l₀ s · 2 ^ s = 3 ^ (⌊log₃ s⌋ + 5) · 2 ^ s`
(`towerDeg_eq`). -/
def towerDeg (s : ℕ) : ℕ := 3 * l₀ s * 2 ^ s

/-- The definition of `towerDeg`. -/
theorem towerDeg_def (s : ℕ) : towerDeg s = 3 * l₀ s * 2 ^ s := (rfl)

/-- The closed form `towerDeg s = 3 ^ (⌊log₃ s⌋ + 5) · 2 ^ s`. -/
theorem towerDeg_eq (s : ℕ) : towerDeg s = 3 ^ (Nat.log 3 s + 5) * 2 ^ s := by
  rw [towerDeg_def, l₀_def, ← pow_succ']

/-- `27 s < l₀ s` for every `s`. -/
theorem lt_l₀ (s : ℕ) : 27 * s < l₀ s := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) s
  rw [l₀_def, pow_add]
  omega

/-- `l₀ s ≤ 81 s` for `s ≠ 0`. -/
theorem l₀_le {s : ℕ} (hs : s ≠ 0) : l₀ s ≤ 81 * s := by
  have h := Nat.pow_log_le_self 3 hs
  rw [l₀_def, pow_add]
  omega

/-- `towerDeg s` is positive. -/
theorem towerDeg_pos (s : ℕ) : 0 < towerDeg s := by
  rw [towerDeg_eq]
  positivity

/-- **Parameters** `(q₀, d)`: a natural number `q₀` divisible by `18480 = 16 · 3 · 5 · 7 · 11`
and a prime `d` with `q₀ ∣ 2 (d + 1)` and `q₀ ∤ d + 1`, that is `d ≡ q₀ / 2 - 1 (mod q₀)`
(`Parameters.modEq_div_two_sub_one`). The character `χ_K = (· / d)` is `legendreSym P.d`.
Two parameters are equal when their `q₀` and `d` are (`Parameters.ext`). -/
@[ext]
structure Parameters where
  /-- The modulus. -/
  q₀ : ℕ
  /-- The prime. -/
  d : ℕ
  /-- `18480 = 16 · 3 · 5 · 7 · 11` divides `q₀`. -/
  dvd_q₀ : 18480 ∣ q₀
  /-- `d` is prime. -/
  prime_d : d.Prime
  /-- `q₀ ∣ 2 (d + 1)`: with `not_q₀_dvd_d_add_one`, the congruence `d ≡ q₀ / 2 - 1`. -/
  q₀_dvd_two_mul_d_add_one : q₀ ∣ 2 * (d + 1)
  /-- `q₀ ∤ d + 1`: with `q₀_dvd_two_mul_d_add_one`, the congruence `d ≡ q₀ / 2 - 1`. -/
  not_q₀_dvd_d_add_one : ¬ q₀ ∣ d + 1

/-- The residue `q₀ / 2 - 1` is prime to `q₀` at every positive multiple of `18480`. -/
theorem coprime_div_two_sub_one_of_dvd {q₀ : ℕ} (hq₀ : q₀ ≠ 0) (hq : 18480 ∣ q₀) :
    (q₀ / 2 - 1).Coprime q₀ :=
  (Nat.coprime_div_two_sub_one_iff (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 18480).trans hq))
    hq₀).mpr ((by norm_num : 4 ∣ 18480).trans hq)

/-- The residue `q₀ / 2 - 1` is `7` modulo `8` at every positive multiple of `18480`. -/
theorem div_two_sub_one_modEq_seven {q₀ : ℕ} (hq₀ : q₀ ≠ 0) (hq : 18480 ∣ q₀) :
    q₀ / 2 - 1 ≡ 7 [MOD 8] :=
  Nat.div_two_sub_one_modEq_of_mul_dvd hq₀ ((by decide : 2 * 8 ∣ 18480).trans hq)

namespace Parameters

variable (P : Parameters)

/-- The prime `d` of parameters, as an instance, for `legendreSym P.d` and `ZMod P.d`. -/
instance fact_prime_d : Fact P.d.Prime := ⟨P.prime_d⟩

/-- `q₁ s = q₀ · towerDeg s`, the order of the roots of unity adjoined to `ℚ(√-d)`. -/
def q₁ (s : ℕ) : ℕ := P.q₀ * towerDeg s

/-- `q₂ s = (q₀ d) ^ (s + 6)`. -/
def q₂ (s : ℕ) : ℕ := (P.q₀ * P.d) ^ (s + 6)

/-- The definition of `q₁`. -/
theorem q₁_def (s : ℕ) : P.q₁ s = P.q₀ * towerDeg s := (rfl)

/-- The definition of `q₂`. -/
theorem q₂_def (s : ℕ) : P.q₂ s = (P.q₀ * P.d) ^ (s + 6) := (rfl)

/-- `q₀ > 0`, since `q₀` divides `2 (d + 1) ≠ 0`. -/
theorem q₀_pos : 0 < P.q₀ :=
  Nat.pos_of_dvd_of_pos P.q₀_dvd_two_mul_d_add_one (by omega)

/-- `q₀ ≠ 0`. -/
theorem q₀_ne_zero : P.q₀ ≠ 0 := P.q₀_pos.ne'

/-- `q₀ ≠ 0`, as an instance, for `ZMod P.q₀`. -/
instance neZero_q₀ : NeZero P.q₀ := ⟨P.q₀_ne_zero⟩

/-- `18480 ≤ q₀`. -/
theorem le_q₀ : 18480 ≤ P.q₀ := Nat.le_of_dvd P.q₀_pos P.dvd_q₀

/-- `2 ∣ q₀`. -/
theorem two_dvd_q₀ : 2 ∣ P.q₀ := (by norm_num : 2 ∣ 18480).trans P.dvd_q₀

/-- `3 ∣ q₀`. -/
theorem three_dvd_q₀ : 3 ∣ P.q₀ := (by norm_num : 3 ∣ 18480).trans P.dvd_q₀

/-- `q₁ s > 0`. -/
theorem q₁_pos (s : ℕ) : 0 < P.q₁ s := Nat.mul_pos P.q₀_pos (towerDeg_pos s)

/-- `q₁ s ≠ 0`, as an instance, for `ZMod (P.q₁ s)` and roots of unity of order `q₁ s`. -/
instance neZero_q₁ (s : ℕ) : NeZero (P.q₁ s) := ⟨(P.q₁_pos s).ne'⟩

/-- The congruence `d ≡ q₀ / 2 - 1 (mod q₀)` stored in the two divisibilities. -/
theorem modEq_div_two_sub_one : P.d ≡ P.q₀ / 2 - 1 [MOD P.q₀] :=
  (Nat.modEq_div_two_sub_one_iff (even_iff_two_dvd.2 P.two_dvd_q₀) P.q₀_ne_zero).2
    ⟨P.q₀_dvd_two_mul_d_add_one, P.not_q₀_dvd_d_add_one⟩

/-- Parameters from the congruence `d ≡ q₀ / 2 - 1 (mod q₀)`. -/
def ofModEq {q₀ d : ℕ} (hq₀ : 18480 ∣ q₀) (hd : d.Prime) (h : d ≡ q₀ / 2 - 1 [MOD q₀]) :
    Parameters :=
  have hq₀' : q₀ ≠ 0 := by
    rintro rfl
    exact hd.ne_zero (by simpa [Nat.ModEq] using h)
  have h' := (Nat.modEq_div_two_sub_one_iff
    (even_iff_two_dvd.2 ((by norm_num : 2 ∣ 18480).trans hq₀)) hq₀').1 h
  ⟨q₀, d, hq₀, hd, h'.1, h'.2⟩

/-- The modulus of `ofModEq hq₀ hd h` is `q₀`. -/
@[simp] theorem ofModEq_q₀ {q₀ d : ℕ} (hq₀ : 18480 ∣ q₀) (hd : d.Prime)
    (h : d ≡ q₀ / 2 - 1 [MOD q₀]) : (ofModEq hq₀ hd h).q₀ = q₀ := (rfl)

/-- The prime of `ofModEq hq₀ hd h` is `d`. -/
@[simp] theorem ofModEq_d {q₀ d : ℕ} (hq₀ : 18480 ∣ q₀) (hd : d.Prime)
    (h : d ≡ q₀ / 2 - 1 [MOD q₀]) : (ofModEq hq₀ hd h).d = d := (rfl)

/-- `8 ∣ d + 1`, since `16 ∣ q₀ ∣ 2 (d + 1)`. -/
theorem eight_dvd_d_add_one : 8 ∣ P.d + 1 := by
  have := ((by norm_num : 16 ∣ 18480).trans P.dvd_q₀).trans P.q₀_dvd_two_mul_d_add_one
  omega

/-- `4 ∣ d + 1`. -/
theorem four_dvd_d_add_one : 4 ∣ P.d + 1 := (by norm_num : 4 ∣ 8).trans P.eight_dvd_d_add_one

/-- `d ≡ 7 (mod 8)`. -/
theorem d_mod_eight : P.d % 8 = 7 := by
  have hd := P.modEq_div_two_sub_one.of_dvd ((by decide : 8 ∣ 18480).trans P.dvd_q₀)
  have h₇ := div_two_sub_one_modEq_seven P.q₀_ne_zero P.dvd_q₀
  simp_all [Nat.ModEq]

/-- `d` is odd. -/
theorem odd_d : Odd P.d := Nat.odd_iff.2 (by have := P.d_mod_eight; omega)

/-- `d > 64`: indeed `18480 ≤ q₀ ≤ 2 (d + 1)`. -/
theorem sixty_four_lt_d : 64 < P.d := by
  have h₁ := P.le_q₀
  have h₂ := Nat.le_of_dvd (by omega) P.q₀_dvd_two_mul_d_add_one
  omega

/-- `2 ^ (s + 1) ∣ q₁ s`. -/
theorem two_pow_succ_dvd_q₁ (s : ℕ) : 2 ^ (s + 1) ∣ P.q₁ s := by
  rw [q₁_def, towerDeg_def, pow_succ', ← mul_assoc]
  exact mul_dvd_mul (P.two_dvd_q₀.mul_right _) dvd_rfl

/-- `q₀ ∣ q₁ s`. -/
theorem q₀_dvd_q₁ (s : ℕ) : P.q₀ ∣ P.q₁ s := dvd_mul_right _ _

/-- Every prime factor of `q₁ s` divides `q₀`. -/
theorem dvd_q₀_of_dvd_q₁ {p s : ℕ} (hp : p.Prime) (h : p ∣ P.q₁ s) : p ∣ P.q₀ := by
  rw [q₁_def, towerDeg_eq, hp.dvd_mul, hp.dvd_mul] at h
  rcases h with h | h | h
  · exact h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)]
    exact P.three_dvd_q₀
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)]
    exact P.two_dvd_q₀

/-- Every prime factor `p` of `q₀` satisfies `d ≡ -1 (mod 4 p)`. -/
theorem four_mul_dvd_d_add_one {p : ℕ} (hp : p.Prime) (h : p ∣ P.q₀) : 4 * p ∣ P.d + 1 := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · exact P.eight_dvd_d_add_one
  have h2 : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.2 (by omega)
  exact (h2.pow_left 2).mul_dvd_of_dvd_of_dvd P.four_dvd_d_add_one
    (h2.symm.dvd_of_dvd_mul_left (h.trans P.q₀_dvd_two_mul_d_add_one))

/-- Every prime factor of `q₁ s` divides `(d + 1) / 4`. -/
theorem dvd_d_add_one_div_four {p s : ℕ} (hp : p.Prime) (h : p ∣ P.q₁ s) :
    p ∣ (P.d + 1) / 4 :=
  (Nat.dvd_div_iff_mul_dvd P.four_dvd_d_add_one).2
    (P.four_mul_dvd_d_add_one hp (P.dvd_q₀_of_dvd_q₁ hp h))

/-- Every divisor `n` of `q₁ s` has `(n / d) = 1`; in particular `(p / d) = 1` for every prime
factor `p` of `q₁ s`. -/
theorem legendreSym_eq_one_of_dvd_q₁ {n s : ℕ} (h : n ∣ P.q₁ s) : legendreSym P.d n = 1 := by
  induction n using Nat.recOnMul with
  | zero => exact absurd (Nat.eq_zero_of_zero_dvd h) (P.q₁_pos s).ne'
  | one => exact_mod_cast legendreSym.at_one P.d
  | prime p hp =>
    -- `d ≡ -1 (mod 4p)`, so reciprocity for the Jacobi symbol gives `(p / d) = (p / 1) = 1`
    have h4 := P.four_mul_dvd_d_add_one hp (P.dvd_q₀_of_dvd_q₁ hp h)
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym_eq_sign_mul_of_dvd_add (p : ℤ) odd_one
      (b' := P.d) (by simpa [add_comm] using h4), jacobiSym.one_right, mul_one,
      Int.sign_natCast_of_ne_zero hp.ne_zero]
  | mul a b ha hb =>
    rw [Nat.cast_mul, legendreSym.mul, ha (dvd_of_mul_right_dvd h),
      hb (dvd_of_mul_left_dvd h), one_mul]

/-- A prime `p` with `(p / d) ≠ 1` is at least `13`: the primes below `13` divide `q₀`. -/
theorem thirteen_le_of_legendreSym_ne_one {p : ℕ} (hp : p.Prime) (h : legendreSym P.d p ≠ 1) :
    13 ≤ p := by
  by_contra! hlt
  -- the primes below `13` are `2, 3, 5, 7, 11`, all factors of `18480`
  have h₁ : p ∣ 18480 := by
    revert hp
    interval_cases p <;> norm_num
  exact h (P.legendreSym_eq_one_of_dvd_q₁ (s := 0) ((h₁.trans P.dvd_q₀).trans (P.q₀_dvd_q₁ 0)))

/-- `q₁ s` is prime to `d`. -/
theorem coprime_q₁_d (s : ℕ) : (P.q₁ s).Coprime P.d := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd P.prime_d).2 fun h ↦ ?_)
  have h₁ := (P.dvd_q₀_of_dvd_q₁ P.prime_d h).trans P.q₀_dvd_two_mul_d_add_one
  have h₂ : P.d ∣ 2 := by
    rw [mul_add, mul_one] at h₁
    exact (Nat.dvd_add_right (dvd_mul_left _ _)).1 h₁
  have := Nat.le_of_dvd (by norm_num) h₂
  have := P.sixty_four_lt_d
  omega

/-- `q₁ s · d ∣ q₂ s`. -/
theorem q₁_mul_d_dvd_q₂ (s : ℕ) : P.q₁ s * P.d ∣ P.q₂ s := by
  have h₆ : 3 * 2 ∣ P.q₀ :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) P.three_dvd_q₀ P.two_dvd_q₀
  have hT : towerDeg s ∣ P.q₀ ^ (s + 5) := by
    refine Nat.dvd_trans ?_ (pow_dvd_pow_of_dvd h₆ _)
    rw [towerDeg_eq, mul_pow]
    exact mul_dvd_mul (pow_dvd_pow 3 (by have := Nat.log_le_self 3 s; omega))
      (pow_dvd_pow 2 (by omega))
  -- regroup `q₂ s` as `q₀ · q₀ ^ (s + 5) · d ^ (s + 6)`, matching `q₀ · towerDeg s · d` factorwise
  rw [q₁_def, q₂_def, show (P.q₀ * P.d) ^ (s + 6) = P.q₀ * P.q₀ ^ (s + 5) * P.d ^ (s + 6) by ring]
  exact mul_dvd_mul (mul_dvd_mul_left _ hT) (dvd_pow_self _ (by omega))

/-- No power of `d` is `-1` modulo `q₀`: `d ^ 2 = 1` in `ZMod q₀`, so every power of `d` is `1`
or `d`, and neither is `-1` since `q₀ ∤ 2` and `q₀ ∤ d + 1`. -/
theorem d_pow_ne_neg_one (k : ℕ) : (P.d : ZMod P.q₀) ^ k ≠ -1 := by
  have h₂ : (2 * (P.d + 1) : ℕ) = (0 : ZMod P.q₀) :=
    (ZMod.natCast_eq_zero_iff _ _).2 P.q₀_dvd_two_mul_d_add_one
  have hsq : ((P.d + 1) * (P.d + 1) : ℕ) = (0 : ZMod P.q₀) :=
    (ZMod.natCast_eq_zero_iff _ _).2 (P.q₀_dvd_two_mul_d_add_one.trans
      (mul_dvd_mul_right P.odd_d.add_one.two_dvd _))
  push_cast at h₂ hsq
  rcases pow_eq_one_or_pow_eq_self_of_sq_eq_one (by linear_combination hsq - h₂) k with h | h <;>
    rw [h] <;> intro h'
  · have h2 : ((2 : ℕ) : ZMod P.q₀) = 0 := by push_cast; linear_combination h'
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h2)
    have := P.le_q₀
    omega
  · exact P.not_q₀_dvd_d_add_one ((ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; rw [h']; ring))

end Parameters

end TauCeti.OneSidedBound
