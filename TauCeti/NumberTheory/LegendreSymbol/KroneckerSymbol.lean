/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.Data.Int.Sign
import TauCeti.Data.Nat.Factorization.GcdSplit

/-!
# The Kronecker symbol

Mathlib's Jacobi symbol `jacobiSym a b` is defined for a natural denominator `b`, and is the
quadratic symbol only for odd `b`. The **Kronecker symbol** `(a / b)` extends it to every integer
denominator `b`, multiplicatively in `b`, by fixing the values at the three denominators the Jacobi
symbol does not cover:

* `(a / 2)` is `χ₈ a`: `0` for even `a`, `1` for `a ≡ ±1 (mod 8)` and `-1` for `a ≡ ±3 (mod 8)`;
* `(a / -1)` is `-1` for `a < 0` and `1` otherwise;
* `(a / 0)` is `1` for `a = ±1` and `0` otherwise.

So for `b ≠ 0`, writing `|b| = 2 ^ e * m` with `m` odd,
`(a / b) = (a / -1)^[b < 0] * χ₈ a ^ e * J(a | m)`. The value at `0` is not the Jacobi symbol's
`J(a | 0) = 1`: the two symbols agree on odd positive denominators only. That value also makes
multiplicativity in the denominator fail exactly for the numerator `-1`, where
`(-1 / 0) = 1` but `(-1 / 0) * (-1 / 3) = -1`.

The point of the extension is the case of a **discriminant** `D ≡ 0, 1 (mod 4)`. Then `(D / ·)` is
periodic modulo `|D|` on all of `ℤ`, so it is a quadratic Dirichlet character `kroneckerChar` of
modulus `|D|`, whose value at `-1` is the sign of `D`. For `D ≡ 1 (mod 4)` this rests on
quadratic reciprocity, in the form `(D / n) = J(n | |D|)`; for `D ≡ 0 (mod 4)` it rests on the
periodicity of `J(D | ·)` modulo `|D|` on odd numbers and on its reflection law under `b ↦ -b`.
The character need not be primitive: `(-12 / ·)` is induced from `(-3 / ·)`.

## Main definitions

* `TauCeti.kroneckerSym a b`: the Kronecker symbol `(a / b)`.
* `TauCeti.kroneckerChar R D hD hD₀`: for `D ≡ 0, 1 (mod 4)`, `D ≠ 0`, the Dirichlet character
  `(D / ·)` of modulus `|D|` with values in a commutative ring `R`.

## Main statements

* `TauCeti.kroneckerSym_eq_jacobiSym`, `TauCeti.kroneckerSym_eq_legendreSym`: agreement with the
  Jacobi symbol at odd positive denominators and with the Legendre symbol at odd primes.
* `TauCeti.kroneckerSym_two_right`, `TauCeti.kroneckerSym_neg_one_right`,
  `TauCeti.kroneckerSym_zero_right`: the values at `2`, `-1` and `0`.
* `TauCeti.kroneckerSym_mul_right`, `TauCeti.kroneckerSym_mul_right_of_ne_neg_one`:
  multiplicativity in the denominator, over nonzero factors, and without restriction when the
  numerator is not `-1`.
* `TauCeti.kroneckerSym_mul_left`: multiplicativity in the numerator, over nonzero factors.
* `TauCeti.kroneckerSym_eq_zero_iff`: `(a / b) = 0` exactly when `gcd (a, b) ≠ 1`.
* `TauCeti.kroneckerSym_eq_jacobiSym_natAbs`: `(D / n) = J(n | |D|)` for `D ≡ 1 (mod 4)`.
* `TauCeti.kroneckerSym_mod_right'`: for `D ≡ 0, 1 (mod 4)`, `(D / ·)` is periodic modulo `D`.
* `TauCeti.kroneckerChar_intCast`, `TauCeti.kroneckerChar_isQuadratic`,
  `TauCeti.kroneckerChar_neg_one`: the character computes the Kronecker symbol, is quadratic, and
  has value `sign D` at `-1`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §1.4.2.
* H. Cohen, *Number Theory, Volume I: Tools and Diophantine Equations*, §2.2.
-/

public section

open ZMod

namespace TauCeti

/-! ### Definition and the values at `0`, `-1`, `2` and odd denominators -/

/-- The **Kronecker symbol** `(a / b)`: the extension of the Jacobi symbol `jacobiSym a b` to all
integer denominators `b`, multiplicative in `b` (over nonzero factors, `kroneckerSym_mul_right`)
and with the standard values at `2`, `-1` and `0`: `(a / 2) = χ₈ a`, `(a / -1)` is the sign of
`a` with `(0 / -1) = 1`, and `(a / 0)` is `1` for `a = ±1` and `0` otherwise. For `b ≠ 0` with
`|b| = 2 ^ e * m`, `m` odd, it is `(a / -1)^[b < 0] * χ₈ a ^ e * J(a | m)`. -/
def kroneckerSym (a b : ℤ) : ℤ :=
  if b = 0 then if a = 1 ∨ a = -1 then 1 else 0
  else (if a < 0 ∧ b < 0 then -1 else 1) * χ₈ a ^ b.natAbs.factorization 2 *
    jacobiSym a (ordCompl[2] b.natAbs)

/-- `(a / 0)` is `1` for `a = ±1` and `0` otherwise. It is not `jacobiSym a 0 = 1`. -/
@[simp]
theorem kroneckerSym_zero_right (a : ℤ) :
    kroneckerSym a 0 = if a = 1 ∨ a = -1 then 1 else 0 :=
  ite_eq_left rfl

/-- The Kronecker symbol at a nonzero denominator `b`, with `|b| = 2 ^ e * m` and `m` odd. -/
theorem kroneckerSym_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    kroneckerSym a b = (if a < 0 ∧ b < 0 then -1 else 1) * χ₈ a ^ b.natAbs.factorization 2 *
      jacobiSym a (ordCompl[2] b.natAbs) :=
  ite_eq_right hb

/-- At an odd denominator `b`, of either sign, the Kronecker symbol is the Jacobi symbol at `|b|`,
times `-1` when both `a < 0` and `b < 0`. -/
theorem kroneckerSym_of_odd (a : ℤ) {b : ℤ} (hb : Odd b) :
    kroneckerSym a b = (if a < 0 ∧ b < 0 then -1 else 1) * jacobiSym a b.natAbs := by
  have h2 : ¬ 2 ∣ b.natAbs := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp (Int.natAbs_odd.mpr hb))
  rw [kroneckerSym_of_ne_zero a (by rintro rfl; exact Int.not_odd_zero hb),
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (Or.inr h2),
    Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, mul_one]

/-- At an odd positive denominator the Kronecker symbol is the Jacobi symbol. -/
theorem kroneckerSym_eq_jacobiSym (a : ℤ) {b : ℕ} (hb : Odd b) :
    kroneckerSym a b = jacobiSym a b := by
  rw [kroneckerSym_of_odd a (Int.odd_coe_nat b |>.mpr hb), Int.natAbs_natCast,
    ite_eq_right (fun h ↦ (Int.natCast_nonneg b).not_gt h.2), one_mul]

/-- At an odd prime the Kronecker symbol is the Legendre symbol. -/
theorem kroneckerSym_eq_legendreSym (a : ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    kroneckerSym a p = legendreSym p a := by
  rw [kroneckerSym_eq_jacobiSym a ((Fact.out : p.Prime).odd_of_ne_two hp),
    jacobiSym.legendreSym.to_jacobiSym]

/-- `(a / 1) = 1`. -/
@[simp]
theorem kroneckerSym_one_right (a : ℤ) : kroneckerSym a 1 = 1 := by
  simpa using kroneckerSym_eq_jacobiSym a odd_one

/-- `(a / -1)` is `-1` for `a < 0` and `1` otherwise. -/
@[simp]
theorem kroneckerSym_neg_one_right (a : ℤ) :
    kroneckerSym a (-1) = if a < 0 then -1 else 1 := by
  rw [kroneckerSym_of_odd a (by decide), Int.natAbs_neg, Int.natAbs_one, jacobiSym.one_right,
    mul_one]
  simp

/-- `(a / 2) = χ₈ a`: it is `0` for even `a`, `1` for `a ≡ ±1 (mod 8)` and `-1` for
`a ≡ ±3 (mod 8)` (`ZMod.χ₈_int_eq_if_mod_eight`). -/
@[simp]
theorem kroneckerSym_two_right (a : ℤ) : kroneckerSym a 2 = χ₈ a := by
  rw [kroneckerSym_of_ne_zero a two_ne_zero]
  simp [Nat.Prime.factorization_self Nat.prime_two]

/-- `(1 / b) = 1`, including at `b = 0`. -/
@[simp]
theorem kroneckerSym_one_left (b : ℤ) : kroneckerSym 1 b = 1 := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [kroneckerSym_zero_right]
  · simp [kroneckerSym_of_ne_zero 1 hb, jacobiSym.one_left]

/-! ### Multiplicativity in the denominator -/

/-- Multiplicativity of the Kronecker symbol in the denominator, over nonzero factors, as in
`jacobiSym.mul_right'`. The hypotheses cannot be dropped: for `a = -1`, `b = 0`, `c = 3` the left
side is `(-1 / 0) = 1` and the right side is `-1` (`kroneckerSym_zero_right`). -/
theorem kroneckerSym_mul_right (a : ℤ) {b c : ℤ} (hb : b ≠ 0) (hc : c ≠ 0) :
    kroneckerSym a (b * c) = kroneckerSym a b * kroneckerSym a c := by
  have hb' : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  have hc' : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  rw [kroneckerSym_of_ne_zero a (mul_ne_zero hb hc), kroneckerSym_of_ne_zero a hb,
    kroneckerSym_of_ne_zero a hc, Int.ite_and_mul_lt_zero hb hc]
  -- `|b c| = |b| |c|` splits both the power of `2` and the odd part, which `J(a | ·)` respects.
  simp only [Int.natAbs_mul, Nat.ordCompl_mul,
    jacobiSym.mul_right' a (Nat.ordCompl_pos 2 hb').ne' (Nat.ordCompl_pos 2 hc').ne']
  simp only [Nat.factorization_mul hb' hc', Finsupp.add_apply, pow_add]
  ring

/-- For a numerator other than `-1`, the Kronecker symbol is completely multiplicative in the
denominator: `(a / 0)` is `1` when `a = 1`, where every value is `1`, and `0` otherwise, where it
absorbs the product. Every discriminant `D ≡ 0, 1 (mod 4)` is such a numerator. -/
theorem kroneckerSym_mul_right_of_ne_neg_one {a : ℤ} (ha : a ≠ -1) (b c : ℤ) :
    kroneckerSym a (b * c) = kroneckerSym a b * kroneckerSym a c := by
  by_cases ha₁ : a = 1
  · simp [ha₁]
  have h₀ : kroneckerSym a 0 = 0 := by simp [kroneckerSym_zero_right, ha, ha₁]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [zero_mul, h₀, zero_mul]
  rcases eq_or_ne c 0 with rfl | hc
  · rw [mul_zero, h₀, mul_zero]
  exact kroneckerSym_mul_right a hb hc

/-- The Kronecker symbol of a power is the power of the symbol. Unlike multiplicativity, this holds
without restriction: at `b = 0` the value `(a / 0) ∈ {0, 1}` is idempotent. -/
theorem kroneckerSym_pow_right (a b : ℤ) (k : ℕ) :
    kroneckerSym a (b ^ k) = kroneckerSym a b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_ne b 0 with rfl | hb
    · rw [zero_pow k.succ_ne_zero, kroneckerSym_zero_right]
      split_ifs <;> simp
    · rw [pow_succ, kroneckerSym_mul_right a (pow_ne_zero k hb) hb, ih, pow_succ]

/-! ### Vanishing and the values `0`, `1`, `-1` -/

/-- The Kronecker symbol `(a / b)` vanishes exactly when `a` and `b` have a common factor, as for
`jacobiSym.eq_zero_iff`. At `b = 0` this says that `(a / 0) ≠ 0` exactly for `a = ±1`. -/
theorem kroneckerSym_eq_zero_iff {a b : ℤ} : kroneckerSym a b = 0 ↔ a.gcd b ≠ 1 := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [kroneckerSym_zero_right, Int.gcd_zero_right, Ne, Int.natAbs_eq_iff, Nat.cast_one]
    split_ifs <;> simp_all
  have hm : ordCompl[2] b.natAbs ≠ 0 := (Nat.ordCompl_pos 2 (Int.natAbs_ne_zero.mpr hb)).ne'
  have hs : (if a < 0 ∧ b < 0 then -1 else 1 : ℤ) ≠ 0 := by split_ifs <;> norm_num
  -- Writing `|b| = 2 ^ e * m` with `m` odd, `a` and `b` have a common factor exactly when `a` is
  -- even and `e ≠ 0`, or `a` and `m` have one.
  rw [kroneckerSym_of_ne_zero a hb, Int.gcd_eq_natAbs_gcd_natAbs, Ne,
    ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_coprime_ordCompl Nat.prime_two]
  simp only [mul_eq_zero, hs, false_or, pow_eq_zero_iff', χ₈_intCast_eq_zero_iff,
    jacobiSym.eq_zero_iff, Ne, hm, not_false_eq_true, true_and, Int.gcd_eq_natAbs_gcd_natAbs,
    Int.natAbs_natCast, not_and_or, not_imp, Nat.coprime_iff_gcd_eq_one, ← Int.natCast_dvd,
    Nat.cast_ofNat]

/-- `(0 / b)` is `1` for `b = ±1` and `0` otherwise. -/
@[simp]
theorem kroneckerSym_zero_left (b : ℤ) : kroneckerSym 0 b = if b = 1 ∨ b = -1 then 1 else 0 := by
  by_cases hb : b = 1 ∨ b = -1
  · rcases hb with rfl | rfl <;> simp
  · rw [ite_eq_right hb, kroneckerSym_eq_zero_iff, Int.gcd_zero_left]
    omega

/-- The Kronecker symbol takes only the values `0`, `1` and `-1`. -/
theorem kroneckerSym_trichotomy (a b : ℤ) :
    kroneckerSym a b = 0 ∨ kroneckerSym a b = 1 ∨ kroneckerSym a b = -1 := by
  rw [← Int.abs_le_one_iff]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [kroneckerSym_zero_right]
    split_ifs <;> simp
  have hs : |(if a < 0 ∧ b < 0 then -1 else 1 : ℤ)| ≤ 1 := by split_ifs <;> simp
  have h₈ : |(χ₈ a : ℤ)| ≤ 1 := Int.abs_le_one_iff.mpr (isQuadratic_χ₈ a)
  have hJ : |jacobiSym a (ordCompl[2] b.natAbs)| ≤ 1 :=
    Int.abs_le_one_iff.mpr (jacobiSym.trichotomy _ _)
  have hmul (x y : ℤ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg x, abs_nonneg y]
  rw [kroneckerSym_of_ne_zero a hb]
  exact hmul _ _ (hmul _ _ hs (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h₈)) hJ

/-! ### Multiplicativity in the numerator -/

/-- Multiplicativity of the Kronecker symbol in the numerator, over nonzero factors, as in
`jacobiSym.mul_left`. The hypotheses cannot be dropped: for `a = 0`, `a' = -1`, `b = -1` the left
side is `(0 / -1) = 1` and the right side is `-1` (`kroneckerSym_neg_one_right`). -/
theorem kroneckerSym_mul_left {a a' : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0) (b : ℤ) :
    kroneckerSym (a * a') b = kroneckerSym a b * kroneckerSym a' b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [kroneckerSym_zero_right, ← Int.isUnit_iff, IsUnit.mul_iff]
    split_ifs <;> simp_all
  have hs : (if a * a' < 0 ∧ b < 0 then -1 else 1 : ℤ) =
      (if a < 0 ∧ b < 0 then -1 else 1) * (if a' < 0 ∧ b < 0 then -1 else 1) := by
    simpa only [and_comm] using Int.ite_and_mul_lt_zero (p := b < 0) ha ha'
  rw [kroneckerSym_of_ne_zero _ hb, kroneckerSym_of_ne_zero a hb, kroneckerSym_of_ne_zero a' hb,
    Int.cast_mul, map_mul, mul_pow, jacobiSym.mul_left, hs]
  ring

/-! ### The Kronecker symbol of a discriminant -/

/-- A discriminant `D ≡ 0, 1 (mod 4)` is not `-1`, so `(D / ·)` is completely multiplicative
(`kroneckerSym_mul_right_of_ne_neg_one`). -/
private theorem ne_neg_one_of_modEq_four {D : ℤ} (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) :
    D ≠ -1 := by
  rintro rfl
  rcases hD with h | h <;> revert h <;> decide

/-- For `D ≡ 1 (mod 4)`, the Kronecker symbol `(D / n)` is the Jacobi symbol `J(n | |D|)`, for every
integer `n`. At odd `n > 0` this is quadratic reciprocity, at `n = 2` the supplementary law
`χ₈ D = J(2 | |D|)`, and at `n = -1` the supplementary law `sign D = J(-1 | |D|)`. In particular
`(D / ·)` is periodic modulo `|D|`. -/
theorem kroneckerSym_eq_jacobiSym_natAbs {D : ℤ} (hD : D ≡ 1 [ZMOD 4]) (n : ℤ) :
    kroneckerSym D n = jacobiSym n D.natAbs := by
  have hD4 : D % 4 = 1 := hD.eq.trans (by norm_num)
  have hD1 : D ≠ -1 := ne_neg_one_of_modEq_four (.inr hD)
  have hodd : Odd D.natAbs := Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))
  have hnat (k : ℕ) : kroneckerSym D k = jacobiSym k D.natAbs := by
    rcases eq_or_ne k 0 with rfl | hk
    · rw [Nat.cast_zero, kroneckerSym_zero_right]
      by_cases h1 : D = 1
      · simp [h1]
      · rw [ite_eq_right (by omega), jacobiSym.zero_left (by omega)]
    obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
    push_cast
    -- Both sides split as the factor at `2 ^ e` times the factor at `m`; reciprocity matches the
    -- factors at `m`, and the supplementary law `J(2 | |D|) = χ₈ |D|` those at `2 ^ e`.
    rw [kroneckerSym_mul_right_of_ne_neg_one hD1, kroneckerSym_pow_right, kroneckerSym_two_right,
      kroneckerSym_eq_jacobiSym _ hm, jacobiSym_eq_jacobiSym_natAbs_of_emod_four_eq_one hD4 hm]
    simp only [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two hodd]
    congr 2
    have habs : ((D.natAbs : ℕ) : ZMod 8) = ((|D| : ℤ) : ZMod 8) := by
      rw [← Int.natCast_natAbs, Int.cast_natCast]
    rw [habs]
    rcases abs_choice D with h | h <;> rw [h]
    rw [Int.cast_neg, χ₈_neg]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact hnat k
  · rw [neg_eq_neg_one_mul, kroneckerSym_mul_right_of_ne_neg_one hD1, kroneckerSym_neg_one_right,
      hnat, jacobiSym.mul_left, jacobiSym.at_neg_one hodd]
    congr 1
    rcases Int.natAbs_eq D with h | h
    · rw [ite_eq_right (by omega), χ₄_nat_one_mod_four (by omega)]
    · rw [ite_eq_left (by omega), χ₄_nat_three_mod_four (by omega)]

/-- For `D ≡ 0 (mod 4)` and odd `m`, the Kronecker symbol `(D / m)` is the Jacobi symbol at the
least nonnegative residue of `m` modulo `D`. For `m < 0` this is the reflection law
`jacobiSym_eq_sign_mul_of_emod_four_eq_zero`. -/
private theorem kroneckerSym_eq_jacobiSym_emod {D : ℤ} (hD : D % 4 = 0) (hD₀ : D ≠ 0) {m : ℤ}
    (hm : Odd m) : kroneckerSym D m = jacobiSym D (m % D).toNat := by
  have hr₀ : 0 ≤ m % D := Int.emod_nonneg m hD₀
  have hr : Odd (m % D).toNat := by
    have h2 : Even D := even_iff_two_dvd.mpr (dvd_trans (by norm_num) (Int.dvd_of_emod_eq_zero hD))
    rw [← Int.odd_coe_nat, Int.toNat_of_nonneg hr₀, Int.emod_def]
    exact hm.sub_even (h2.mul_right _)
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · have hk : Odd k := (Int.odd_coe_nat k).mp hm
    have hmod : ((k : ℤ) % D).toNat = k % D.natAbs := by
      rw [← Int.emod_abs, ← Int.natCast_natAbs, ← Int.natCast_mod, Int.toNat_natCast]
    rw [kroneckerSym_eq_jacobiSym D hk, jacobiSym_mod_natAbs_of_emod_four_eq_zero hD hk, hmod,
      jacobiSym_mod_natAbs_of_emod_four_eq_zero hD (hmod ▸ hr), Nat.mod_mod]
  · have hk : Odd k := (Int.odd_coe_nat k).mp (by simpa using hm)
    have hdvd : D.natAbs ∣ k + (-(k : ℤ) % D).toNat := by
      rw [← Int.natCast_dvd_natCast, Nat.cast_add, Int.toNat_of_nonneg hr₀, Int.natCast_natAbs,
        abs_dvd, Int.emod_def]
      exact ⟨-(-(k : ℤ) / D), by ring⟩
    have hk₀ : -(k : ℤ) < 0 := by have := hk.pos; omega
    rw [kroneckerSym_of_odd D hm, Int.natAbs_neg, Int.natAbs_natCast,
      jacobiSym_eq_sign_mul_of_emod_four_eq_zero hD hk hr hdvd]
    simp only [hk₀, and_true, Int.ite_lt_zero_eq_sign hD₀]

private theorem kroneckerSym_eq_zero_of_two_dvd {D m : ℤ} (hD : 2 ∣ D) (hm : 2 ∣ m) :
    kroneckerSym D m = 0 :=
  kroneckerSym_eq_zero_iff.mpr fun h ↦ by
    have := Int.dvd_gcd hD hm
    rw [h] at this
    norm_num at this

/-- For a discriminant `D ≡ 0, 1 (mod 4)`, the Kronecker symbol `(D / ·)` is periodic modulo `D`. -/
theorem kroneckerSym_mod_right' {D : ℤ} (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) {m n : ℤ}
    (h : m % D = n % D) : kroneckerSym D m = kroneckerSym D n := by
  rcases hD with hD | hD
  · have hD4 : D % 4 = 0 := hD.eq.trans (Int.zero_emod 4)
    rcases eq_or_ne D 0 with rfl | hD₀
    · rw [Int.emod_zero, Int.emod_zero] at h
      rw [h]
    have h2 : (2 : ℤ) ∣ D := dvd_trans (by norm_num) (Int.dvd_of_emod_eq_zero hD4)
    have hmn : m % 2 = n % 2 := by
      rw [← Int.emod_emod_of_dvd m h2, h, Int.emod_emod_of_dvd n h2]
    by_cases hm : Odd m
    · have hn : Odd n := Int.odd_iff.mpr (hmn ▸ Int.odd_iff.mp hm)
      rw [kroneckerSym_eq_jacobiSym_emod hD4 hD₀ hm, kroneckerSym_eq_jacobiSym_emod hD4 hD₀ hn, h]
    · have hm' : 2 ∣ m := even_iff_two_dvd.mp (Int.not_odd_iff_even.mp hm)
      have hn' : 2 ∣ n := Int.dvd_iff_emod_eq_zero.mpr (hmn ▸ Int.emod_eq_zero_of_dvd hm')
      rw [kroneckerSym_eq_zero_of_two_dvd h2 hm', kroneckerSym_eq_zero_of_two_dvd h2 hn']
  · rw [kroneckerSym_eq_jacobiSym_natAbs hD, kroneckerSym_eq_jacobiSym_natAbs hD]
    exact jacobiSym.mod_left' (by rwa [Int.natCast_natAbs, Int.emod_abs, Int.emod_abs])

/-- For a discriminant `D ≡ 0, 1 (mod 4)`, `(D / n) = (D / (n % D))`. -/
theorem kroneckerSym_mod_right {D : ℤ} (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (n : ℤ) :
    kroneckerSym D n = kroneckerSym D (n % D) :=
  kroneckerSym_mod_right' hD (Int.emod_emod n D).symm

/-! ### The Kronecker character of a discriminant -/

section KroneckerChar

variable (R : Type*) [CommRing R] {D : ℤ}

private theorem kroneckerSym_val (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) [NeZero D.natAbs]
    {x : ZMod D.natAbs} {a : ℤ} (hx : (a : ZMod D.natAbs) = x) :
    kroneckerSym D x.val = kroneckerSym D a := by
  refine kroneckerSym_mod_right' hD ?_
  have h := (ZMod.intCast_eq_intCast_iff _ _ _).mp
    (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, hx] : ((x.val : ℤ) : ZMod D.natAbs) = a)
  rwa [Int.ModEq, Int.natCast_natAbs, Int.emod_abs, Int.emod_abs] at h

/-- The **Kronecker character** of a discriminant `D ≡ 0, 1 (mod 4)`, `D ≠ 0`: the Dirichlet
character `(D / ·)` of modulus `|D|`, with values in a commutative ring `R`. It is well defined
because `(D / ·)` is periodic modulo `|D|` (`kroneckerSym_mod_right'`) and multiplicative
(`kroneckerSym_mul_right_of_ne_neg_one`, as `D ≠ -1`), and it vanishes off the units because
`(D / n) = 0` when `gcd (D, n) ≠ 1` (`kroneckerSym_eq_zero_iff`). It need not be primitive. -/
def kroneckerChar (D : ℤ) (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD₀ : D ≠ 0) :
    DirichletCharacter R D.natAbs :=
  haveI : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD₀⟩
  { toFun x := (kroneckerSym D x.val : R)
    map_one' := by
      rw [kroneckerSym_val hD Int.cast_one, kroneckerSym_one_right, Int.cast_one]
    map_mul' x y := by
      rw [kroneckerSym_val hD (a := x.val * y.val) (by push_cast; simp),
        kroneckerSym_mul_right_of_ne_neg_one (ne_neg_one_of_modEq_four hD), Int.cast_mul]
    map_nonunit' x hx := by
      rw [kroneckerSym_eq_zero_iff.mpr, Int.cast_zero]
      intro h
      refine hx ?_
      rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
      rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] at h
      exact (Nat.coprime_iff_gcd_eq_one.mpr h).symm }

variable {R} (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD₀ : D ≠ 0)

/-- The Kronecker character at `x : ZMod |D|` is the Kronecker symbol `(D / x.val)`, by
definition. -/
theorem kroneckerChar_apply (x : ZMod D.natAbs) :
    kroneckerChar R D hD hD₀ x = kroneckerSym D x.val := by
  rfl

/-- The Kronecker character at the class of an integer `a` is the Kronecker symbol `(D / a)`. -/
@[simp]
theorem kroneckerChar_intCast (a : ℤ) : kroneckerChar R D hD hD₀ a = kroneckerSym D a := by
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD₀⟩
  rw [kroneckerChar_apply]
  exact congrArg (Int.cast : ℤ → R) (kroneckerSym_val hD rfl)

/-- The Kronecker character at the class of a natural number `n` is the Kronecker symbol
`(D / n)`. -/
@[simp]
theorem kroneckerChar_natCast (n : ℕ) : kroneckerChar R D hD hD₀ n = kroneckerSym D n := by
  rw [← kroneckerChar_intCast hD hD₀, Int.cast_natCast]

/-- The Kronecker character is quadratic: it takes only the values `0`, `1` and `-1`. -/
theorem kroneckerChar_isQuadratic : (kroneckerChar R D hD hD₀).IsQuadratic := by
  intro x
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [kroneckerChar_intCast]
  rcases kroneckerSym_trichotomy D a with h | h | h <;> simp [h]

/-- The Kronecker character takes the value `sign D` at `-1`: it is even for `D > 0` and odd for
`D < 0`. -/
@[simp]
theorem kroneckerChar_neg_one : kroneckerChar R D hD hD₀ (-1) = D.sign := by
  rw [← Int.cast_one (R := ZMod D.natAbs), ← Int.cast_neg, kroneckerChar_intCast,
    kroneckerSym_neg_one_right, Int.ite_lt_zero_eq_sign hD₀]

end KroneckerChar

end TauCeti
