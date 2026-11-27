/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Natural-number congruences

Two distinct residues `a, b < p` never differ by a multiple of `p`: if `b ≤ p * m + a`, so that
the natural subtraction does not truncate, the difference `p * m + a - b` is not divisible by `p`.
This is the arithmetic behind the uniqueness of the decomposition of an exponent as `p • μ + ν`
with `ν i < p`. Likewise, since `(p - 1) a ≡ -a` modulo `p`, two residues `a, b < p` with
`p ∣ (p - 1) a + b` are equal.

## Main results

* `Nat.not_dvd_mul_add_sub`: for distinct `a, b < p` with `b ≤ p * m + a`, `p` does not divide
  `p * m + a - b`.
* `Nat.eq_of_dvd_sub_one_mul_add`: for residues `a, b < p`, `p ∣ (p - 1) * a + b` forces `b = a`.
* `Nat.modEq_div_two_sub_one_iff`: for even `q ≠ 0`, `d ≡ q / 2 - 1 (mod q)` if and only if
  `q ∣ 2 (d + 1)` and `q ∤ d + 1`.
* `Nat.coprime_div_two_sub_one_iff`: for a positive even `q`, the class `q / 2 - 1` is reduced
  exactly when `4 ∣ q`.
* `Nat.div_two_sub_one_modEq_of_mul_dvd`: reduce that class modulo a divisor of `q / 2`.
* `TauCeti.sq_sub_one_eq_four_mul_of_mod_four_eq_three`: for `q ≡ 3 (mod 4)`, factor `q² - 1`
  with the factor `4` made explicit.
-/

public section

namespace Nat

/-- Two distinct residues modulo `p` do not differ by a multiple of `p`. -/
theorem not_dvd_mul_add_sub {p m a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b)
    (hle : b ≤ p * m + a) : ¬ p ∣ p * m + a - b := by
  intro h
  have h' : b ≡ p * m + a [MOD p] := (modEq_iff_dvd' hle).mpr h
  have h'' : b ≡ a [MOD p] := h'.trans (by simp [ModEq])
  exact hab (ModEq.eq_of_lt_of_lt h''.symm ha hb)

/-- Two residues `a, b < p` with `p ∣ (p - 1) * a + b` are equal, since `(p - 1) * a ≡ -a`
modulo `p`. -/
theorem eq_of_dvd_sub_one_mul_add {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : p ∣ (p - 1) * a + b) : b = a := by
  obtain ⟨q, hq⟩ := h
  have hab : p * a + b = p * q + a := by
    rw [← hq, add_right_comm, ← add_one_mul, Nat.sub_add_cancel (by omega)]
  have := congrArg (· % p) hab
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-- For an even `q ≠ 0`, `d ≡ q / 2 - 1 (mod q)` holds exactly when `q` divides `2 (d + 1)` but
not `d + 1`. -/
theorem modEq_div_two_sub_one_iff {q d : ℕ} (hq : Even q) (hq₀ : q ≠ 0) :
    d ≡ q / 2 - 1 [MOD q] ↔ q ∣ 2 * (d + 1) ∧ ¬ q ∣ d + 1 := by
  obtain ⟨m, rfl⟩ := hq
  have hm : (m + m) / 2 - 1 + 1 = m := by omega
  have hr : (d + 1) % (m + m) < m + m := Nat.mod_lt _ (by omega)
  have hn : d + 1 = (d + 1) % (m + m) + (m + m) * ((d + 1) / (m + m)) :=
    (Nat.mod_add_div _ _).symm
  generalize (d + 1) % (m + m) = r at hr hn
  generalize (d + 1) / (m + m) = k at hn
  have h₁ : m + m ∣ d + 1 ↔ r = 0 := by
    rw [hn, Nat.dvd_add_left (dvd_mul_right _ _)]
    exact ⟨fun h ↦ Nat.eq_zero_of_dvd_of_lt h hr, fun h ↦ h ▸ dvd_zero _⟩
  have h₂ : m + m ∣ 2 * (d + 1) ↔ r = 0 ∨ r = m := by
    -- split off the multiple `(m + m) * (2 * k)` of the modulus, so that only `2 * r` is left
    rw [hn, show 2 * (r + (m + m) * k) = 2 * r + (m + m) * (2 * k) by ring,
      Nat.dvd_add_left (dvd_mul_right _ _)]
    constructor
    · rintro ⟨j, hj⟩
      have hj₂ : j < 2 := Nat.lt_of_mul_lt_mul_left (a := m + m) (by omega)
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> omega
    · rintro (rfl | rfl)
      exacts [dvd_zero _, ⟨1, by ring⟩]
  have h₃ : d ≡ (m + m) / 2 - 1 [MOD m + m] ↔ d + 1 ≡ m [MOD m + m] := by
    constructor
    · intro h
      simpa only [hm] using h.add_right 1
    · intro h
      exact Nat.ModEq.add_right_cancel' 1 (by rwa [hm])
  rw [h₃, h₁, h₂, Nat.ModEq, Nat.mod_eq_of_lt (by omega : m < m + m), hn,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  omega

/-- For a positive even modulus `q`, the residue `q / 2 - 1` is prime to `q` exactly when
`q` is divisible by four. -/
theorem coprime_div_two_sub_one_iff {q : ℕ} (hq : Even q) (hq₀ : q ≠ 0) :
    (q / 2 - 1).Coprime q ↔ 4 ∣ q := by
  obtain ⟨m, rfl⟩ := hq
  have hdiv : (m + m) / 2 = m := by omega
  have hpos : 1 ≤ m := by omega
  have hc : (m - 1).Coprime m := (coprime_self_sub_left hpos).2 (by simp)
  rw [hdiv, ← two_mul, coprime_mul_iff_right, and_iff_left hc, coprime_two_right, odd_iff]
  omega

/-- If `2m` divides the positive modulus `q`, its residue `q / 2 - 1` reduces to `m - 1`
modulo `m`. -/
theorem div_two_sub_one_modEq_of_mul_dvd {q m : ℕ} (hq : q ≠ 0) (hm : 2 * m ∣ q) :
    q / 2 - 1 ≡ m - 1 [MOD m] := by
  obtain ⟨k, hk⟩ := hm
  have hpos : 0 < m ∧ 0 < k := by
    simpa [hk, mul_ne_zero_iff, Nat.pos_iff_ne_zero] using hq
  have hdiv : q / 2 = m * k := by rw [hk, mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.2.ne'
  rw [hdiv, Nat.mul_succ, Nat.add_sub_assoc hpos.1]
  simp [Nat.ModEq]

end Nat

namespace TauCeti

/-- For `q ≡ 3 (mod 4)`, factor `q² - 1` with the factor `4` made explicit. -/
theorem sq_sub_one_eq_four_mul_of_mod_four_eq_three {q : ℕ} (hq : q % 4 = 3) :
    q ^ 2 - 1 = (4 * (q - 1)) * ((q + 1) / 4) := by
  rw [← Nat.one_pow 2, Nat.sq_sub_sq, Nat.one_pow]
  have h4 : 4 ∣ q + 1 := by omega
  calc
    (q + 1) * (q - 1) = (4 * ((q + 1) / 4)) * (q - 1) := by
      rw [Nat.mul_div_cancel' h4]
    _ = (4 * (q - 1)) * ((q + 1) / 4) := by ring

end TauCeti
