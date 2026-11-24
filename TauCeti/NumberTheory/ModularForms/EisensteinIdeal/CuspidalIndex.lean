/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# The cuspidal index of prime level

For a prime `P`, Mazur's index `n` is the numerator of `(P - 1) / 12` in lowest terms,
`n = (P - 1) / gcd(P - 1, 12)`. Mazur proved that the Eisenstein quotient `T/I` of the
weight-two Hecke algebra of level `P` is `ℤ/n`, and that `n` is the exact order of the cuspidal
divisor class `[0] - [∞]` in the Jacobian of `X₀(P)`; those theorems are not proved here.

This file defines `TauCeti.cuspidalIndex P` as `(P - 1) / gcd(P - 1, 12)` and proves the
arithmetic facts used about it:

* `TauCeti.cuspidalIndex_mul_gcd`: `n * gcd(P - 1, 12) = P - 1`, so `n` divides `P - 1`
  (`TauCeti.cuspidalIndex_dvd_sub_one`);
* `TauCeti.cuspidalIndex_pos_iff`: `n` is positive exactly when `1 < P`;
* `TauCeti.num_natCast_sub_one_div_twelve` and `TauCeti.den_natCast_sub_one_div_twelve`:
  `n` is the numerator of the reduced rational `(P - 1) / 12`, whose denominator is
  `12 / gcd(P - 1, 12)`;
* `TauCeti.cuspidalIndex_eq_one_iff_of_prime`: for prime `P`, `n = 1` exactly at the five
  genus-zero levels `P = 2, 3, 5, 7, 13`, and `TauCeti.one_lt_cuspidalIndex_iff_of_prime`
  gives the complementary inequality `1 < n`.

For example `n = 5` at `P = 11` (not `10`), `n = 4` at `P = 17`, and `n = 1` at `P = 13`.

## References

* B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977),
  Introduction, Theorem (1), and II §11.
-/

public section

namespace TauCeti

/-- The cuspidal index of level `P`, `(P - 1) / gcd(P - 1, 12)`: the numerator of the reduced
rational `(P - 1) / 12` (see `TauCeti.num_natCast_sub_one_div_twelve`). For prime `P` this is
Mazur's integer `n`; Mazur proved that it is the order of the Eisenstein quotient `T/I` and of
the cuspidal class `[0] - [∞]`. -/
def cuspidalIndex (P : ℕ) : ℕ :=
  (P - 1) / (P - 1).gcd 12

/-- Unfolding lemma for `TauCeti.cuspidalIndex`. -/
theorem cuspidalIndex_def (P : ℕ) : cuspidalIndex P = (P - 1) / (P - 1).gcd 12 := (rfl)

/-- The cuspidal index times `gcd(P - 1, 12)` is `P - 1`. -/
theorem cuspidalIndex_mul_gcd (P : ℕ) : cuspidalIndex P * (P - 1).gcd 12 = P - 1 :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)

/-- The cuspidal index divides `P - 1`. -/
theorem cuspidalIndex_dvd_sub_one (P : ℕ) : cuspidalIndex P ∣ P - 1 :=
  Dvd.intro _ (cuspidalIndex_mul_gcd P)

/-- The cuspidal index is positive exactly when `1 < P`; at `P = 0, 1` it is `0`. -/
theorem cuspidalIndex_pos_iff {P : ℕ} : 0 < cuspidalIndex P ↔ 1 < P := by
  rw [cuspidalIndex_def, Nat.div_pos_iff]
  constructor
  · rintro ⟨-, h⟩
    by_contra hP
    have hP0 : P - 1 = 0 := by omega
    simp [hP0] at h
  · intro hP
    exact ⟨Nat.gcd_pos_of_pos_right _ (by norm_num),
      Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)⟩

/-- The cuspidal index of a level `P > 1`, in particular of a prime level, is positive. -/
theorem cuspidalIndex_pos {P : ℕ} (hP : 1 < P) : 0 < cuspidalIndex P :=
  cuspidalIndex_pos_iff.mpr hP

/-- `(P - 1) / 12 = n / d` in `ℚ` for the coprime naturals `n = cuspidalIndex P` and
`d = 12 / gcd(P - 1, 12)`, with `0 < d`. -/
private theorem natCast_sub_one_div_twelve {P : ℕ} (hP : P ≠ 0) :
    ((P : ℚ) - 1) / 12 = (cuspidalIndex P : ℚ) / ((12 / (P - 1).gcd 12 : ℕ) : ℚ) ∧
      0 < 12 / (P - 1).gcd 12 ∧ (cuspidalIndex P).Coprime (12 / (P - 1).gcd 12) := by
  have hg : 0 < (P - 1).gcd 12 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  have h12 : ((12 / (P - 1).gcd 12 : ℕ) : ℚ) * (P - 1).gcd 12 = 12 := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right (P - 1) 12)
  have hP1 : ((P : ℚ) - 1) = cuspidalIndex P * (P - 1).gcd 12 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hP)]
    exact_mod_cast (cuspidalIndex_mul_gcd P).symm
  refine ⟨?_, Nat.div_pos (Nat.gcd_le_right _ (by norm_num)) hg, ?_⟩
  · rw [hP1, ← h12, mul_div_mul_right _ _ (by exact_mod_cast hg.ne')]
  · rw [cuspidalIndex_def]
    exact Nat.coprime_div_gcd_div_gcd hg

/-- The numerator of the reduced rational `(P - 1) / 12` is the cuspidal index. -/
theorem num_natCast_sub_one_div_twelve {P : ℕ} (hP : P ≠ 0) :
    (((P : ℚ) - 1) / 12).num = cuspidalIndex P := by
  obtain ⟨h, hd, hcop⟩ := natCast_sub_one_div_twelve hP
  rw [h]
  generalize cuspidalIndex P = n at hcop ⊢
  generalize 12 / (P - 1).gcd 12 = d at hd hcop ⊢
  simpa using Rat.num_div_eq_of_coprime (a := n) (b := d) (by omega) (by simpa using hcop)

/-- The denominator of the reduced rational `(P - 1) / 12` is `12 / gcd(P - 1, 12)`. -/
theorem den_natCast_sub_one_div_twelve {P : ℕ} (hP : P ≠ 0) :
    (((P : ℚ) - 1) / 12).den = 12 / (P - 1).gcd 12 := by
  obtain ⟨h, hd, hcop⟩ := natCast_sub_one_div_twelve hP
  rw [h]
  generalize cuspidalIndex P = n at hcop ⊢
  generalize 12 / (P - 1).gcd 12 = d at hd hcop ⊢
  have := Rat.den_div_eq_of_coprime (a := n) (b := d) (by omega) (by simpa using hcop)
  exact_mod_cast (by simpa using this)

/-- The cuspidal index is `1` exactly when `P - 1` divides `12`. -/
theorem cuspidalIndex_eq_one_iff {P : ℕ} : cuspidalIndex P = 1 ↔ P - 1 ∣ 12 := by
  constructor
  · intro h
    have := cuspidalIndex_mul_gcd P
    rw [h, one_mul] at this
    exact this ▸ Nat.gcd_dvd_right _ _
  · intro h
    have hP : P - 1 ≠ 0 := by rintro hP; simp [hP] at h
    rw [cuspidalIndex_def, Nat.gcd_eq_left h, Nat.div_self (Nat.pos_of_ne_zero hP)]

/-- For prime `P`, the cuspidal index is `1` exactly at the five genus-zero levels
`2, 3, 5, 7, 13`. -/
theorem cuspidalIndex_eq_one_iff_of_prime {P : ℕ} (hP : P.Prime) :
    cuspidalIndex P = 1 ↔ P = 2 ∨ P = 3 ∨ P = 5 ∨ P = 7 ∨ P = 13 := by
  rw [cuspidalIndex_eq_one_iff]
  constructor
  · intro h
    have : P ≤ 13 := by have := Nat.le_of_dvd (by norm_num) h; omega
    -- Revert so that `interval_cases` substitutes each value into `hP` and `h`, which
    -- `norm_num` then decides together with the goal.
    revert hP h
    interval_cases P <;> norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> norm_num

/-- For prime `P` outside the five genus-zero levels `2, 3, 5, 7, 13`, the cuspidal index
exceeds `1`, and conversely. -/
theorem one_lt_cuspidalIndex_iff_of_prime {P : ℕ} (hP : P.Prime) :
    1 < cuspidalIndex P ↔ P ≠ 2 ∧ P ≠ 3 ∧ P ≠ 5 ∧ P ≠ 7 ∧ P ≠ 13 := by
  have hpos := cuspidalIndex_pos hP.one_lt
  have := cuspidalIndex_eq_one_iff_of_prime hP
  omega

example : cuspidalIndex 11 = 5 := by simp [cuspidalIndex_def]
example : cuspidalIndex 17 = 4 := by simp [cuspidalIndex_def]
example : cuspidalIndex 13 = 1 := by simp [cuspidalIndex_def]
example : cuspidalIndex 37 = 3 := by simp [cuspidalIndex_def]

end TauCeti
