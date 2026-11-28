/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.Complex.Basic
import TauCeti.Algebra.Ring.Int.Parity
import TauCeti.NumberTheory.LegendreSymbol.ZModChar

/-!
# Shimura's theta multiplier phase factor `ε_d`

Defines Shimura's fourth-root-of-unity phase factor `TauCeti.thetaMultiplierPhase d` (`ε_d`), equal
to `1` for `d ≡ 1 (mod 4)`, `I` for `d ≡ 3 (mod 4)`, and `0` for even `d`, together with its
arithmetic properties (`ε_d ^ 2 = χ₄(d)`, `ε_d ^ 4 = 1` for odd `d`, inversion, conjugation, and
negation).

## Main definitions

* `TauCeti.thetaMultiplierPhase`: Shimura's fourth-root-of-unity phase `ε_d` for odd `d`, equal to
  `1` for `d ≡ 1 (mod 4)` and `I` for `d ≡ 3 (mod 4)`, extended by `0` for even `d`.

## Main results

* `TauCeti.thetaMultiplierPhase_sq`, `TauCeti.thetaMultiplierPhase_pow_four`:
  `thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ)` for every `d : ℤ`, and
  `thetaMultiplierPhase d ^ 4 = 1` for odd `d`.
* `TauCeti.thetaMultiplierPhase_neg`, `TauCeti.star_thetaMultiplierPhase`,
  `TauCeti.thetaMultiplierPhase_mul_neg`: negation, conjugation, and sign-product identities.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. (2) **97** (1973),
  440–481, (1.10)–(1.11).
-/

public section

open Complex

namespace TauCeti

/-- Shimura's phase factor `ε_d`, a fourth root of unity for odd `d` (`1` for `d ≡ 1 (mod 4)`, `I`
for `d ≡ 3 (mod 4)`) extended by `0` for even `d`, appearing in the transformation law of `θ(2 τ)`
under `Γ₀(4)`. -/
noncomputable def thetaMultiplierPhase (d : ℤ) : ℂ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0

/-- Defining formula for `thetaMultiplierPhase`. -/
theorem thetaMultiplierPhase_def (d : ℤ) :
    thetaMultiplierPhase d = if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0 := (rfl)

/-- For `d ≡ 1 (mod 4)`, `thetaMultiplierPhase d = 1`. -/
theorem thetaMultiplierPhase_one_mod_four {d : ℤ} (hd : d % 4 = 1) :
    thetaMultiplierPhase d = 1 := by
  rw [thetaMultiplierPhase_def, ite_eq_left hd]

/-- For `d ≡ 3 (mod 4)`, `thetaMultiplierPhase d = I`. -/
theorem thetaMultiplierPhase_three_mod_four {d : ℤ} (hd : d % 4 = 3) :
    thetaMultiplierPhase d = I := by
  rw [thetaMultiplierPhase_def, ite_eq_right (by omega), ite_eq_left hd]

/-- For even `d`, `thetaMultiplierPhase d = 0`. -/
theorem thetaMultiplierPhase_eq_zero_of_even {d : ℤ} (hd : Even d) :
    thetaMultiplierPhase d = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [thetaMultiplierPhase_def, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- `thetaMultiplierPhase d = 0` if and only if `d` is even. -/
@[simp]
theorem thetaMultiplierPhase_eq_zero_iff (d : ℤ) : thetaMultiplierPhase d = 0 ↔ Even d := by
  refine ⟨fun h ↦ ?_, thetaMultiplierPhase_eq_zero_of_even⟩
  by_contra hodd
  rcases Int.emod_four_eq_one_or_three_of_odd (Int.not_even_iff_odd.mp hodd) with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm] at h
    exact one_ne_zero h
  · rw [thetaMultiplierPhase_three_mod_four hm] at h
    exact I_ne_zero h

/-- For odd `d`, `thetaMultiplierPhase d ≠ 0`. -/
theorem thetaMultiplierPhase_ne_zero {d : ℤ} (hd : Odd d) : thetaMultiplierPhase d ≠ 0 := by
  rw [ne_eq, thetaMultiplierPhase_eq_zero_iff]
  exact Int.not_even_iff_odd.mpr hd

@[simp]
theorem thetaMultiplierPhase_zero : thetaMultiplierPhase 0 = 0 :=
  thetaMultiplierPhase_eq_zero_of_even ⟨0, rfl⟩

@[simp]
theorem thetaMultiplierPhase_one : thetaMultiplierPhase 1 = 1 :=
  thetaMultiplierPhase_one_mod_four (by norm_num)

@[simp]
theorem thetaMultiplierPhase_neg_one : thetaMultiplierPhase (-1) = I :=
  thetaMultiplierPhase_three_mod_four (by norm_num)

/-- `thetaMultiplierPhase` depends only on the residue class modulo `4`. -/
theorem thetaMultiplierPhase_congr {d d' : ℤ} (h : d ≡ d' [ZMOD 4]) :
    thetaMultiplierPhase d = thetaMultiplierPhase d' := by
  simp only [thetaMultiplierPhase_def, Int.ModEq] at h ⊢
  rw [h]

/-- `thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ)` for every integer `d`. -/
@[simp]
theorem thetaMultiplierPhase_sq (d : ℤ) : thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ) := by
  rw [ZMod.χ₄_int_eq_if_mod_four]
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaMultiplierPhase_eq_zero_of_even hd, zero_pow two_ne_zero,
      ite_eq_left (by obtain ⟨k, rfl⟩ := hd; omega), Int.cast_zero]
  · have hne : d % 2 ≠ 0 := by
      obtain ⟨k, rfl⟩ := hd
      omega
    rw [ite_eq_right hne]
    rcases Int.emod_four_eq_one_or_three_of_odd hd with hm | hm
    · rw [thetaMultiplierPhase_one_mod_four hm, ite_eq_left hm]
      norm_num
    · rw [thetaMultiplierPhase_three_mod_four hm, ite_eq_right (by omega)]
      norm_num

/-- For odd `d`, `thetaMultiplierPhase d ^ 4 = 1`. -/
@[simp]
theorem thetaMultiplierPhase_pow_four {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase d ^ 4 = 1 := by
  calc thetaMultiplierPhase d ^ 4
      = (thetaMultiplierPhase d ^ 2) ^ 2 := by ring
    _ = 1 := by rw [thetaMultiplierPhase_sq]; exact_mod_cast ZMod.χ₄_intCast_sq hd

/-- For odd `d`, `‖thetaMultiplierPhase d‖ = 1`. -/
theorem norm_thetaMultiplierPhase {d : ℤ} (hd : Odd d) : ‖thetaMultiplierPhase d‖ = 1 := by
  rcases Int.emod_four_eq_one_or_three_of_odd hd with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, norm_one]
  · rw [thetaMultiplierPhase_three_mod_four hm, norm_I]

/-- For odd `d`, `(thetaMultiplierPhase d)⁻¹ = if d % 4 = 1 then 1 else -I`. -/
theorem thetaMultiplierPhase_inv {d : ℤ} (hd : Odd d) :
    (thetaMultiplierPhase d)⁻¹ = if d % 4 = 1 then 1 else -I := by
  rcases Int.emod_four_eq_one_or_three_of_odd hd with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, ite_eq_left hm, inv_one]
  · rw [thetaMultiplierPhase_three_mod_four hm, ite_eq_right (by omega), inv_I]

/-- Negating the integer parameter gives
`thetaMultiplierPhase (-d) = I * star (thetaMultiplierPhase d)` for every `d : ℤ` (both sides
vanish when `d` is even). -/
theorem thetaMultiplierPhase_neg (d : ℤ) :
    thetaMultiplierPhase (-d) = I * star (thetaMultiplierPhase d) := by
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaMultiplierPhase_eq_zero_of_even hd.neg, thetaMultiplierPhase_eq_zero_of_even hd,
      star_zero, mul_zero]
  · rcases Int.emod_four_eq_one_or_three_of_odd hd with hm | hm
    · rw [thetaMultiplierPhase_three_mod_four (by omega), thetaMultiplierPhase_one_mod_four hm,
        star_one, mul_one]
    · rw [thetaMultiplierPhase_one_mod_four (by omega), thetaMultiplierPhase_three_mod_four hm,
        Complex.star_def, conj_I, mul_neg, I_mul_I, neg_neg]

/-- Conjugation equals inversion on `thetaMultiplierPhase d` for every integer `d` (both sides
vanish when `d` is even, and `‖thetaMultiplierPhase d‖ = 1` when `d` is odd). -/
theorem star_thetaMultiplierPhase (d : ℤ) :
    star (thetaMultiplierPhase d) = (thetaMultiplierPhase d)⁻¹ := by
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaMultiplierPhase_eq_zero_of_even hd, star_zero, inv_zero]
  · rw [Complex.star_def]
    exact (Complex.inv_eq_conj (norm_thetaMultiplierPhase hd)).symm

/-- For odd `d`, `thetaMultiplierPhase d * thetaMultiplierPhase (-d) = I`. -/
theorem thetaMultiplierPhase_mul_neg {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase d * thetaMultiplierPhase (-d) = I := by
  rw [thetaMultiplierPhase_neg, star_thetaMultiplierPhase, mul_left_comm,
    mul_inv_cancel₀ (thetaMultiplierPhase_ne_zero hd), mul_one]

end TauCeti
