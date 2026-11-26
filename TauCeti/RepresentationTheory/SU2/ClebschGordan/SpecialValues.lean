/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.ClebschGordan.Basic

/-!
# Special values of the Clebsch–Gordan coefficients

In several families of arguments only one index `z` contributes to Racah's sum for the
Clebsch–Gordan coefficient `(j₁ m₁ j₂ m₂ | j₁ j₂ j m)` (`TauCeti.SU2.clebschGordan`), which then
has a closed form. This file evaluates these families, in the conventions of Edmonds [Edmonds]:

* `TauCeti.SU2.clebschGordan_zero_right`: coupling with spin zero, `(j m 0 0 | j 0 j m) = 1`
  [Edmonds, (3.5.12)];
* `TauCeti.SU2.clebschGordan_spin_zero`: coupling to spin zero,
  `(j m j -m | j j 0 0) = (-1)^{j - m} / √(2j + 1)` [Edmonds, (3.5.13)];
* `TauCeti.SU2.clebschGordan_stretched`: the stretched coefficients `j = j₁ + j₂`, which are
  positive [Edmonds, p. 45];
* `TauCeti.SU2.clebschGordan_spinHalf`: `(j₁ m₁ ½ ½ | j₁ + ½, m) = √((j₁ + m + ½)/(2j₁ + 1))`;
* `TauCeti.SU2.clebschGordan_pos`: the **Condon–Shortley phase convention**
  `(j₁ j₁ j₂ (j - j₁) | j₁ j₂ j j) > 0` [Edmonds, (3.5.11)], which fixes the sign of each coupled
  basis.

## References

* [Edmonds] A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press,
  1957, §§3.5–3.6. Equation numbers and pages refer to the 1957 printing.

The statements follow the prior formalization lean-SFVK of B. J. Braams
(<https://github.com/bjbraams/lean-SFVK>, Apache-2.0), file `SFVK/ClebschGordan/Coefficients.lean`.
-/

public section

namespace TauCeti.SU2

open Finset

/-- **Coupling to spin zero** [Edmonds, (3.5.13)]:
`(j m j -m | j j 0 0) = (-1)^{j - m} / √(2j + 1)`. -/
theorem clebschGordan_spin_zero {d i : ℕ} (h : i ≤ d) :
    clebschGordan d d 0 i (d - i) 0 = (-1) ^ (d - i) / Real.sqrt (d + 1) := by
  rw [clebschGordan_eq_sqrt_mul_clebschGordanTerm (isTriad_iff.2 ⟨by omega, by omega, by omega,
      ⟨d, by omega⟩⟩) h (Nat.sub_le d i) le_rfl (by omega) (z₀ := d - i) (by omega)
      fun z _ _ ↦ clebschGordanTerm_eq_zero (by omega),
    clebschGordanPrefactor_eq (a := d) (b := 0) (c := 0) (s := d) (by omega) (by omega) (by omega)
      (by omega),
    clebschGordanTerm_eq (a := i) (b := 0) (c := 0) (e := 0) (f := 0) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
  simp only [Nat.sub_self, Nat.sub_sub_self h, zero_add, Nat.factorial_zero, mul_one, one_mul]
  rw [mul_div_left_comm, div_eq_mul_inv _ (Real.sqrt _), ← Real.sqrt_inv]
  congr 1
  rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), div_pow,
    Real.sq_sqrt (by positivity), Nat.factorial_succ]
  push_cast
  field_simp

/-- **The stretched coefficient** [Edmonds, p. 45]: for `j = j₁ + j₂`,
`(j₁ m₁ j₂ m₂ | j₁ j₂ j m)` is the positive square root of
`(2j₁)! (2j₂)! (j + m)! (j - m)! / ((2j)! (j₁ + m₁)! (j₁ - m₁)! (j₂ + m₂)! (j₂ - m₂)!)`. -/
theorem clebschGordan_stretched {d₁ d₂ i₁ i₂ : ℕ} (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂) :
    clebschGordan d₁ d₂ (d₁ + d₂) i₁ i₂ (i₁ + i₂) =
      Real.sqrt (((d₁.factorial * d₂.factorial * (i₁ + i₂).factorial *
          (d₁ + d₂ - (i₁ + i₂)).factorial : ℕ) : ℝ) /
        (((d₁ + d₂).factorial * i₁.factorial * (d₁ - i₁).factorial * i₂.factorial *
          (d₂ - i₂).factorial : ℕ) : ℝ)) := by
  rw [clebschGordan_eq_sqrt_mul_clebschGordanTerm (isTriad_add d₁ d₂) h₁ h₂ (by omega)
      (by omega) (z₀ := 0) (by omega)
      fun z _ _ ↦ clebschGordanTerm_eq_zero (by omega),
    clebschGordanPrefactor_eq (a := 0) (b := d₁) (c := d₂) (s := d₁ + d₂) (by omega) (by omega)
      (by omega) (by omega),
    clebschGordanTerm_eq (a := 0) (b := d₁ - i₁) (c := i₂) (e := i₁) (f := d₂ - i₂) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [Nat.factorial_zero, pow_zero, mul_one, one_mul]
  rw [mul_one_div, eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), div_pow,
    Real.sq_sqrt (by positivity), Nat.factorial_succ (d₁ + d₂)]
  push_cast
  field_simp

/-- **Coupling with spin zero** [Edmonds, (3.5.12)]: `(j m 0 0 | j 0 j m) = 1`. -/
theorem clebschGordan_zero_right {d i : ℕ} (h : i ≤ d) : clebschGordan d 0 d i 0 i = 1 := by
  have := clebschGordan_stretched h le_rfl (d₂ := 0) (i₂ := 0)
  simp only [add_zero, Nat.sub_zero, Nat.factorial_zero, mul_one] at this
  rw [this, div_self (by positivity), Real.sqrt_one]

/-- **Coupling with spin one half** to `j = j₁ + ½` at `m₂ = ½`:
`(j₁ m₁ ½ ½ | j₁ ½ (j₁ + ½) m) = √((j₁ + m + ½)/(2j₁ + 1))`, with `j₁ + m + ½ = i + 1`. -/
theorem clebschGordan_spinHalf {d i : ℕ} (h : i ≤ d) :
    clebschGordan d 1 (d + 1) i 1 (i + 1) = Real.sqrt ((i + 1) / (d + 1)) := by
  rw [clebschGordan_stretched h le_rfl, Nat.add_sub_add_right]
  congr 1
  simp only [Nat.factorial_succ, Nat.sub_self, Nat.factorial_zero]
  push_cast
  field_simp

/-- **The Condon–Shortley phase convention** [Edmonds, (3.5.11)]:
`(j₁ j₁ j₂ (j - j₁) | j₁ j₂ j j) > 0` for every admissible triple. -/
theorem clebschGordan_pos {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d) :
    0 < clebschGordan d₁ d₂ d d₁ ((d + d₂ - d₁) / 2) d := by
  obtain ⟨h₁, h₂, h₃, r, hr⟩ := isTriad_iff.1 h
  rw [clebschGordan_eq_sqrt_mul_clebschGordanTerm h le_rfl (by omega) le_rfl (by omega) (z₀ := 0)
      (by omega) fun z _ _ ↦ clebschGordanTerm_eq_zero (by omega),
    clebschGordanTerm_def, ite_eq_left (by omega), pow_zero]
  exact mul_pos (Real.sqrt_pos.2 (clebschGordanPrefactor_pos _ _ _ _ _ _)) (by positivity)

end TauCeti.SU2
