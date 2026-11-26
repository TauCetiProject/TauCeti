/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ExplicitBounds.VerifiedZeros.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# Platt's finite-conductor GRH records and exclusion of real zeros

Platt's finite-conductor computation verifies the generalized Riemann hypothesis up to the
modulus-dependent height `TauCeti.plattHeight q` (`max(10⁸ / q, 7.5·10⁷ / q + 200)` for even `q`
and `max(10⁸ / q, 3.75·10⁷ / q + 200)` for odd `q`) for every modulus `2 ≤ q ≤ 400 000`
(`TauCeti.PlattRecord`), and verifies `L(1 / 2, χ) ≠ 0` for every primitive character `χ` modulo
`2 ≤ q ≤ 2 000 000` (`TauCeti.PlattCentralRecord`).

This file defines `plattHeight`, `PlattRecord`, and `PlattCentralRecord`, derives the uniform
height specializations used in explicit zero-free regions and prime-counting estimates
(`10⁸ / q` for `2 ≤ q ≤ 400 000`, `10 000` for `2 ≤ q ≤ 10 000` and in particular `2 ≤ q ≤ 13` and
`q = 8`, and `2500` for `2 ≤ q ≤ 40 000`), and proves `TauCeti.LFunction_ne_zero_of_platt`:
assuming `PlattRecord` and `PlattCentralRecord`, no primitive Dirichlet character of conductor
`q ≤ 400 000` (and hence no character whose conductor is at most `400 000`,
`TauCeti.LFunction_ne_zero_of_platt_of_conductor_le`) vanishes on the real interval `(0, 1)`. For
`q ≥ 2` any real zero has ordinate `0 ≤ plattHeight q` and is forced onto `1 / 2`, where
`PlattCentralRecord` excludes it; for `q = 1` the L-function is `riemannZeta`, which is strictly
negative on `(0, 1)` unconditionally (`TauCeti.riemannZeta_lt_zero`).

## References

* D. J. Platt, *Numerical computations concerning the GRH*, Math. Comp. 85 (2016), 3009–3027,
  Theorems 7.1 and 7.2.
* H. Kadiri, A. Lumley, and N. Ng, *Explicit zero density for the Riemann zeta function*, J. Math.
  Anal. Appl. 465 (2018), 22–46.
-/

public section

open Complex
open scoped ComplexOrder

namespace TauCeti

/-! ### Platt's verification height `H(q)` -/

/-- **Platt's verification height** as a function of the modulus `q`:
`max(10⁸ / q, 7.5·10⁷ / q + 200)` for even `q`, and `max(10⁸ / q, 3.75·10⁷ / q + 200)` for odd
`q`. -/
noncomputable def plattHeight (q : ℕ) : ℝ :=
  if Even q then max (10 ^ 8 / q) (7.5 * 10 ^ 7 / q + 200)
  else max (10 ^ 8 / q) (3.75 * 10 ^ 7 / q + 200)

theorem plattHeight_def (q : ℕ) :
    plattHeight q =
      if Even q then max (10 ^ 8 / (q : ℝ)) (7.5 * 10 ^ 7 / (q : ℝ) + 200)
      else max (10 ^ 8 / (q : ℝ)) (3.75 * 10 ^ 7 / (q : ℝ) + 200) :=
  (rfl)

/-- Value of `plattHeight q` for even `q`. -/
theorem plattHeight_of_even {q : ℕ} (hq : Even q) :
    plattHeight q = max (10 ^ 8 / (q : ℝ)) (7.5 * 10 ^ 7 / (q : ℝ) + 200) := by
  rw [plattHeight_def, ite_eq_left hq]

/-- Value of `plattHeight q` when `q` is not even. -/
theorem plattHeight_of_not_even {q : ℕ} (hq : ¬Even q) :
    plattHeight q = max (10 ^ 8 / (q : ℝ)) (3.75 * 10 ^ 7 / (q : ℝ) + 200) := by
  rw [plattHeight_def, ite_eq_right hq]

/-- Value of `plattHeight q` for odd `q`. -/
theorem plattHeight_of_odd {q : ℕ} (hq : Odd q) :
    plattHeight q = max (10 ^ 8 / (q : ℝ)) (3.75 * 10 ^ 7 / (q : ℝ) + 200) :=
  plattHeight_of_not_even (Nat.not_even_iff_odd.mpr hq)

/-- The first branch `10 ^ 8 / q` is always a lower bound for `plattHeight q`. -/
theorem div_le_plattHeight (q : ℕ) : 10 ^ 8 / (q : ℝ) ≤ plattHeight q := by
  rw [plattHeight_def]
  split_ifs <;> exact le_max_left _ _

/-- `plattHeight q` is bounded below by `200` for every `q : ℕ`. -/
theorem two_hundred_le_plattHeight (q : ℕ) : 200 ≤ plattHeight q := by
  rw [plattHeight_def]
  split_ifs <;> exact le_trans (le_add_of_nonneg_left (by positivity)) (le_max_right _ _)

/-- `plattHeight q` is strictly positive for every `q : ℕ`. -/
theorem plattHeight_pos (q : ℕ) : 0 < plattHeight q :=
  lt_of_lt_of_le (by norm_num) (two_hundred_le_plattHeight q)

/-- `plattHeight q` is nonnegative for every `q : ℕ`. -/
theorem plattHeight_nonneg (q : ℕ) : 0 ≤ plattHeight q :=
  (plattHeight_pos q).le

/-- Within moduli of the same parity, `plattHeight` is antitone on positive integers. -/
theorem plattHeight_le_plattHeight {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hle : q₁ ≤ q₂)
    (hpar : Even q₁ ↔ Even q₂) : plattHeight q₂ ≤ plattHeight q₁ := by
  have hpos : (0 : ℝ) < q₁ := Nat.cast_pos.mpr hq₁
  have hcast : (q₁ : ℝ) ≤ q₂ := Nat.cast_le.mpr hle
  simp only [plattHeight_def, hpar]
  split_ifs <;> exact max_le_max (div_le_div_of_nonneg_left (by positivity) hpos hcast)
    (add_le_add_left (div_le_div_of_nonneg_left (by positivity) hpos hcast) 200)

@[simp]
theorem plattHeight_three : plattHeight 3 = 10 ^ 8 / 3 := by
  rw [plattHeight_of_odd (by decide)]
  norm_num

@[simp]
theorem plattHeight_five : plattHeight 5 = 2 * 10 ^ 7 := by
  rw [plattHeight_of_odd (by decide)]
  norm_num

@[simp]
theorem plattHeight_four_hundred_thousand : plattHeight 400000 = 387.5 := by
  rw [plattHeight_of_even (by decide)]
  norm_num

/-- If `c * q ≤ 10 ^ 8` for a positive modulus `q`, then `c ≤ plattHeight q`. -/
theorem le_plattHeight_of_mul_le {q : ℕ} {c : ℝ} (hq : 0 < q) (h : c * q ≤ 10 ^ 8) :
    c ≤ plattHeight q :=
  ((le_div_iff₀ (Nat.cast_pos.mpr hq)).2 h).trans (div_le_plattHeight q)

/-- For `0 < q ≤ 10 000`, `10 000 ≤ plattHeight q`. -/
theorem ten_thousand_le_plattHeight {q : ℕ} (hq₀ : 0 < q) (hq : q ≤ 10000) :
    10000 ≤ plattHeight q :=
  le_plattHeight_of_mul_le hq₀ (by
    have : (q : ℝ) ≤ 10000 := by exact_mod_cast hq
    linarith)

/-- For `0 < q ≤ 40 000`, `2500 ≤ plattHeight q`. -/
theorem two_thousand_five_hundred_le_plattHeight {q : ℕ} (hq₀ : 0 < q) (hq : q ≤ 40000) :
    2500 ≤ plattHeight q :=
  le_plattHeight_of_mul_le hq₀ (by
    have : (q : ℝ) ≤ 40000 := by exact_mod_cast hq
    linarith)

/-! ### Platt's records and bounded-height corollaries -/

/-- **Platt's finite-conductor GRH record** (Platt 2016, Theorem 7.1): `DirichletGRHUpTo q H(q)`
for every modulus `2 ≤ q ≤ 400 000`. Modulus `1` (whose primitive L-function is `riemannZeta`) is
excluded. -/
def PlattRecord : Prop :=
  ∀ (q : ℕ) [NeZero q], 2 ≤ q → q ≤ 400000 → DirichletGRHUpTo q (plattHeight q)

theorem plattRecord_def :
    PlattRecord =
      ∀ (q : ℕ) [NeZero q], 2 ≤ q → q ≤ 400000 → DirichletGRHUpTo q (plattHeight q) :=
  (rfl)

/-- Specialize `PlattRecord` to a modulus `2 ≤ q ≤ 400 000`. -/
theorem PlattRecord.dirichletGRHUpTo (hP : PlattRecord) {q : ℕ} [NeZero q] (hq₂ : 2 ≤ q)
    (hq : q ≤ 400000) : DirichletGRHUpTo q (plattHeight q) :=
  hP q hq₂ hq

/-- **Platt's central-point nonvanishing record** (Platt 2016, Theorem 7.2): `L(1 / 2, χ) ≠ 0` for
every primitive character `χ` modulo `2 ≤ q ≤ 2 000 000`. -/
def PlattCentralRecord : Prop :=
  ∀ (q : ℕ) [NeZero q], 2 ≤ q → q ≤ 2000000 → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    DirichletCharacter.LFunction χ (1 / 2) ≠ 0

theorem plattCentralRecord_def :
    PlattCentralRecord =
      ∀ (q : ℕ) [NeZero q], 2 ≤ q → q ≤ 2000000 → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        DirichletCharacter.LFunction χ (1 / 2) ≠ 0 :=
  (rfl)

/-- Specialize `PlattCentralRecord` to a primitive character modulo `2 ≤ q ≤ 2 000 000`. -/
theorem PlattCentralRecord.LFunction_half_ne_zero (hC : PlattCentralRecord) {q : ℕ} [NeZero q]
    (hq₂ : 2 ≤ q) (hq : q ≤ 2000000) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ.LFunction (1 / 2) ≠ 0 :=
  hC q hq₂ hq χ hχ

/-- Given `PlattRecord`, `DirichletGRHUpTo q (10 ^ 8 / q)` holds for every `2 ≤ q ≤ 400 000`. -/
theorem PlattRecord.dirichletGRHUpTo_div (hP : PlattRecord) {q : ℕ} [NeZero q] (hq₂ : 2 ≤ q)
    (hq : q ≤ 400000) : DirichletGRHUpTo q (10 ^ 8 / q) :=
  (hP q hq₂ hq).mono (div_le_plattHeight q)

/-- Given `PlattRecord`, `DirichletGRHUpTo q 10000` holds for every `2 ≤ q ≤ 10 000`. -/
theorem PlattRecord.dirichletGRHUpTo_ten_thousand_of_le_ten_thousand (hP : PlattRecord) {q : ℕ}
    [NeZero q] (hq₂ : 2 ≤ q) (hq : q ≤ 10000) : DirichletGRHUpTo q 10000 :=
  (hP q hq₂ (by omega)).mono (ten_thousand_le_plattHeight (by omega) hq)

/-- Given `PlattRecord`, `DirichletGRHUpTo q 10000` holds for `2 ≤ q ≤ 13`. -/
theorem PlattRecord.dirichletGRHUpTo_ten_thousand_of_le_thirteen (hP : PlattRecord) {q : ℕ}
    [NeZero q] (hq₂ : 2 ≤ q) (hq : q ≤ 13) : DirichletGRHUpTo q 10000 :=
  hP.dirichletGRHUpTo_ten_thousand_of_le_ten_thousand hq₂ (by omega)

/-- Given `PlattRecord`, `DirichletGRHUpTo q 2500` holds for every `2 ≤ q ≤ 40 000`. -/
theorem PlattRecord.dirichletGRHUpTo_two_thousand_five_hundred (hP : PlattRecord) {q : ℕ}
    [NeZero q] (hq₂ : 2 ≤ q) (hq : q ≤ 40000) : DirichletGRHUpTo q 2500 :=
  (hP q hq₂ (by omega)).mono (two_thousand_five_hundred_le_plattHeight (by omega) hq)

/-- Given `PlattRecord`, `DirichletGRHUpTo 8 10000` holds. -/
theorem PlattRecord.dirichletGRHUpTo_eight_ten_thousand (hP : PlattRecord) :
    DirichletGRHUpTo 8 10000 :=
  hP.dirichletGRHUpTo_ten_thousand_of_le_thirteen (by decide) (by decide)

/-! ### Exclusion of real zeros in `(0, 1)` -/

/-- **No real zeros in `(0, 1)` for primitive characters of conductor up to `400 000`.** Given
`PlattRecord` and `PlattCentralRecord`, `χ.LFunction s ≠ 0` for every primitive character `χ`
modulo `q ≤ 400 000` and real `0 < s < 1`. At `q = 1` the statement holds unconditionally by
`TauCeti.riemannZeta_lt_zero`. -/
theorem LFunction_ne_zero_of_platt (hP : PlattRecord) (hC : PlattCentralRecord) {q : ℕ}
    [NeZero q] (hq : q ≤ 400000) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  rcases eq_or_ne q 1 with rfl | hq1
  · rw [DirichletCharacter.LFunction_modOne_eq]
    exact (riemannZeta_lt_zero hs₀ hs₁).ne
  · have hq₂ : 2 ≤ q := by
      have hpos := NeZero.pos q
      omega
    intro h0
    have hs_half : s = 1 / 2 := by
      simpa using (hP.dirichletGRHUpTo hq₂ hq).re_eq hχ h0 (by simpa using hs₀)
        (by simpa using hs₁) (by simpa using plattHeight_nonneg q)
    have hcs : ((s : ℝ) : ℂ) = 1 / 2 := by
      rw [hs_half]
      norm_num
    rw [hcs] at h0
    exact hC.LFunction_half_ne_zero hq₂ (by omega) hχ h0

/-- **No real zeros in `(0, 1)` for any character of conductor at most `400 000`.** Deleted Euler
factors at primes dividing an ambient modulus `q` are nonzero on `Re s > 0`, so
`LFunction_ne_zero_of_platt` lifts from `χ.primitiveCharacter` to any character `χ` (primitive or
imprimitive) whose conductor satisfies `χ.conductor ≤ 400 000`. -/
theorem LFunction_ne_zero_of_platt_of_conductor_le (hP : PlattRecord) (hC : PlattCentralRecord)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hcond : χ.conductor ≤ 400000)
    (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hs1' : (s : ℂ) ≠ 1 := by exact_mod_cast hs₁.ne
  rw [← χ.changeLevel_primitiveCharacter]
  intro h0
  have hprim0 : χ.primitiveCharacter.LFunction s = 0 :=
    (DirichletCharacter.LFunction_changeLevel_eq_zero_iff χ.primitiveCharacter
      χ.conductor_dvd_level (by simpa using hs₀) (.inr hs1')).1 h0
  exact LFunction_ne_zero_of_platt hP hC hcond χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive s hs₀ hs₁ hprim0

/-- **No real zeros in `(0, 1)` for any character modulo `q ≤ 400 000`.** -/
theorem LFunction_ne_zero_of_platt_of_le (hP : PlattRecord) (hC : PlattCentralRecord)
    {q : ℕ} [NeZero q] (hq : q ≤ 400000) (χ : DirichletCharacter ℂ q)
    (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_platt_of_conductor_le hP hC χ
    ((Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level).trans hq) s hs₀ hs₁

end TauCeti
