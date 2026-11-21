/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Data.Int.MulPred
import TauCeti.Data.Int.Parity
import TauCeti.Data.ZMod.Divisibility
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.Modular.Reduction

/-!
# Kronecker-symbol formulas for the Dedekind eta multiplier

This file evaluates the Dedekind eta multiplier `ε(γ)` (`TauCeti.ModularForm.etaMultiplier`) for
matrices `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` in terms of the Kronecker symbol
(complementing the negation, `c = 0`, and Dedekind-sum formulas in
`TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation` and
`TauCeti.NumberTheory.ModularForms.DedekindEta.DedekindSum`):

* **The Kronecker-symbol formula** (Strömberg, Remark 2.5, equation (2.5)): for `c > 0`, writing
  `e(x) = exp(2 π i x)`,
  - `ε(γ) = (d / c) e(((a + d) c - b d (c² - 1) - 3 c) / 24)` if `c` is odd,
  - `ε(γ) = (c / d) e(((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)` if `c` is even,
  where `(· / ·)` is the Kronecker symbol `TauCeti.kroneckerSym`.

The formula is proved by Euclidean induction on `SL(2, ℤ)`
(`Matrix.SpecialLinearGroup.induction_on_of_c_pos`), starting from `c = 1`
(`etaMultiplier_of_c_eq_one`) and matching the transformation laws under right multiplication by
`T` (`etaMultiplier_mul_T`) and `S` (`etaMultiplier_mul_S`) via quadratic reciprocity and its
supplements for `kroneckerSym`.

## Main results

* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_odd`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_even`: the Kronecker-symbol formulas for
  `c > 0`.

## References

* F. Strömberg, *Computation of Maass waveforms with nontrivial multiplier systems*, Math. Comp.
  77 (2008), 2375–2416, Remark 2.5, equation (2.5).
-/

public section

open Complex ModularGroup Matrix.SpecialLinearGroup ZMod
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### The Kronecker-symbol formula -/

/-- Addition law for the 24th-root phase `n ↦ exp (2 π i n / 24)`. -/
private theorem cexp_twentyFour_add (m n : ℤ) :
    cexp (2 * π * I * (m : ℂ) / 24) * cexp (2 * π * I * (n : ℂ) / 24) =
      cexp (2 * π * I * ((m + n : ℤ) : ℂ) / 24) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Multiplying `cexp (2 π i n / 24)` by `cexp (π i / 12)` shifts `n` by `1`. -/
private theorem cexp_pi_div_twelve_mul_cexp_twentyFour (n : ℤ) :
    cexp (π * I / 12) * cexp (2 * π * I * (n : ℂ) / 24) =
      cexp (2 * π * I * ((n + 1 : ℤ) : ℂ) / 24) := by
  have h1 : cexp (π * I / 12) = cexp (2 * π * I * ((1 : ℤ) : ℂ) / 24) := by
    congr 1
    push_cast
    ring
  rw [h1, cexp_twentyFour_add, add_comm]

/-- Multiplying `cexp (2 π i n / 24)` by `cexp (2 π i · 3 / 24)` shifts `n` by `3`. -/
private theorem cexp_twentyFour_three_mul (n : ℤ) :
    cexp (2 * π * I * ((3 : ℤ) : ℂ) / 24) * cexp (2 * π * I * (n : ℂ) / 24) =
      cexp (2 * π * I * ((n + 3 : ℤ) : ℂ) / 24) := by
  rw [cexp_twentyFour_add, add_comm]

/-- Shifting `n` by `24 * k` leaves `cexp (2 π i n / 24)` unchanged. -/
private theorem cexp_twentyFour_add_twentyFour_mul (n k : ℤ) :
    cexp (2 * π * I * ((n + 24 * k : ℤ) : ℂ) / 24) = cexp (2 * π * I * (n : ℂ) / 24) := by
  have harg : 2 * π * I * ((24 * k : ℤ) : ℂ) / 24 = (k : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [← cexp_twentyFour_add, harg, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Multiplying `cexp (2 π i (n + 12 k) / 24)` by `(-1) ^ k` cancels the shift. -/
private theorem negOnePow_mul_cexp_twentyFour_add_twelve_mul (n k : ℤ) :
    ((k.negOnePow : ℤ) : ℂ) * cexp (2 * π * I * ((n + 12 * k : ℤ) : ℂ) / 24) =
      cexp (2 * π * I * (n : ℂ) / 24) := by
  have harg : 2 * π * I * ((12 * k : ℤ) : ℂ) / 24 = k * (π * I) := by
    push_cast
    ring
  rw [← cexp_twentyFour_add, harg, ← Complex.exp_add, Int.cast_negOnePow,
    Complex.neg_one_zpow_mul_exp_add_int_mul_pi_mul_I]

private theorem mul_T_apply_apply_zero (γ : SL(2, ℤ)) (i : Fin 2) : (γ * T) i 0 = γ i 0 := by
  simpa using TauCeti.ModularGroup.mul_T_zpow_apply_apply_zero γ 1 i

private theorem mul_T_apply_apply_one (γ : SL(2, ℤ)) (i : Fin 2) :
    (γ * T) i 1 = γ i 0 + γ i 1 := by
  simpa using TauCeti.ModularGroup.mul_T_zpow_apply_apply_one γ 1 i

/-- The 24th-root exponent in Strömberg's Kronecker formula for odd `c`. -/
private def kroneckerExpOdd (γ : SL(2, ℤ)) : ℤ :=
  (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0

/-- The 24th-root exponent in Strömberg's Kronecker formula for even `c`. -/
private def kroneckerExpEven (γ : SL(2, ℤ)) : ℤ :=
  (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) + 3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1

/-- Combined Kronecker-symbol formula for `ε(γ)` when `c > 0`, used as the induction motive. -/
private noncomputable def kroneckerMultiplier (γ : SL(2, ℤ)) : ℂ :=
  if Odd (γ 1 0) then
    (kroneckerSym (γ 1 1) (γ 1 0) : ℂ) * cexp (2 * π * I * (kroneckerExpOdd γ : ℂ) / 24)
  else
    (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) * cexp (2 * π * I * (kroneckerExpEven γ : ℂ) / 24)

/-- Base case `c = 1` of `kroneckerMultiplier`. -/
private theorem kroneckerMultiplier_of_c_eq_one (γ : SL(2, ℤ)) (hc : γ 1 0 = 1) :
    kroneckerMultiplier γ = etaMultiplier γ := by
  have hodd : Odd (γ 1 0) := by rw [hc]; exact odd_one
  rw [etaMultiplier_of_c_eq_one γ hc, kroneckerMultiplier, ite_eq_left hodd, hc,
    kroneckerSym_one_right, Int.cast_one, one_mul, kroneckerExpOdd, hc]
  congr 1
  push_cast
  ring

/-- Exponent change in `kroneckerExpOdd` under `γ ↦ γ * T`: for odd `c`, it increases by
`1 (mod 24)`. -/
private theorem kroneckerExpOdd_mul_T (γ : SL(2, ℤ)) (hodd : Odd (γ 1 0)) :
    ∃ k : ℤ, kroneckerExpOdd (γ * T) = kroneckerExpOdd γ + 1 + 24 * k := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hdiff : kroneckerExpOdd (γ * T) - (kroneckerExpOdd γ + 1) =
      -(γ 0 0 + 2 * γ 0 1) * (γ 1 0 * (γ 1 0 ^ 2 - 1)) := by
    simp only [kroneckerExpOdd, mul_T_apply_apply_zero, mul_T_apply_apply_one]
    linear_combination -(γ 1 0 ^ 2 - 1) * hdet
  have h24 : (24 : ℤ) ∣ γ 1 0 * (γ 1 0 ^ 2 - 1) :=
    (by decide : IsCoprime (3 : ℤ) 8).mul_dvd (Int.three_dvd_mul_sq_sub_one (γ 1 0))
      (dvd_mul_of_dvd_right (Int.eight_dvd_sq_sub_one_of_odd hodd) _)
  obtain ⟨t, ht⟩ := h24
  refine ⟨-(γ 0 0 + 2 * γ 0 1) * t, ?_⟩
  linear_combination hdiff + (-(γ 0 0 + 2 * γ 0 1)) * ht

/-- Algebraic change in `kroneckerExpEven` under `γ ↦ γ * T`. -/
private theorem kroneckerExpEven_mul_T_sub (γ : SL(2, ℤ)) :
    kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) =
      -3 * γ 1 0 * (γ 1 0 - 1) - (γ 0 0 + 2 * γ 0 1) * (γ 1 0 * (γ 1 0 ^ 2 - 1)) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  simp only [kroneckerExpEven, mul_T_apply_apply_zero, mul_T_apply_apply_one]
  linear_combination -(γ 1 0 ^ 2 - 1) * hdet

/-- For every `γ ∈ SL(2, ℤ)`, `kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1)` is divisible
by `3`. -/
private theorem three_dvd_kroneckerExpEven_mul_T_sub (γ : SL(2, ℤ)) :
    (3 : ℤ) ∣ kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) := by
  rw [kroneckerExpEven_mul_T_sub]
  exact dvd_sub ⟨-γ 1 0 * (γ 1 0 - 1), by ring⟩
    (dvd_mul_of_dvd_right (Int.three_dvd_mul_sq_sub_one (γ 1 0)) _)

/-- Exponent change in `kroneckerExpEven` under `γ ↦ γ * T` when `4 ∣ c`: it increases by
`1 (mod 24)`. -/
private theorem kroneckerExpEven_mul_T_of_emod_four_eq_zero (γ : SL(2, ℤ))
    (hc4 : γ 1 0 % 4 = 0) :
    ∃ k : ℤ, kroneckerExpEven (γ * T) = kroneckerExpEven γ + 1 + 24 * k := by
  have ha_odd : Odd (γ 0 0) :=
    (Matrix.SpecialLinearGroup.isCoprime_col γ 0).symm.odd_of_even (Int.even_iff.mpr (by omega))
  have hc4_dvd : (4 : ℤ) ∣ γ 1 0 := Int.dvd_of_emod_eq_zero hc4
  have hc_sq8 : ((γ 1 0 : ZMod 8) ^ 2) = 0 := by
    simpa [sq] using ZMod.intCast_mul_eq_zero_of_dvd
      (dvd_trans (by norm_num : (2 : ℤ) ∣ 4) hc4_dvd) hc4_dvd
  have hc_mul_odd8 : ((γ 1 0 * (3 + γ 0 0 + 2 * γ 0 1) : ℤ) : ZMod 8) = 0 := by
    obtain ⟨a', ha'⟩ := ha_odd
    have h2 : (2 : ℤ) ∣ 3 + γ 0 0 + 2 * γ 0 1 := ⟨2 + a' + γ 0 1, by rw [ha']; ring⟩
    simpa [mul_comm] using ZMod.intCast_mul_eq_zero_of_dvd h2 hc4_dvd
  have h8 : (8 : ℤ) ∣ kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp ?_
    rw [kroneckerExpEven_mul_T_sub]
    push_cast
    push_cast at hc_mul_odd8
    linear_combination (-3 - (γ 0 0 + 2 * γ 0 1) * γ 1 0 : ZMod 8) * hc_sq8 + hc_mul_odd8
  obtain ⟨k, hk⟩ := (by decide : IsCoprime (3 : ℤ) 8).mul_dvd
    (three_dvd_kroneckerExpEven_mul_T_sub γ) h8
  exact ⟨k, by linarith⟩

/-- From `a d - b c = 1` and `c ≡ 2 (mod 4)`, `d` is odd and `a + 2 b ≡ d (mod 4)`. -/
private theorem four_dvd_add_two_mul_sub_of_emod_four_eq_two (γ : SL(2, ℤ))
    (hc4 : γ 1 0 % 4 = 2) : (4 : ℤ) ∣ γ 0 0 + 2 * γ 0 1 - γ 1 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hd_odd : Odd (γ 1 1) :=
    (ModularGroup.bottom_row_coprime γ).odd_of_even (Int.even_iff.mpr (by omega))
  obtain ⟨u, hu⟩ : ∃ u : ℤ, γ 1 0 = 4 * u + 2 := ⟨γ 1 0 / 4, by omega⟩
  obtain ⟨v, hv⟩ := hd_odd
  have hd2 : γ 1 1 ^ 2 = 4 * v * (v + 1) + 1 := by rw [hv]; ring
  have hcd : γ 1 0 + 2 * γ 1 1 = 4 * (u + v + 1) := by rw [hu, hv]; ring
  refine ⟨γ 1 1 * γ 0 1 * (u + v + 1) - (γ 0 0 + 2 * γ 0 1) * v * (v + 1), ?_⟩
  linear_combination γ 1 1 * hdet - (γ 0 0 + 2 * γ 0 1) * hd2 + γ 1 1 * γ 0 1 * hcd

/-- Modulo `8`, `kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) ≡ -3 c (1 + d)` when
`c ≡ 2 (mod 4)`. -/
private theorem kroneckerExpEven_mul_T_sub_cast_zmod8 (γ : SL(2, ℤ)) (hc4 : γ 1 0 % 4 = 2) :
    ((kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) : ℤ) : ZMod 8) =
      -3 * γ 1 0 * (1 + γ 1 1) := by
  have hc_even : (2 : ℤ) ∣ γ 1 0 := Int.dvd_of_emod_eq_zero (by omega)
  have hc_sub2 : (4 : ℤ) ∣ γ 1 0 - 2 := Int.dvd_of_emod_eq_zero (by omega)
  have had_c8 : ((γ 1 0 * (γ 0 0 + 2 * γ 0 1 - γ 1 1) : ℤ) : ZMod 8) = 0 :=
    ZMod.intCast_mul_eq_zero_of_dvd hc_even (four_dvd_add_two_mul_sub_of_emod_four_eq_two γ hc4)
  have hc_sub2_8 : ((γ 1 0 * (γ 1 0 - 2) : ℤ) : ZMod 8) = 0 :=
    ZMod.intCast_mul_eq_zero_of_dvd hc_even hc_sub2
  have hc_sq_sub4_8 : ((γ 1 0 ^ 2 - 4 : ℤ) : ZMod 8) = 0 := by
    have hsq : γ 1 0 ^ 2 - 4 = (γ 1 0 + 2) * (γ 1 0 - 2) := by simpa using sq_sub_sq (γ 1 0) 2
    rw [hsq]
    exact ZMod.intCast_mul_eq_zero_of_dvd (m := 2) (Int.dvd_of_emod_eq_zero (by omega)) hc_sub2
  rw [kroneckerExpEven_mul_T_sub]
  push_cast
  push_cast at had_c8 hc_sub2_8 hc_sq_sub4_8
  linear_combination -3 * hc_sub2_8 - 3 * had_c8 - (γ 0 0 + 2 * γ 0 1 : ZMod 8) *
    (γ 1 0 : ZMod 8) * hc_sq_sub4_8

/-- Exponent change in `kroneckerExpEven` under `γ ↦ γ * T` when `c ≡ 2 (mod 4)`: it changes by
`1 + 12 k` where `(-1)^k = -χ₄ d`. -/
private theorem kroneckerExpEven_mul_T_of_emod_four_eq_two (γ : SL(2, ℤ))
    (hc4 : γ 1 0 % 4 = 2) :
    ∃ k : ℤ, kroneckerExpEven (γ * T) = kroneckerExpEven γ + 1 + 12 * k ∧
      (k.negOnePow : ℤ) = -χ₄ (γ 1 1) := by
  have hd_odd : Odd (γ 1 1) :=
    (ModularGroup.bottom_row_coprime γ).odd_of_even (Int.even_iff.mpr (by omega))
  have hd2_mod : γ 1 1 % 2 = 1 := Int.odd_iff.mp hd_odd
  have h3 := three_dvd_kroneckerExpEven_mul_T_sub γ
  have hc_even : (2 : ℤ) ∣ γ 1 0 := Int.dvd_of_emod_eq_zero (by omega)
  have hc_sub2 : (4 : ℤ) ∣ γ 1 0 - 2 := Int.dvd_of_emod_eq_zero (by omega)
  have hmod8 := kroneckerExpEven_mul_T_sub_cast_zmod8 γ hc4
  rcases (by omega : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3) with h1 | h3d
  · have h8' : (8 : ℤ) ∣ kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) - 12 := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp ?_
      rw [Int.cast_sub, hmod8]
      have hcd8 : ((γ 1 0 * (γ 1 1 - 1) : ℤ) : ZMod 8) = 0 :=
        ZMod.intCast_mul_eq_zero_of_dvd hc_even (n := 4) (Int.dvd_of_emod_eq_zero (by omega))
      have h6c8 : ((6 * (γ 1 0 - 2) : ℤ) : ZMod 8) = 0 :=
        ZMod.intCast_mul_eq_zero_of_dvd (by norm_num : (2 : ℤ) ∣ 6) hc_sub2
      have h24 : (24 : ZMod 8) = 0 := by decide
      push_cast at hcd8 h6c8 ⊢
      linear_combination -3 * hcd8 - h6c8 - h24
    obtain ⟨u, hu⟩ := (by decide : IsCoprime (3 : ℤ) 8).mul_dvd
      (dvd_sub h3 ⟨4, by norm_num⟩) h8'
    refine ⟨2 * u + 1, by linarith, ?_⟩
    rw [Int.negOnePow_two_mul_add_one, Units.val_neg, Units.val_one, χ₄_int_one_mod_four h1]
  · have h8 : (8 : ℤ) ∣ kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp ?_
      rw [hmod8]
      have hcd8 : ((γ 1 0 * (1 + γ 1 1) : ℤ) : ZMod 8) = 0 :=
        ZMod.intCast_mul_eq_zero_of_dvd hc_even (n := 4) (Int.dvd_of_emod_eq_zero (by omega))
      push_cast at hcd8
      linear_combination -3 * hcd8
    obtain ⟨u, hu⟩ := (by decide : IsCoprime (3 : ℤ) 8).mul_dvd h3 h8
    refine ⟨2 * u, by linarith, ?_⟩
    rw [Int.negOnePow_two_mul, Units.val_one, χ₄_int_three_mod_four h3d, neg_neg]

/-- Right translation step `γ ↦ γ * T` for `kroneckerMultiplier`. -/
private theorem kroneckerMultiplier_mul_T (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    kroneckerMultiplier (γ * T) = cexp (π * I / 12) * kroneckerMultiplier γ := by
  have hcT : (γ * T) 1 0 = γ 1 0 := mul_T_apply_apply_zero γ 1
  have hdT : (γ * T) 1 1 = γ 1 0 + γ 1 1 := mul_T_apply_apply_one γ 1
  by_cases hodd : Odd (γ 1 0)
  · simp only [kroneckerMultiplier, hcT, hdT, ite_eq_left hodd]
    obtain ⟨k, hk⟩ := kroneckerExpOdd_mul_T γ hodd
    have hsym : kroneckerSym (γ 1 0 + γ 1 1) (γ 1 0) = kroneckerSym (γ 1 1) (γ 1 0) :=
      kroneckerSym_mod_left' hodd hc (Int.add_emod_left (γ 1 0) (γ 1 1))
    rw [hsym, hk, cexp_twentyFour_add_twentyFour_mul, ← cexp_pi_div_twelve_mul_cexp_twentyFour]
    ring
  · simp only [kroneckerMultiplier, hcT, hdT, ite_eq_right hodd]
    have hc_even : γ 1 0 % 4 = 0 ∨ γ 1 0 % 4 = 2 := by
      have := Int.even_iff.mp (Int.not_odd_iff_even.mp hodd)
      omega
    rcases hc_even with hc0 | hc2
    · obtain ⟨k, hk⟩ := kroneckerExpEven_mul_T_of_emod_four_eq_zero γ hc0
      have hsym : kroneckerSym (γ 1 0) (γ 1 0 + γ 1 1) = kroneckerSym (γ 1 0) (γ 1 1) := by
        rw [add_comm]
        exact kroneckerSym_mod_right' (.inl (Int.modEq_zero_iff_dvd.mpr
          (Int.dvd_of_emod_eq_zero hc0))) (Int.add_emod_right (γ 1 1) (γ 1 0))
      rw [hsym, hk, cexp_twentyFour_add_twentyFour_mul, ← cexp_pi_div_twelve_mul_cexp_twentyFour]
      ring
    · obtain ⟨k, hk, hk_sign⟩ := kroneckerExpEven_mul_T_of_emod_four_eq_two γ hc2
      have hsym : kroneckerSym (γ 1 0) (γ 1 0 + γ 1 1) =
          (k.negOnePow : ℤ) * kroneckerSym (γ 1 0) (γ 1 1) := by
        rw [add_comm, kroneckerSym_add_self_right_of_emod_four_eq_two hc2 (γ 1 1), hk_sign]
      rw [hsym, hk, Int.cast_mul, mul_comm ((k.negOnePow : ℤ) : ℂ), mul_assoc,
        negOnePow_mul_cexp_twentyFour_add_twelve_mul, ← cexp_pi_div_twelve_mul_cexp_twentyFour]
      ring

/-- The universal polynomial change under right inversion `γ ↦ γ * S`:
`((b - c) d - a c (d² - 1)) - ((a + d) c - b d (c² - 1)) = -3 c d`. -/
private theorem kroneckerQuad_mul_S (γ : SL(2, ℤ)) :
    (((γ * S) 0 0 + (γ * S) 1 1) * (γ * S) 1 0 -
      (γ * S) 0 1 * (γ * S) 1 1 * ((γ * S) 1 0 ^ 2 - 1)) -
    ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1)) = -3 * γ 1 0 * γ 1 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  simp only [TauCeti.ModularGroup.mul_S_apply_apply_zero,
    TauCeti.ModularGroup.mul_S_apply_apply_one]
  linear_combination -γ 1 0 * γ 1 1 * hdet

/-- Right inversion step `γ ↦ γ * S` for `kroneckerMultiplier` when `c > 0` and `d > 0`. -/
private theorem kroneckerMultiplier_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    kroneckerMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerMultiplier γ := by
  have hcS : (γ * S) 1 0 = γ 1 1 := TauCeti.ModularGroup.mul_S_apply_apply_zero γ 1
  have hdS : (γ * S) 1 1 = -γ 1 0 := TauCeti.ModularGroup.mul_S_apply_apply_one γ 1
  have hquad := kroneckerQuad_mul_S γ
  rw [hcS, hdS] at hquad
  suffices h : cexp (2 * π * I * ((3 : ℤ) : ℂ) / 24) * kroneckerMultiplier (γ * S) =
      kroneckerMultiplier γ by
    have hmul := congrArg (cexp (-(π * I / 4)) * ·) h
    have hcancel : cexp (-(π * I / 4)) * cexp (2 * π * I * ((3 : ℤ) : ℂ) / 24) = 1 := by
      rw [← Complex.exp_add]; convert Complex.exp_zero using 2; push_cast; ring
    rwa [← mul_assoc, hcancel, one_mul] at hmul
  by_cases hc_odd : Odd (γ 1 0) <;> by_cases hd_odd : Odd (γ 1 1)
  · simp only [kroneckerMultiplier, hcS, hdS, ite_eq_left hc_odd, ite_eq_left hd_odd]
    rw [mul_left_comm, cexp_twentyFour_three_mul]
    set k : ℤ := ((-γ 1 0 - 1) / 2) * ((γ 1 1 - 1) / 2)
    have hexp : kroneckerExpOdd (γ * S) + 3 = kroneckerExpOdd γ + 12 * k := by
      obtain ⟨c', hc'⟩ := hc_odd
      obtain ⟨d', hd'⟩ := hd_odd
      have hk : k = -(c' + 1) * d' := by simp only [k, hc', hd']; congr 1 <;> omega
      simp only [kroneckerExpOdd, hcS, hdS]
      rw [hk]; rw [hc', hd'] at hquad ⊢; linear_combination hquad
    rw [hexp, kroneckerSym_quadratic_reciprocity hc_odd.neg hd_odd,
      ite_eq_right (fun h ↦ hd.not_gt h.2), one_mul, kroneckerSym_neg_right_of_nonneg hd.le,
      Int.cast_mul, mul_comm ((k.negOnePow : ℤ) : ℂ), mul_assoc,
      negOnePow_mul_cexp_twentyFour_add_twelve_mul]
  · simp only [kroneckerMultiplier, hcS, hdS, ite_eq_left hc_odd, ite_eq_right hd_odd]
    rw [mul_left_comm, cexp_twentyFour_three_mul, kroneckerSym_neg_right_of_nonneg hd.le]
    have hexp : kroneckerExpEven (γ * S) + 3 = kroneckerExpOdd γ := by
      simp only [kroneckerExpEven, kroneckerExpOdd, hcS, hdS]
      linear_combination hquad
    rw [hexp]
  · simp only [kroneckerMultiplier, hcS, hdS, ite_eq_right hc_odd, ite_eq_left hd_odd]
    rw [mul_left_comm, cexp_twentyFour_three_mul]
    set k : ℤ := (γ 1 1 - 1) / 2
    have hexp : kroneckerExpOdd (γ * S) + 3 = kroneckerExpEven γ + 12 * (-k) := by
      obtain ⟨d', hd'⟩ := hd_odd
      have hk : k = d' := by simp only [k, hd']; omega
      simp only [kroneckerExpOdd, kroneckerExpEven, hcS, hdS]
      rw [hk]; rw [hd'] at hquad ⊢; linear_combination hquad
    have hsym : kroneckerSym (-γ 1 0) (γ 1 1) =
        ((-k).negOnePow : ℤ) * kroneckerSym (γ 1 0) (γ 1 1) := by
      rw [Int.negOnePow_neg, neg_eq_neg_one_mul, kroneckerSym_mul_left (by norm_num) hc.ne',
        kroneckerSym_neg_one_left hd_odd, χ₄_intCast_eq_negOnePow hd_odd]
    rw [hexp, hsym, Int.cast_mul, mul_comm (((-k).negOnePow : ℤ) : ℂ), mul_assoc,
      negOnePow_mul_cexp_twentyFour_add_twelve_mul]
  · exact absurd ((ModularGroup.bottom_row_coprime γ).odd_of_even (Int.not_odd_iff_even.mp hc_odd))
      hd_odd

/-- Combined Kronecker formula for `ε(γ)` when `c > 0`, by Euclidean induction. -/
private theorem etaMultiplier_eq_kroneckerMultiplier (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = kroneckerMultiplier γ := by
  refine γ.induction_on_of_c_pos hc (P := fun γ ↦ etaMultiplier γ = kroneckerMultiplier γ) ?_ ?_ ?_
  · intro γ hc1
    exact (kroneckerMultiplier_of_c_eq_one γ hc1).symm
  · intro γ hc
    rw [etaMultiplier_mul_T, kroneckerMultiplier_mul_T γ hc,
      mul_right_inj' (Complex.exp_ne_zero _)]
  · intro γ hc hd ih
    rw [etaMultiplier_mul_S γ hd, kroneckerMultiplier_mul_S γ hc hd,
      mul_right_inj' (Complex.exp_ne_zero _)] at ih
    exact ih

/-- **The Kronecker-symbol formula for the eta multiplier, odd `c` case** (Strömberg, Remark 2.5,
equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` odd,
`ε(γ) = (d / c) exp(2 π i ((a + d) c - b d (c² - 1) - 3 c) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_c_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = (kroneckerSym (γ 1 1) (γ 1 0) : ℂ) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  rw [etaMultiplier_eq_kroneckerMultiplier γ hc, kroneckerMultiplier, ite_eq_left hodd,
    kroneckerExpOdd]

/-- **The Kronecker-symbol formula for the eta multiplier, even `c` case** (Strömberg, Remark 2.5,
equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` even,
`ε(γ) = (c / d) exp(2 π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_c_even (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (heven : Even (γ 1 0)) :
    etaMultiplier γ = (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  rw [etaMultiplier_eq_kroneckerMultiplier γ hc, kroneckerMultiplier,
    ite_eq_right (Int.not_odd_iff_even.mpr heven), kroneckerExpEven]

end TauCeti.ModularForm
