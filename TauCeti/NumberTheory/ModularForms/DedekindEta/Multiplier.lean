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

/-- Multiplying `cexp (2 π i (n + 12 k) / 24)` by `(-1) ^ k` cancels the shift. -/
private theorem negOnePow_mul_cexp_twentyFour_add_twelve_mul (n k : ℤ) :
    ((k.negOnePow : ℤ) : ℂ) * cexp (2 * π * I * ((n + 12 * k : ℤ) : ℂ) / 24) =
      cexp (2 * π * I * (n : ℂ) / 24) := by
  rw [show 2 * π * I * ((n + 12 * k : ℤ) : ℂ) / 24 =
      2 * π * I * (n : ℂ) / 24 + k * (π * I) by push_cast; ring,
    Complex.exp_add_int_mul_pi_mul_I, Int.cast_negOnePow, ← mul_assoc, ← mul_zpow,
    neg_one_mul, neg_neg, one_zpow, one_mul]

/-- An even lower-left entry in `SL(2, ℤ)` forces an odd lower-right entry by bottom-row
coprimality. -/
private theorem odd_d_of_even_c (γ : SL(2, ℤ)) (hc : Even (γ 1 0)) : Odd (γ 1 1) := by
  by_contra h
  exact absurd ((ModularGroup.bottom_row_coprime γ).isUnit_of_dvd'
    (even_iff_two_dvd.mp hc) (even_iff_two_dvd.mp (Int.not_odd_iff_even.mp h))) (by decide)

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
    rw [kroneckerExpOdd, kroneckerExpOdd, coe_mul_T]
    simp
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
  rw [kroneckerExpEven, kroneckerExpEven, coe_mul_T]
  simp
  linear_combination -(γ 1 0 ^ 2 - 1) * hdet

/-- For every `γ ∈ SL(2, ℤ)`, `kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1)` is divisible
by `3`. -/
private theorem three_dvd_kroneckerExpEven_mul_T_sub (γ : SL(2, ℤ)) :
    (3 : ℤ) ∣ kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) := by
  rw [kroneckerExpEven_mul_T_sub]
  exact dvd_sub ⟨-γ 1 0 * (γ 1 0 - 1), by ring⟩
    (dvd_mul_of_dvd_right (Int.three_dvd_mul_sq_sub_one (γ 1 0)) _)

/-- An integer product `a * b` with `2 ∣ a` and `4 ∣ b` vanishes in `ZMod 8`. -/
private theorem zmod8_mul_eq_zero_of_dvd {a b : ℤ} (ha : 2 ∣ a) (hb : 4 ∣ b) :
    ((a * b : ℤ) : ZMod 8) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr
    (by simpa [show ((8 : ℕ) : ℤ) = 2 * 4 by norm_num] using mul_dvd_mul ha hb)

/-- Exponent change in `kroneckerExpEven` under `γ ↦ γ * T` when `4 ∣ c`: it increases by
`1 (mod 24)`. -/
private theorem kroneckerExpEven_mul_T_of_emod_four_eq_zero (γ : SL(2, ℤ))
    (hc4 : γ 1 0 % 4 = 0) :
    ∃ k : ℤ, kroneckerExpEven (γ * T) = kroneckerExpEven γ + 1 + 24 * k := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have ha_odd : Odd (γ 0 0) := by
    by_contra h
    have ha2 : 2 ∣ γ 0 0 := even_iff_two_dvd.mp (Int.not_odd_iff_even.mp h)
    have hc2 : 2 ∣ γ 1 0 := Int.dvd_iff_emod_eq_zero.mpr (by omega)
    have h1 : (2 : ℤ) ∣ 1 :=
      hdet ▸ dvd_sub (dvd_mul_of_dvd_left ha2 _) (dvd_mul_of_dvd_right hc2 _)
    omega
  have hc4_dvd : (4 : ℤ) ∣ γ 1 0 := Int.dvd_of_emod_eq_zero hc4
  have hc_sq8 : ((γ 1 0 : ZMod 8) ^ 2) = 0 := by
    simpa [sq] using zmod8_mul_eq_zero_of_dvd
      (dvd_trans (by norm_num) hc4_dvd) hc4_dvd
  have hc_mul_odd8 : ((γ 1 0 * (3 + γ 0 0 + 2 * γ 0 1) : ℤ) : ZMod 8) = 0 := by
    obtain ⟨a', ha'⟩ := ha_odd
    have h2 : (2 : ℤ) ∣ 3 + γ 0 0 + 2 * γ 0 1 := ⟨2 + a' + γ 0 1, by rw [ha']; ring⟩
    simpa [mul_comm] using zmod8_mul_eq_zero_of_dvd h2 hc4_dvd
  have h8 : (8 : ℤ) ∣ kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp ?_
    rw [kroneckerExpEven_mul_T_sub]
    push_cast
    push_cast at hc_mul_odd8
    linear_combination (-3 - (γ 0 0 + 2 * γ 0 1) * γ 1 0 : ZMod 8) * hc_sq8 + hc_mul_odd8
  obtain ⟨k, hk⟩ := (by decide : IsCoprime (3 : ℤ) 8).mul_dvd
    (three_dvd_kroneckerExpEven_mul_T_sub γ) h8
  exact ⟨k, by linarith⟩

/-- Exponent change in `kroneckerExpEven` under `γ ↦ γ * T` when `c ≡ 2 (mod 4)`: it changes by
`1 + 12 k` where `(-1)^k = -χ₄ d`. -/
private theorem kroneckerExpEven_mul_T_of_emod_four_eq_two (γ : SL(2, ℤ))
    (hc4 : γ 1 0 % 4 = 2) :
    ∃ k : ℤ, kroneckerExpEven (γ * T) = kroneckerExpEven γ + 1 + 12 * k ∧
      (k.negOnePow : ℤ) = -χ₄ (γ 1 1) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hd_odd : Odd (γ 1 1) := odd_d_of_even_c γ (Int.even_iff.mpr (by omega))
  have hd2_mod : γ 1 1 % 2 = 1 := Int.odd_iff.mp hd_odd
  have h3 := three_dvd_kroneckerExpEven_mul_T_sub γ
  have hc_even : (2 : ℤ) ∣ γ 1 0 := Int.dvd_of_emod_eq_zero (by omega)
  have hc_sub2 : (4 : ℤ) ∣ γ 1 0 - 2 := Int.dvd_of_emod_eq_zero (by omega)
  -- From `a d - b c = 1`, `c ≡ 2 (mod 4)`, and odd `d`, we have `a + 2 b ≡ d (mod 4)`.
  have had_dvd : (4 : ℤ) ∣ γ 0 0 + 2 * γ 0 1 - γ 1 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp ?_
    have hd2 : ((γ 1 1 : ZMod 4) ^ 2 - 1) = 0 := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr
        (dvd_trans (by norm_num) (Int.eight_dvd_sq_sub_one_of_odd hd_odd))
    have hc2 : ((γ 1 0 : ZMod 4) - 2) = 0 := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hc_sub2
    have h2d : (2 : ZMod 4) * γ 1 1 - 2 = 0 := by
      obtain ⟨q, hq⟩ := hd_odd
      rw [hq]
      push_cast
      have h4 : (4 : ZMod 4) = 0 := by decide
      linear_combination q * h4
    have hdet_z4 : (γ 0 0 : ZMod 4) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := congrArg (Int.cast : ℤ → ZMod 4) hdet
      push_cast at h
      exact h
    have h4 : (4 : ZMod 4) = 0 := by decide
    push_cast
    linear_combination (γ 1 1 : ZMod 4) * hdet_z4 - (γ 0 0 : ZMod 4) * hd2 +
      (γ 0 1 * γ 1 1 : ZMod 4) * hc2 + (γ 0 1 : ZMod 4) * h2d + (γ 0 1 : ZMod 4) * h4
  have had_c8 : ((γ 1 0 * (γ 0 0 + 2 * γ 0 1 - γ 1 1) : ℤ) : ZMod 8) = 0 :=
    zmod8_mul_eq_zero_of_dvd hc_even had_dvd
  have hc_sub2_8 : ((γ 1 0 * (γ 1 0 - 2) : ℤ) : ZMod 8) = 0 :=
    zmod8_mul_eq_zero_of_dvd hc_even hc_sub2
  have hc_sq_sub4_8 : ((γ 1 0 ^ 2 - 4 : ℤ) : ZMod 8) = 0 := by
    rw [show γ 1 0 ^ 2 - 4 = (γ 1 0 + 2) * (γ 1 0 - 2) by ring]
    exact zmod8_mul_eq_zero_of_dvd (Int.dvd_of_emod_eq_zero (by omega)) hc_sub2
  have hmod8 : ((kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) : ℤ) : ZMod 8) =
      -3 * γ 1 0 * (1 + γ 1 1) := by
    rw [kroneckerExpEven_mul_T_sub]
    push_cast
    push_cast at had_c8 hc_sub2_8 hc_sq_sub4_8
    linear_combination -3 * hc_sub2_8 - 3 * had_c8 - (γ 0 0 + 2 * γ 0 1 : ZMod 8) *
      (γ 1 0 : ZMod 8) * hc_sq_sub4_8
  rcases (by omega : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3) with h1 | h3d
  · have h8' : (8 : ℤ) ∣ kroneckerExpEven (γ * T) - (kroneckerExpEven γ + 1) - 12 := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp ?_
      rw [Int.cast_sub, hmod8]
      have hcd8 : ((γ 1 0 * (γ 1 1 - 1) : ℤ) : ZMod 8) = 0 :=
        zmod8_mul_eq_zero_of_dvd hc_even (Int.dvd_of_emod_eq_zero (by omega))
      have h6c8 : ((6 * (γ 1 0 - 2) : ℤ) : ZMod 8) = 0 :=
        zmod8_mul_eq_zero_of_dvd (by norm_num : (2 : ℤ) ∣ 6) hc_sub2
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
        zmod8_mul_eq_zero_of_dvd hc_even (Int.dvd_of_emod_eq_zero (by omega))
      push_cast at hcd8
      linear_combination -3 * hcd8
    obtain ⟨u, hu⟩ := (by decide : IsCoprime (3 : ℤ) 8).mul_dvd h3 h8
    refine ⟨2 * u, by linarith, ?_⟩
    rw [Int.negOnePow_two_mul, Units.val_one, χ₄_int_three_mod_four h3d, neg_neg]

/-- Right translation step `γ ↦ γ * T` for `kroneckerMultiplier`. -/
private theorem kroneckerMultiplier_mul_T (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    kroneckerMultiplier (γ * T) = cexp (π * I / 12) * kroneckerMultiplier γ := by
  have hcT : (γ * T) 1 0 = γ 1 0 := by rw [coe_mul_T]; simp
  have hdT : (γ * T) 1 1 = γ 1 0 + γ 1 1 := by rw [coe_mul_T]; simp
  have hshift (n : ℤ) : cexp (π * I / 12) * cexp (2 * π * I * (n : ℂ) / 24) =
      cexp (2 * π * I * ((n + 1 : ℤ) : ℂ) / 24) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h24 (n k : ℤ) : cexp (2 * π * I * ((n + 24 * k : ℤ) : ℂ) / 24) =
      cexp (2 * π * I * (n : ℂ) / 24) := by
    rw [show 2 * π * I * ((n + 24 * k : ℤ) : ℂ) / 24 =
        2 * π * I * ((n : ℂ) / 24 + k) by push_cast; ring,
      Complex.exp_two_pi_mul_I_mul_add_intCast]
    ring_nf
  by_cases hodd : Odd (γ 1 0)
  · simp only [kroneckerMultiplier, hcT, hdT, ite_eq_left hodd]
    obtain ⟨k, hk⟩ := kroneckerExpOdd_mul_T γ hodd
    have hsym : kroneckerSym (γ 1 0 + γ 1 1) (γ 1 0) = kroneckerSym (γ 1 1) (γ 1 0) :=
      kroneckerSym_mod_left' hodd hc (Int.add_emod_left (γ 1 0) (γ 1 1))
    rw [hsym, hk, h24, ← hshift]
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
      rw [hsym, hk, h24, ← hshift]
      ring
    · obtain ⟨k, hk, hk_sign⟩ := kroneckerExpEven_mul_T_of_emod_four_eq_two γ hc2
      have hsym : kroneckerSym (γ 1 0) (γ 1 0 + γ 1 1) =
          -χ₄ (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
        rw [add_comm]
        exact kroneckerSym_add_self_right_of_emod_four_eq_two hc2 (γ 1 1)
      have hd_odd : Odd (γ 1 1) := odd_d_of_even_c γ (Int.not_odd_iff_even.mp hodd)
      have hχ4_sqC : ((χ₄ (γ 1 1) : ℤ) : ℂ) * ((χ₄ (γ 1 1) : ℤ) : ℂ) = 1 := by
        norm_cast
        exact χ₄_intCast_mul_self hd_odd
      rw [hsym, hk, show 2 * π * I * ((kroneckerExpEven γ + 1 + 12 * k : ℤ) : ℂ) / 24 =
          2 * π * I * ((kroneckerExpEven γ + 1 : ℤ) : ℂ) / 24 + k * (π * I) by push_cast; ring,
        Complex.exp_add_int_mul_pi_mul_I, ← Int.cast_negOnePow ℂ k, hk_sign, ← hshift]
      push_cast
      linear_combination (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        cexp (π * I / 12) * cexp (2 * π * I * (kroneckerExpEven γ : ℂ) / 24) * hχ4_sqC

/-- The universal polynomial change under right inversion `γ ↦ γ * S`:
`((b - c) d - a c (d² - 1)) - ((a + d) c - b d (c² - 1)) = -3 c d`. -/
private theorem kroneckerQuad_mul_S (γ : SL(2, ℤ)) :
    (((γ * S) 0 0 + (γ * S) 1 1) * (γ * S) 1 0 -
      (γ * S) 0 1 * (γ * S) 1 1 * ((γ * S) 1 0 ^ 2 - 1)) -
    ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1)) = -3 * γ 1 0 * γ 1 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  rw [coe_mul_S]
  simp
  linear_combination -γ 1 0 * γ 1 1 * hdet

/-- Right inversion step `γ ↦ γ * S` for `kroneckerMultiplier` when `c > 0` and `d > 0`. -/
private theorem kroneckerMultiplier_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    kroneckerMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerMultiplier γ := by
  have hcS : (γ * S) 1 0 = γ 1 1 := by rw [coe_mul_S]; simp
  have hdS : (γ * S) 1 1 = -γ 1 0 := by rw [coe_mul_S]; simp
  have hquad := kroneckerQuad_mul_S γ
  rw [hcS, hdS] at hquad
  suffices h : cexp (2 * π * I * (3 : ℂ) / 24) * kroneckerMultiplier (γ * S) =
      kroneckerMultiplier γ by
    have hmul := congrArg (cexp (-(π * I / 4)) * ·) h
    have hcancel : cexp (-(π * I / 4)) * cexp (2 * π * I * (3 : ℂ) / 24) = 1 := by
      rw [← Complex.exp_add]; convert Complex.exp_zero using 2; ring
    rwa [← mul_assoc, hcancel, one_mul] at hmul
  have hadd3 (n : ℤ) : cexp (2 * π * I * (3 : ℂ) / 24) * cexp (2 * π * I * (n : ℂ) / 24) =
      cexp (2 * π * I * ((n + 3 : ℤ) : ℂ) / 24) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  by_cases hc_odd : Odd (γ 1 0) <;> by_cases hd_odd : Odd (γ 1 1)
  · simp only [kroneckerMultiplier, hcS, hdS, ite_eq_left hc_odd, ite_eq_left hd_odd]
    rw [mul_left_comm, hadd3]
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
    rw [mul_left_comm, hadd3, kroneckerSym_neg_right_of_nonneg hd.le]
    have hexp : kroneckerExpEven (γ * S) + 3 = kroneckerExpOdd γ := by
      simp only [kroneckerExpEven, kroneckerExpOdd, hcS, hdS]
      linear_combination hquad
    rw [hexp]
  · simp only [kroneckerMultiplier, hcS, hdS, ite_eq_right hc_odd, ite_eq_left hd_odd]
    rw [mul_left_comm, hadd3]
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
  · exact absurd (odd_d_of_even_c γ (Int.not_odd_iff_even.mp hc_odd)) hd_odd

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
