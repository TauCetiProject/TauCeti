/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Data.Int.MulPred
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Explicit Dedekind-sum and Kronecker-symbol formulas for the eta multiplier

`TauCeti.ModularForm.etaMultiplier` attaches to each `γ = (a b; c d) ∈ SL(2, ℤ)` the 24th root of
unity `ε(γ)` satisfying `η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane with the principal
square root (`TauCeti.ModularForm.eta_smul`).
`TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation` establishes its generator laws,
Euclidean uniqueness principle
(`TauCeti.ModularForm.etaMultiplier_eq_of_mul_T_zpow_of_mul_S_of_c_pos`), negation laws, and values
at upper-triangular elements (`c = 0`) and lower transvections.

This file evaluates `ε(γ)` across `SL(2, ℤ)` in two classical closed forms:

1. **Dedekind's formula in terms of `TauCeti.dedekindSum`** (Apostol, Theorem 3.4):
   * for `c > 0`, `ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, proved by strong induction
     on `c` along the Euclidean steps `γ ↦ γ T^{-⌊d/c⌋}` and `γ₁ ↦ γ₁ S`, using Dedekind's
     reciprocity law `TauCeti.dedekindSum_add_dedekindSum`;
   * for `c < 0`, `ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`, obtained from `ε(-γ)` and
     the branch jump `√(-c τ - d) = i √(c τ + d)` (`TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`
     applied to `-γ`).

2. **The Rademacher–Petersson–Newman Kronecker-symbol formula** (Strömberg, Remark 2.5, eq. (2.5)):
   eliminating the Dedekind sum via the Kronecker symbol `TauCeti.kroneckerSym` expresses `ε(γ)` as
   a quadratic sign times a 24th root of unity polynomial in `(a, b, c, d)`:
   * for `c > 0` odd,
     `ε(γ) = (d / c) exp(π i ((a + d) c - b d (c² - 1) - 3 c) / 12)`;
   * for `d` odd (of any sign, and with `c` of any sign or parity, including `c = 0`),
     `ε(γ) = (c / d) exp(π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 12)`,
     which in particular covers every `γ ∈ SL(2, ℤ)` with even `c` (since `a d - b c = 1` forces
     `d` to be odd) and every `γ ∈ Γ₀(N)` with odd `d`.

## Main results

* `TauCeti.ModularForm.etaMultiplier_of_c_pos`, `TauCeti.ModularForm.eta_smul_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_eq_exp_sum_fract_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_neg`: Dedekind's Dedekind-sum transformation formulas.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_exp_of_c_pos_of_c_odd`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_exp_of_d_odd`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_exp_of_c_even`,
  `TauCeti.ModularForm.etaMultiplier_eq_ite_kroneckerSym_mul_exp_of_c_nonneg`: the
  Kronecker-symbol formulas.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4.
* H. Rademacher, *Topics in Analytic Number Theory*, Grundlehren 169, §§71–73.
* M. Newman, *Construction and application of a class of modular functions (II)*, Proc. London
  Math. Soc. (3) 9 (1959), 373–387.
* F. Strömberg, *Computation of Maass waveforms with nontrivial multiplier systems*, Math. Comp.
  77 (2008), 2375–2416 (arXiv:math/0611146v1, 2006), Remark 2.5, eq. (2.5).
-/

public section

open Complex ModularGroup ZMod
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Dedekind's formula in terms of `dedekindSum` -/

private theorem etaMultiplier_eq_exp_mul_etaMultiplier_neg_of_c_neg {γ : SL(2, ℤ)}
    (hc : γ 1 0 < 0) :
    etaMultiplier γ = cexp (π * I / 2) * etaMultiplier (-γ) := by
  have hc' : 0 < (-γ) 1 0 := by simpa using hc
  have h := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at h
  rw [h, show π * I / 2 = π / 2 * I by ring, exp_pi_div_two_mul_I]

/-- The Dedekind-sum phase formula for `ε(γ)` when `c > 0`. -/
private noncomputable def dedekindForm (γ : SL(2, ℤ)) : ℂ :=
  cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4))

private theorem dedekindForm_mul_T_zpow (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) (n : ℤ) :
    dedekindForm (γ * T ^ n) = cexp (π * I * n / 12) * dedekindForm γ := by
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  rw [dedekindForm, dedekindForm, γ.mul_T_zpow_apply_zero_zero, γ.mul_T_zpow_apply_one_zero,
    γ.mul_T_zpow_apply_one_one, add_comm (γ 1 0 * n) (γ 1 1), dedekindSum_add_self_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

private theorem dedekindForm_of_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    cexp (π * I / 4) * dedekindForm (γ * S) = dedekindForm γ := by
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  have hdC : (γ 1 1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne'
  have hrec := congrArg (Rat.cast : ℚ → ℂ)
    (dedekindSum_add_dedekindSum hd hc (γ.isCoprime_row 1).symm)
  push_cast at hrec
  have hs : (dedekindSum (γ 1 0) (γ 1 1) : ℂ) =
      ((γ 1 1 : ℂ) ^ 2 + (γ 1 0 : ℂ) ^ 2 + 1) / (12 * γ 1 1 * γ 1 0) - 1 / 4 -
        dedekindSum (γ 1 1) (γ 1 0) := by linear_combination hrec
  have hdet := γ.intCast_fin_two_mul_sub_mul_eq_one (R := ℂ)
  rw [dedekindForm, dedekindForm, γ.mul_S_apply_zero_zero, γ.mul_S_apply_one_zero,
    γ.mul_S_apply_one_one, dedekindSum_neg, Rat.cast_neg, sub_neg_eq_add, hs, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  linear_combination -4 * hdet

/-- **Dedekind's formula for the eta multiplier** (Apostol, Theorem 3.4): for `γ = (a b; c d)` in
`SL(2, ℤ)` with `c > 0`,
`ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, where `s(d, c)` is `TauCeti.dedekindSum d c`
and the `-1/4` converts Apostol's branch of `√(-i (c τ + d))` to the principal root `√(c τ + d)`. -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) :=
  etaMultiplier_eq_of_mul_T_zpow_of_mul_S_of_c_pos
    (fun g hc1 _ ↦ by
      rw [etaMultiplier_of_c_eq_one g hc1, dedekindForm, hc1, dedekindSum_one_right]
      simp)
    (fun g n hg ↦ dedekindForm_mul_T_zpow g hg.ne' n)
    dedekindForm_of_mul_S γ hc

/-- **Dedekind's functional equation for `η`** (Apostol, Theorem 3.4): for `γ = (a b; c d)` in
`SL(2, ℤ)` with `c > 0` and `τ` in the upper half-plane,
`η(γ τ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4)) √(c τ + d) η(τ)`. -/
theorem eta_smul_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    η (γ • τ : ℍ) = cexp (π * I *
      (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) *
      Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [eta_smul, etaMultiplier_of_c_pos γ hc]

/-- Dedekind's formula for `ε(γ)` (`c > 0`) written directly with the finite sawtooth sum over
`r ∈ (0, c)`, using `Int.fract` on `ℝ`. -/
theorem etaMultiplier_eq_exp_sum_fract_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * (γ 1 0 : ℂ)) -
        ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
          (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) -
        1 / 4)) := by
  have hsum : ((dedekindSum (γ 1 1) (γ 1 0) : ℚ) : ℂ) =
      ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
        (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) := by
    rw [(γ.isCoprime_row 1).symm.dedekindSum_eq, ← Complex.ofReal_ratCast]
    push_cast [Rat.cast_fract]
    rfl
  rw [etaMultiplier_of_c_pos γ hc, hsum, Int.cast_add]

/-- For `γ = (a b; c d) ∈ SL(2, ℤ)` with `c < 0`,
`ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`. -/
theorem etaMultiplier_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) + dedekindSum (γ 1 1) (-γ 1 0) + 1 / 4)) := by
  have hc' : 0 < (-γ) 1 0 := by simpa using hc
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
  rw [etaMultiplier_eq_exp_mul_etaMultiplier_neg_of_c_neg hc, etaMultiplier_of_c_pos (-γ) hc',
    ← Complex.exp_add]
  congr 1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, dedekindSum_neg,
    Rat.cast_neg]
  field_simp
  ring

/-! ### The Kronecker-symbol formulas -/

private def oddPhaseInt (a b c d : ℤ) : ℤ :=
  (a + d) * c - b * d * (c ^ 2 - 1) - 3 * c

private def evenPhaseInt (a b c d : ℤ) : ℤ :=
  (a + d) * c - b * d * (c ^ 2 - 1) + 3 * d - 3 - 3 * c * d

private noncomputable def kroneckerOddForm (γ : SL(2, ℤ)) : ℂ :=
  kroneckerSym (γ 1 1) (γ 1 0) *
    cexp (π * I * (oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) : ℂ) / 12)

private noncomputable def kroneckerEvenForm (γ : SL(2, ℤ)) : ℂ :=
  kroneckerSym (γ 1 0) (γ 1 1) *
    cexp (π * I * (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) : ℂ) / 12)

private noncomputable def kroneckerForm (γ : SL(2, ℤ)) : ℂ :=
  if Odd (γ 1 0) then kroneckerOddForm γ else kroneckerEvenForm γ

private theorem isCoprime_eight_three : IsCoprime (8 : ℤ) 3 :=
  ⟨2, -5, by norm_num⟩

private theorem chi4_mul_cexp_pi_mul_I_div_twelve {x y d : ℤ} (hd : Odd d)
    (hdvd : 24 ∣ x - y + 6 * (d - 1)) :
    (χ₄ d : ℂ) * cexp (π * I * (x : ℂ) / 12) = cexp (π * I * (y : ℂ) / 12) := by
  obtain ⟨k, hk⟩ := hd
  rcases (by omega : d % 4 = 1 ∨ d % 4 = 3) with hd1 | hd3
  · have h6 : (24 : ℤ) ∣ 6 * (d - 1) :=
      ⟨d / 4, by omega⟩
    have hxy : (2 * 12 : ℤ) ∣ x - y := by simpa using dvd_sub hdvd h6
    rw [ZMod.χ₄_int_one_mod_four hd1, Int.cast_one, one_mul]
    exact Complex.exp_pi_mul_I_mul_div_eq_of_dvd (n := 12) hxy
  · have h6 : (24 : ℤ) ∣ 6 * (d - 1) + 12 :=
      ⟨d / 4 + 1, by omega⟩
    have hxy : (2 * 12 : ℤ) ∣ x - y - 12 := by
      have hsub := dvd_sub hdvd h6
      rwa [show x - y + 6 * (d - 1) - (6 * (d - 1) + 12) = x - y - 12 by ring,
        show (24 : ℤ) = 2 * 12 by norm_num] at hsub
    have hexp : cexp (π * I * (x : ℂ) / 12) = -cexp (π * I * (y : ℂ) / 12) :=
      Complex.exp_pi_mul_I_mul_div_eq_neg_of_dvd (n := 12) (by norm_num) hxy
    rw [ZMod.χ₄_int_three_mod_four hd3, Int.cast_neg, Int.cast_one, hexp, neg_one_mul, neg_neg]

private theorem kroneckerOddForm_mul_T (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hodd : Odd (γ 1 0)) :
    kroneckerOddForm (γ * T) = cexp (π * I / 12) * kroneckerOddForm γ := by
  have hcodd : Odd (γ 1 0).natAbs := Int.natAbs_odd.mpr hodd
  have hc_abs : ((γ 1 0).natAbs : ℤ) = γ 1 0 := Int.natAbs_of_nonneg hc.le
  have hk : kroneckerSym (γ 1 0 + γ 1 1) (γ 1 0) = kroneckerSym (γ 1 1) (γ 1 0) := by
    have h1 := kroneckerSym_eq_jacobiSym (γ 1 0 + γ 1 1) hcodd
    have h2 := kroneckerSym_eq_jacobiSym (γ 1 1) hcodd
    rw [hc_abs] at h1 h2
    rw [h1, h2]
    exact jacobiSym.mod_left' (by rw [hc_abs]; simp)
  have hdiff : oddPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
      (oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) =
      -(γ 0 0 + 2 * γ 0 1) * (γ 1 0 * (γ 1 0 ^ 2 - 1)) := by
    unfold oddPhaseInt
    linear_combination -((γ 1 0) ^ 2 - 1) * γ.fin_two_mul_sub_mul_eq_one
  have hdvd : (2 * 12 : ℤ) ∣ oddPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
      (oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) := by
    rw [hdiff, show (2 * 12 : ℤ) = 24 by norm_num]
    exact dvd_mul_of_dvd_right (Int.twentyFour_dvd_mul_sq_sub_one_of_odd hodd) _
  have hexp :
      cexp (π * I * (oddPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) : ℂ) / 12) =
        cexp (π * I * ((oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1 : ℤ) : ℂ) / 12) :=
    Complex.exp_pi_mul_I_mul_div_eq_of_dvd (n := 12) hdvd
  rw [kroneckerOddForm, kroneckerOddForm, γ.mul_T_apply_zero_zero, γ.mul_T_apply_zero_one,
    γ.mul_T_apply_one_zero, γ.mul_T_apply_one_one, hk, hexp,
    Int.cast_add, Int.cast_one, mul_add, mul_one, add_div, Complex.exp_add]
  ring

private theorem kroneckerEvenForm_mul_T (γ : SL(2, ℤ)) (heven : Even (γ 1 0)) :
    kroneckerEvenForm (γ * T) = cexp (π * I / 12) * kroneckerEvenForm γ := by
  have hdiff : evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
      (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) =
      -(γ 0 0 + 2 * γ 0 1) * (γ 1 0 * (γ 1 0 ^ 2 - 1)) - 3 * γ 1 0 * (γ 1 0 - 1) := by
    unfold evenPhaseInt
    linear_combination -((γ 1 0) ^ 2 - 1) * γ.fin_two_mul_sub_mul_eq_one
  have h3 : 3 ∣ evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
      (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) := by
    rw [hdiff]
    exact dvd_sub (dvd_mul_of_dvd_right (Int.three_dvd_mul_sq_sub_one _) _)
      ⟨γ 1 0 * (γ 1 0 - 1), by ring⟩
  have hc4 : γ 1 0 % 4 = 0 ∨ γ 1 0 % 4 = 2 := by obtain ⟨k, hk⟩ := heven; omega
  rw [kroneckerEvenForm, kroneckerEvenForm, γ.mul_T_apply_zero_zero, γ.mul_T_apply_zero_one,
    γ.mul_T_apply_one_zero, γ.mul_T_apply_one_one]
  rcases hc4 with hc0 | hc2
  · have hmod : γ 1 0 ≡ 0 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk : kroneckerSym (γ 1 0) (γ 1 0 + γ 1 1) = kroneckerSym (γ 1 0) (γ 1 1) :=
      kroneckerSym_mod_right' (.inl hmod) (by simp)
    obtain ⟨qa, ha_eq⟩ :=
      Matrix.SpecialLinearGroup.odd_apply_zero_zero_of_even_apply_one_zero heven
    let qc := γ 1 0 / 4
    have hc_eq : γ 1 0 = 4 * qc := by omega
    have h8 : 8 ∣ evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
        (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) := by
      rw [hdiff, hc_eq, ha_eq]
      exact ⟨-qc * (4 * qc - 1) * ((qa + γ 0 1) * (4 * qc + 1) + 2 * qc + 2), by ring⟩
    have hdvd : (2 * 12 : ℤ) ∣ evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
        (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) := by
      simpa using isCoprime_eight_three.mul_dvd h8 h3
    have hexp :
        cexp (π * I * (evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) : ℂ) / 12) =
          cexp (π * I * ((evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1 : ℤ) : ℂ) / 12) :=
      Complex.exp_pi_mul_I_mul_div_eq_of_dvd (n := 12) hdvd
    rw [hk, hexp, Int.cast_add, Int.cast_one, mul_add, mul_one, add_div, Complex.exp_add]
    ring
  · have hmod : γ 1 0 ≡ 2 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk : kroneckerSym (γ 1 0) (γ 1 0 + γ 1 1) =
        χ₄ ((-γ 1 1 : ℤ) : ZMod 4) * kroneckerSym (γ 1 0) (γ 1 1) := by
      rw [add_comm (γ 1 0) (γ 1 1), kroneckerSym_add_self_right_of_modEq_two hmod (γ 1 1),
        Int.cast_neg]
      congr 1
      generalize ((γ 1 1 : ℤ) : ZMod 4) = x
      revert x
      decide
    have hd_odd : Odd (-γ 1 1) :=
      odd_neg.mpr (Matrix.SpecialLinearGroup.odd_apply_one_one_of_even_apply_one_zero heven)
    have h8 : 8 ∣ evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
        (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) + 6 * (-γ 1 1 - 1) := by
      rw [hdiff]
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp ?_
      have hdet := γ.intCast_fin_two_mul_sub_mul_eq_one (R := ZMod 8)
      have hc_eq : γ 1 0 = 4 * (γ 1 0 / 4) + 2 := by omega
      rw [hc_eq] at hdet ⊢
      push_cast at hdet ⊢
      generalize ((γ 0 0 : ℤ) : ZMod 8) = a, ((γ 0 1 : ℤ) : ZMod 8) = b,
        ((γ 1 0 / 4 : ℤ) : ZMod 8) = qc, ((γ 1 1 : ℤ) : ZMod 8) = d at hdet ⊢
      revert a b qc d
      decide
    have h3' : 3 ∣ evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 0 + γ 1 1) -
        (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) + 6 * (-γ 1 1 - 1) :=
      dvd_add h3 ⟨2 * (-γ 1 1 - 1), by ring⟩
    have hexp := chi4_mul_cexp_pi_mul_I_div_twelve hd_odd (isCoprime_eight_three.mul_dvd h8 h3')
    rw [hk, Int.cast_mul, mul_right_comm, hexp, Int.cast_add, Int.cast_one, mul_add, mul_one,
      add_div, Complex.exp_add]
    ring

private theorem kroneckerForm_mul_T (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    kroneckerForm (γ * T) = cexp (π * I / 12) * kroneckerForm γ := by
  rw [kroneckerForm, kroneckerForm, γ.mul_T_apply_one_zero]
  split_ifs with hodd
  · exact kroneckerOddForm_mul_T γ hc hodd
  · exact kroneckerEvenForm_mul_T γ (Int.not_odd_iff_even.mp hodd)

private theorem kroneckerForm_mul_T_zpow (γ : SL(2, ℤ)) (n : ℤ) (hc : 0 < γ 1 0) :
    kroneckerForm (γ * T ^ n) = cexp (π * I * n / 12) * kroneckerForm γ := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hc_k : 0 < (γ * T ^ (k : ℤ)) 1 0 := by
      rw [γ.mul_T_zpow_apply_one_zero]; exact hc
    rw [zpow_add_one, ← mul_assoc, kroneckerForm_mul_T _ hc_k, ih, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  | pred k ih =>
    have hc_k : 0 < (γ * T ^ (-(k : ℤ) - 1)) 1 0 := by
      rw [γ.mul_T_zpow_apply_one_zero]; exact hc
    have hmul : γ * T ^ (-(k : ℤ) - 1) * T = γ * T ^ (-(k : ℤ)) := by
      rw [mul_assoc, ← zpow_add_one]
      congr 2
      omega
    have h := kroneckerForm_mul_T _ hc_k
    rw [hmul, ih] at h
    have hinv : cexp (-(π * I / 12)) * cexp (π * I / 12) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    calc
      kroneckerForm (γ * T ^ (-(k : ℤ) - 1)) =
          cexp (-(π * I / 12)) * (cexp (π * I / 12) * kroneckerForm (γ * T ^ (-(k : ℤ) - 1))) := by
        rw [← mul_assoc, hinv, one_mul]
      _ = cexp (-(π * I / 12)) * (cexp (π * I * ↑(-(k : ℤ)) / 12) * kroneckerForm γ) := by
        rw [← h]
      _ = cexp (π * I * ↑(-(k : ℤ) - 1) / 12) * kroneckerForm γ := by
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring

/-- When both `c > 0` and `d` are odd, `kroneckerOddForm γ` and `kroneckerEvenForm γ` agree. -/
private theorem kroneckerOddForm_eq_kroneckerEvenForm (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hcodd : Odd (γ 1 0)) (hdodd : Odd (γ 1 1)) :
    kroneckerOddForm γ = kroneckerEvenForm γ := by
  have hcodd' : Odd (γ 1 0).natAbs := Int.natAbs_odd.mpr hcodd
  have hc_abs : ((γ 1 0).natAbs : ℤ) = γ 1 0 := Int.natAbs_of_nonneg hc.le
  have hJ : kroneckerSym (γ 1 1) (γ 1 0) = jacobiSym (γ 1 1) (γ 1 0).natAbs := by
    have h := kroneckerSym_eq_jacobiSym (γ 1 1) hcodd'
    rwa [hc_abs] at h
  have hc4 : γ 1 0 % 4 = 1 ∨ γ 1 0 % 4 = 3 := by obtain ⟨k, hk⟩ := hcodd; omega
  rw [kroneckerOddForm, kroneckerEvenForm]
  rcases hc4 with hc1 | hc3
  · have hD : γ 1 0 ≡ 1 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk : kroneckerSym (γ 1 1) (γ 1 0) = kroneckerSym (γ 1 0) (γ 1 1) :=
      hJ.trans (kroneckerSym_eq_jacobiSym_natAbs hD (γ 1 1)).symm
    let qc := γ 1 0 / 4; obtain ⟨qd, hqd⟩ := hdodd
    have hc_eq : γ 1 0 = 4 * qc + 1 := by omega
    have hdvd : (2 * 12 : ℤ) ∣ oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
      unfold oddPhaseInt evenPhaseInt
      rw [hc_eq, hqd]
      exact ⟨qc * qd, by ring⟩
    rw [hk]
    congr 1
    exact Complex.exp_pi_mul_I_mul_div_eq_of_dvd (n := 12) hdvd
  · have hD : -γ 1 0 ≡ 1 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk : kroneckerSym (γ 1 1) (γ 1 0) = χ₄ (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
      have h1 : kroneckerSym (-γ 1 0) (γ 1 1) = kroneckerSym (γ 1 1) (γ 1 0) := by
        rw [kroneckerSym_eq_jacobiSym_natAbs hD (γ 1 1), Int.natAbs_neg, hJ]
      rw [← h1, neg_eq_neg_one_mul, kroneckerSym_mul_left (by norm_num) hc.ne',
        kroneckerSym_neg_one_left_of_odd hdodd]
    let qc := γ 1 0 / 4
    rcases id hdodd with ⟨qd, hqd⟩
    have hc_eq : γ 1 0 = 4 * qc + 3 := by omega
    have hdvd : 24 ∣ oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 6 * (γ 1 1 - 1) := by
      unfold oddPhaseInt evenPhaseInt
      rw [hc_eq, hqd]
      exact ⟨(qc + 1) * qd, by ring⟩
    rw [hk, Int.cast_mul, mul_right_comm, chi4_mul_cexp_pi_mul_I_div_twelve hdodd hdvd, mul_comm]

private theorem kroneckerOddForm_mul_S_of_even (γ : SL(2, ℤ)) (hd : 0 < γ 1 1) :
    cexp (π * I / 4) * kroneckerEvenForm (γ * S) = kroneckerOddForm γ := by
  have hk := kroneckerSym_neg_right_of_nonneg hd.le (γ 1 0)
  have hphase : evenPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3 =
      oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
    unfold evenPhaseInt oddPhaseInt
    linear_combination -γ 1 0 * γ 1 1 * γ.fin_two_mul_sub_mul_eq_one
  have hexp : cexp (π * I / 4) *
      cexp (π * I * (evenPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) : ℂ) / 12) =
      cexp (π * I * (oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) : ℂ) / 12) := by
    rw [← Complex.exp_add, ← hphase]
    congr 1
    push_cast
    ring
  rw [kroneckerEvenForm, kroneckerOddForm, γ.mul_S_apply_zero_zero, γ.mul_S_apply_zero_one,
    γ.mul_S_apply_one_zero, γ.mul_S_apply_one_one, hk, ← mul_assoc,
    mul_comm (cexp (π * I / 4)), mul_assoc, hexp]

private theorem kroneckerEvenForm_mul_S_of_odd (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0)
    (hdodd : Odd (γ 1 1)) :
    cexp (π * I / 4) * kroneckerOddForm (γ * S) = kroneckerEvenForm γ := by
  have hk : kroneckerSym (-γ 1 0) (γ 1 1) = χ₄ (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
    rw [neg_eq_neg_one_mul, kroneckerSym_mul_left (by norm_num) hc,
      kroneckerSym_neg_one_left_of_odd hdodd]
  have hdvd : 24 ∣ (oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3) -
      evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 6 * (γ 1 1 - 1) := by
    have hz : (oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 6 * (γ 1 1 - 1) = 0 := by
      unfold oddPhaseInt evenPhaseInt
      linear_combination -γ 1 0 * γ 1 1 * γ.fin_two_mul_sub_mul_eq_one
    rw [hz]
    exact dvd_zero 24
  have hexp1 : cexp (π * I / 4) *
      cexp (π * I * (oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) : ℂ) / 12) =
      cexp (π * I * ((oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3 : ℤ) : ℂ) / 12) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [kroneckerOddForm, kroneckerEvenForm, γ.mul_S_apply_zero_zero, γ.mul_S_apply_zero_one,
    γ.mul_S_apply_one_zero, γ.mul_S_apply_one_one, hk, ← mul_assoc,
    mul_comm (cexp (π * I / 4)), mul_assoc, hexp1, Int.cast_mul, mul_right_comm,
    chi4_mul_cexp_pi_mul_I_div_twelve hdodd hdvd, mul_comm]

private theorem kroneckerForm_of_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    cexp (π * I / 4) * kroneckerForm (γ * S) = kroneckerForm γ := by
  rw [kroneckerForm, kroneckerForm, γ.mul_S_apply_one_zero]
  split_ifs with hd_odd hc_odd hc_odd
  · rw [kroneckerEvenForm_mul_S_of_odd γ hc.ne' hd_odd,
      kroneckerOddForm_eq_kroneckerEvenForm γ hc hc_odd hd_odd]
  · exact kroneckerEvenForm_mul_S_of_odd γ hc.ne' hd_odd
  · exact kroneckerOddForm_mul_S_of_even γ hd
  · exact absurd
      (Matrix.SpecialLinearGroup.odd_apply_one_one_of_even_apply_one_zero
        (Int.not_odd_iff_even.mp hc_odd))
      hd_odd

private theorem etaMultiplier_eq_kroneckerForm (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = kroneckerForm γ :=
  etaMultiplier_eq_of_mul_T_zpow_of_mul_S_of_c_pos
    (fun g hc1 hd0 ↦ by
      rw [etaMultiplier_of_c_eq_one g hc1, kroneckerForm, hc1]
      simp only [odd_one, ↓reduceIte]
      rw [kroneckerOddForm, hc1, hd0, kroneckerSym_one_right, Int.cast_one, one_mul]
      unfold oddPhaseInt
      congr 1
      push_cast
      ring)
    kroneckerForm_mul_T_zpow
    kroneckerForm_of_mul_S γ hc

private theorem etaMultiplier_eq_kroneckerEvenForm_of_d_odd_c_neg (γ : SL(2, ℤ))
    (hc : γ 1 0 < 0) (hd : Odd (γ 1 1)) :
    etaMultiplier γ = kroneckerEvenForm γ := by
  have hc' : 0 < (-γ) 1 0 := by simpa using hc
  have hd' : Odd ((-γ) 1 1) := by simpa using hd
  have hpos : etaMultiplier (-γ) = kroneckerEvenForm (-γ) := by
    rw [etaMultiplier_eq_kroneckerForm (-γ) hc', kroneckerForm]
    split_ifs with hodd
    · exact kroneckerOddForm_eq_kroneckerEvenForm (-γ) hc' hodd hd'
    · rfl
  have hk : kroneckerSym (-γ 1 0) (-γ 1 1) = χ₄ (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
    rw [kroneckerSym_neg_right_of_nonneg (by omega), neg_eq_neg_one_mul,
      kroneckerSym_mul_left (by norm_num) hc.ne, kroneckerSym_neg_one_left_of_odd hd]
  have hdvd : 24 ∣ (evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) + 6) -
      evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 6 * (γ 1 1 - 1) := by
    have hz : (evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) + 6) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 6 * (γ 1 1 - 1) = 0 := by
      unfold evenPhaseInt; ring
    rw [hz]
    exact dvd_zero 24
  have hexp : cexp (π * I / 2) *
      cexp (π * I * (evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) : ℂ) / 12) =
      cexp (π * I * ((evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) + 6 : ℤ) : ℂ) / 12) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [etaMultiplier_eq_exp_mul_etaMultiplier_neg_of_c_neg hc, hpos, kroneckerEvenForm,
    kroneckerEvenForm]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  rw [hk, ← mul_assoc, mul_comm (cexp (π * I / 2)), mul_assoc, hexp, Int.cast_mul,
    mul_right_comm, chi4_mul_cexp_pi_mul_I_div_twelve hd hdvd, mul_comm]

private theorem etaMultiplier_eq_kroneckerEvenForm_of_d_odd (γ : SL(2, ℤ)) (hd : Odd (γ 1 1)) :
    etaMultiplier γ = kroneckerEvenForm γ := by
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · exact etaMultiplier_eq_kroneckerEvenForm_of_d_odd_c_neg γ hc hd
  · rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hγ | hγ
    · have hd1 : γ 1 1 = 1 := by
        simpa [coe_T_zpow] using congrArg (fun g : SL(2, ℤ) ↦ g 1 1) hγ
      rw [etaMultiplier_of_c_eq_zero_of_d_pos γ hc (by omega), kroneckerEvenForm, hc, hd1,
        kroneckerSym_zero_left]
      unfold evenPhaseInt
      simp
    · have hd1 : γ 1 1 = -1 := by
        simpa [coe_T_zpow] using congrArg (fun g : SL(2, ℤ) ↦ g 1 1) hγ
      have harg : π * I * ((evenPhaseInt (γ 0 0) (γ 0 1) 0 (-1) : ℤ) : ℂ) / 12 =
          -(π / 2 * I) + -(π * I * γ 0 1 / 12) := by
        unfold evenPhaseInt; push_cast; ring
      rw [etaMultiplier_of_c_eq_zero_of_d_neg γ hc (by omega), kroneckerEvenForm, hc, hd1,
        kroneckerSym_zero_left, harg, Complex.exp_add]
      simp [Complex.exp_neg, exp_pi_div_two_mul_I]
  · rw [etaMultiplier_eq_kroneckerForm γ hc, kroneckerForm]
    split_ifs with hodd
    · exact kroneckerOddForm_eq_kroneckerEvenForm γ hc hodd hd
    · rfl

/-- **The Kronecker-symbol formula for `ε(γ)` at odd `c > 0`** (Strömberg, Remark 2.5, eq. (2.5)):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` odd,
`ε(γ) = (d / c) exp(π i ((a + d) c - b d (c² - 1) - 3 c) / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_exp_of_c_pos_of_c_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) -
        3 * γ 1 0 : ℤ) : ℂ) / 12) := by
  rw [etaMultiplier_eq_kroneckerForm γ hc, kroneckerForm]
  simp only [hodd, ↓reduceIte]
  rfl

/-- **The Kronecker-symbol formula for `ε(γ)` at odd `d`**: for every `γ = (a b; c d) ∈ SL(2, ℤ)`
with `d` odd (of either sign, and with `c` of any sign or parity, including `c = 0`),
`ε(γ) = (c / d) exp(π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_exp_of_d_odd (γ : SL(2, ℤ)) (hd : Odd (γ 1 1)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 12) :=
  etaMultiplier_eq_kroneckerEvenForm_of_d_odd γ hd

/-- **The Kronecker-symbol formula for `ε(γ)` at even `c`** (Strömberg, Remark 2.5, eq. (2.5)):
for every `γ = (a b; c d) ∈ SL(2, ℤ)` with `c` even (of any sign, including `c = 0`),
`ε(γ) = (c / d) exp(π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_exp_of_c_even (γ : SL(2, ℤ)) (hc : Even (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 12) :=
  etaMultiplier_eq_kroneckerSym_mul_exp_of_d_odd γ
    (Matrix.SpecialLinearGroup.odd_apply_one_one_of_even_apply_one_zero hc)

/-- **The unified Kronecker-symbol formula for `ε(γ)`** (Strömberg, Remark 2.5, eq. (2.5)):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c ≥ 0`, `ε(γ)` is given by the `(d / c)` formula
(`etaMultiplier_eq_kroneckerSym_mul_exp_of_c_pos_of_c_odd`) when `c` is odd and by the `(c / d)`
formula (`etaMultiplier_eq_kroneckerSym_mul_exp_of_c_even`) when `c` is even. -/
theorem etaMultiplier_eq_ite_kroneckerSym_mul_exp_of_c_nonneg (γ : SL(2, ℤ)) (hc : 0 ≤ γ 1 0) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        kroneckerSym (γ 1 1) (γ 1 0) *
          cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) -
            3 * γ 1 0 : ℤ) : ℂ) / 12)
      else
        kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 12) := by
  split_ifs with hodd
  · exact etaMultiplier_eq_kroneckerSym_mul_exp_of_c_pos_of_c_odd γ
      (hc.lt_of_ne' (by rintro h0; exact absurd (h0 ▸ hodd) (by decide))) hodd
  · exact etaMultiplier_eq_kroneckerSym_mul_exp_of_c_even γ (Int.not_odd_iff_even.mp hodd)

end TauCeti.ModularForm
