/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Analysis.Complex.Sqrt

/-!
# Explicit Dedekind-sum and Kronecker-symbol formulas for the eta multiplier

`TauCeti.ModularForm.etaMultiplier` attaches to each `γ = (a b; c d) ∈ SL(2, ℤ)` the 24th root of
unity `ε(γ)` satisfying `η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane with the principal
square root (`TauCeti.ModularForm.eta_smul`). The generator laws
`TauCeti.ModularForm.etaMultiplier_mul_T_zpow` (`ε(γ Tⁿ) = e^{π i n / 12} ε(γ)`),
`TauCeti.ModularForm.etaMultiplier_mul_S` (`ε(γ S) = e^{-π i / 4} ε(γ)` for `d > 0`), and
`TauCeti.ModularForm.etaMultiplier_of_c_eq_one` supply the Euclidean induction steps and base case.

This file evaluates `ε(γ)` across all of `SL(2, ℤ)` in two classical closed forms:

1. **Dedekind's formula in terms of `TauCeti.dedekindSum`** (Apostol, Theorem 3.4):
   * for `c > 0`, `ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, proved by strong induction
     on `c` along the Euclidean steps `γ ↦ γ T^{-⌊d/c⌋}` and `γ₁ ↦ γ₁ S`, using Dedekind's
     reciprocity law `TauCeti.dedekindSum_add_dedekindSum`;
   * for `c < 0`, `ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`, obtained from `ε(-γ)` and
     the branch jump `√(-c τ - d) = -i √(c τ + d)` (`etaMultiplier_neg_of_c_neg`);
   * for `c = 0`, `ε(γ) = e^{π i b / 12}` when `d = 1` and `-i e^{-π i b / 12}` when `d = -1`;
   * for every lower-triangular transvection `(1 0; c 1)`, `ε(γ) = e^{-π i c / 12}` for all
     `c ∈ ℤ`.

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

* `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`: `ε(-γ) = ±i ε(γ)` for `c ≷ 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_neg`: `ε(γ)` when `c = 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_pos`, `TauCeti.ModularForm.eta_smul_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_pos_eq_sum_fract`,
  `TauCeti.ModularForm.etaMultiplier_of_c_neg`: Dedekind's Dedekind-sum transformation formulas.
* `TauCeti.ModularForm.etaMultiplier_of_b_eq_zero_of_d_eq_one`: `ε((1 0; c 1)) = e^{-π i c / 12}`.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_odd`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_d_odd`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_c_even`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym`: the Kronecker-symbol formulas.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4.
* H. Rademacher, *Topics in Analytic Number Theory*, Grundlehren 169, §§71–73.
* M. Newman, *Construction and application of a class of modular functions (II)*, Proc. London
  Math. Soc. (3) 9 (1959), 373–387.
* F. Strömberg, *Weil representations associated to finite quadratic modules*, Math. Z. 275
  (2013), 509–527, Remark 2.5, eq. (2.5).
-/

public section

open Complex ModularGroup ZMod
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Determinant, parity, and Euclidean-induction helpers on `SL(2, ℤ)` -/

private theorem det_eq_one (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
  (Matrix.det_fin_two _).symm.trans γ.det_coe

private theorem isCoprime_d_c (γ : SL(2, ℤ)) : IsCoprime (γ 1 1) (γ 1 0) :=
  ⟨γ 0 0, -γ 0 1, by linear_combination det_eq_one γ⟩

private theorem entries_of_c_eq_zero {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) :
    γ 0 0 = 1 ∧ γ 1 1 = 1 ∨ γ 0 0 = -1 ∧ γ 1 1 = -1 := by
  have hdet := det_eq_one γ
  rw [hc, mul_zero, sub_zero] at hdet
  exact Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet

private theorem c_eq_one_of_c_nonneg_of_d_eq_zero {γ : SL(2, ℤ)} (hc : 0 ≤ γ 1 0)
    (hd : γ 1 1 = 0) : γ 1 0 = 1 := by
  have hdet := det_eq_one γ
  rw [hd, mul_zero, zero_sub, neg_mul_eq_neg_mul] at hdet
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

private theorem odd_d_of_even_c (γ : SL(2, ℤ)) (hc : Even (γ 1 0)) : Odd (γ 1 1) := by
  have hdet := det_eq_one γ
  obtain ⟨kc, hkc⟩ := hc
  rcases Int.even_or_odd (γ 1 1) with ⟨kd, hkd⟩ | hd
  · exfalso
    rw [hkc, hkd] at hdet
    have : 2 * (γ 0 0 * kd - γ 0 1 * kc) = 1 := by linear_combination hdet
    omega
  · exact hd

private theorem odd_a_of_even_c (γ : SL(2, ℤ)) (hc : Even (γ 1 0)) : Odd (γ 0 0) := by
  have hdet := det_eq_one γ
  obtain ⟨kc, hkc⟩ := hc
  rcases Int.even_or_odd (γ 0 0) with ⟨ka, hka⟩ | ha
  · exfalso
    rw [hkc, hka] at hdet
    have : 2 * (ka * γ 1 1 - γ 0 1 * kc) = 1 := by linear_combination hdet
    omega
  · exact ha

private theorem mul_T_zpow_entries (γ : SL(2, ℤ)) (n : ℤ) :
    (γ * T ^ n) 0 0 = γ 0 0 ∧ (γ * T ^ n) 0 1 = γ 0 0 * n + γ 0 1 ∧
      (γ * T ^ n) 1 0 = γ 1 0 ∧ (γ * T ^ n) 1 1 = γ 1 1 + γ 1 0 * n := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm]

private theorem mul_S_entries (γ : SL(2, ℤ)) :
    (γ * S) 0 0 = γ 0 1 ∧ (γ * S) 0 1 = -γ 0 0 ∧
      (γ * S) 1 0 = γ 1 1 ∧ (γ * S) 1 1 = -γ 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]

/-- Euclidean strong induction on `c = γ 1 0 > 0`: any function `F : SL(2, ℤ) → ℂ` that agrees with
`etaMultiplier` at `(a b; 1 0)` and transforms like `etaMultiplier` under right multiplication by
`T ^ n` and `S` (when `c, d > 0`) agrees with `etaMultiplier` on `{γ | 0 < γ 1 0}`. -/
private theorem etaMultiplier_eq_of_c_pos_ind {F : SL(2, ℤ) → ℂ}
    (hbase : ∀ γ : SL(2, ℤ), γ 1 0 = 1 → γ 1 1 = 0 → etaMultiplier γ = F γ)
    (hT : ∀ (γ : SL(2, ℤ)) (n : ℤ), 0 < γ 1 0 → F (γ * T ^ n) = cexp (π * I * n / 12) * F γ)
    (hS : ∀ γ : SL(2, ℤ), 0 < γ 1 0 → 0 < γ 1 1 → cexp (π * I / 4) * F (γ * S) = F γ)
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = F γ := by
  suffices ∀ (n : ℕ) (γ : SL(2, ℤ)), γ 1 0 = n → 0 < n → etaMultiplier γ = F γ from
    this (γ 1 0).toNat γ (Int.toNat_of_nonneg hc.le).symm (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro γ hcn hn
    have hc : 0 < γ 1 0 := by omega
    let q : ℤ := γ 1 1 / γ 1 0
    let γ₁ : SL(2, ℤ) := γ * T ^ (-q)
    have hγ : γ = γ₁ * T ^ q := by simp [γ₁, mul_assoc, zpow_neg]
    have hc₁ : γ₁ 1 0 = γ 1 0 := (mul_T_zpow_entries γ (-q)).2.2.1
    have hd₁ : γ₁ 1 1 = γ 1 1 + γ 1 0 * (-q) := (mul_T_zpow_entries γ (-q)).2.2.2
    have hr : γ₁ 1 1 = γ 1 1 % γ 1 0 := by
      rw [hd₁, mul_neg, ← sub_eq_add_neg]
      exact (Int.emod_def (γ 1 1) (γ 1 0)).symm
    have hr_nonneg : 0 ≤ γ₁ 1 1 := hr ▸ Int.emod_nonneg _ hc.ne'
    have hr_lt : γ₁ 1 1 < γ 1 0 := hr ▸ Int.emod_lt_of_pos _ hc
    rw [hγ, etaMultiplier_mul_T_zpow, hT γ₁ q (hc₁ ▸ hc)]
    congr 1
    rcases hr_nonneg.eq_or_lt with hr0 | hr_pos
    · exact hbase γ₁ (c_eq_one_of_c_nonneg_of_d_eq_zero (hc₁ ▸ hc.le) hr0.symm) hr0.symm
    · have hm : (γ₁ * S) 1 0 = (γ₁ 1 1).toNat := by
        rw [(mul_S_entries γ₁).2.2.1, Int.toNat_of_nonneg hr_pos.le]
      have ihS := ih (γ₁ 1 1).toNat (by omega) (γ₁ * S) hm (by omega)
      have hcancel : cexp (π * I / 4) * etaMultiplier (γ₁ * S) = etaMultiplier γ₁ := by
        rw [etaMultiplier_mul_S γ₁ hr_pos, ← mul_assoc, ← Complex.exp_add]
        simp
      rw [← hcancel, ihS, hS γ₁ (hc₁ ▸ hc) hr_pos]

/-! ### Negation `-γ` and upper-triangular elements (`c = 0`) -/

/-- For `γ ∈ SL(2, ℤ)` with `c > 0`, negating `γ` multiplies `ε(γ)` by `i`: `-γ` acts as `γ` on
the upper half-plane while `√(-c τ - d) = -i √(c τ + d)`. -/
theorem etaMultiplier_neg_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have him : 0 < ((γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1).im := by
    simpa using (Int.cast_pos.mpr hc : (0 : ℝ) < γ 1 0)
  have hneg : ((-γ) 1 0 : ℂ) * UpperHalfPlane.I + (-γ) 1 1 =
      -((γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1) := by
    simp [neg_add_rev, add_comm]
  rw [SL_neg_smul, eta_smul, hneg, Complex.sqrt_neg_of_im_pos him]
  linear_combination etaMultiplier γ * Complex.sqrt ((γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1) *
    η UpperHalfPlane.I * I_sq

/-- For `γ ∈ SL(2, ℤ)` with `c < 0`, negating `γ` multiplies `ε(γ)` by `-i`. -/
theorem etaMultiplier_neg_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  have hc' : 0 < (-γ) 1 0 := by simpa using hc
  have h := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at h
  linear_combination I * h + etaMultiplier (-γ) * I_sq

/-- An upper-triangular element `(1 b; 0 1) ∈ SL(2, ℤ)` has `ε(γ) = e^{π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  rcases entries_of_c_eq_zero hc with ⟨ha1, hd1⟩ | ⟨_, hd1⟩
  · have hγ : γ = T ^ (γ 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, ha1, hc, hd1]
    rw [congrArg etaMultiplier hγ, etaMultiplier_T_zpow]
  · omega

/-- An upper-triangular element `(-1 b; 0 -1) ∈ SL(2, ℤ)` has `ε(γ) = -i e^{-π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  rcases entries_of_c_eq_zero hc with ⟨_, hd1⟩ | ⟨ha1, hd1⟩
  · omega
  · have hγ : -γ = T ^ (-γ 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, ha1, hc, hd1]
    refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
    have hsmul : γ • UpperHalfPlane.I = T ^ (-γ 0 1) • UpperHalfPlane.I := by
      rw [← hγ, SL_neg_smul]
    have hdenom : (γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1 = -1 := by simp [hc, hd1]
    rw [hsmul, coe_T_zpow_smul_eq, eta_add_intCast, hdenom, Complex.sqrt_neg_one]
    simp only [Int.cast_neg, mul_neg, neg_div]
    linear_combination cexp (-(π * I * γ 0 1 / 12)) * η UpperHalfPlane.I * I_sq

/-- For any upper-triangular `γ ∈ SL(2, ℤ)` (`c = 0`), `ε(γ)` is `e^{π i b / 12}` when `d > 0`
and `-i e^{-π i b / 12}` when `d < 0`. -/
theorem etaMultiplier_of_c_eq_zero (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    etaMultiplier γ =
      if 0 < γ 1 1 then cexp (π * I * γ 0 1 / 12) else -I * cexp (-(π * I * γ 0 1 / 12)) := by
  split_ifs with hd
  · exact etaMultiplier_of_c_eq_zero_of_d_pos γ hc hd
  · rcases entries_of_c_eq_zero hc with ⟨_, hd1⟩ | ⟨_, hd1⟩
    · omega
    · exact etaMultiplier_of_c_eq_zero_of_d_neg γ hc (by omega)

/-! ### Dedekind's formula in terms of `dedekindSum` -/

/-- The Dedekind-sum phase formula for `ε(γ)` when `c > 0`. -/
private noncomputable def dedekindForm (γ : SL(2, ℤ)) : ℂ :=
  cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4))

private theorem dedekindForm_mul_T_zpow (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) (n : ℤ) :
    dedekindForm (γ * T ^ n) = cexp (π * I * n / 12) * dedekindForm γ := by
  obtain ⟨ha, _, hc', hd⟩ := mul_T_zpow_entries γ n
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  rw [dedekindForm, dedekindForm, ha, hc', hd, dedekindSum_add_self_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

private theorem dedekindForm_of_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    cexp (π * I / 4) * dedekindForm (γ * S) = dedekindForm γ := by
  obtain ⟨ha, _, hc', hd'⟩ := mul_S_entries γ
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  have hdC : (γ 1 1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne'
  have hrec := congrArg (Rat.cast : ℚ → ℂ) (dedekindSum_add_dedekindSum hd hc (isCoprime_d_c γ))
  push_cast at hrec
  have hs : (dedekindSum (γ 1 0) (γ 1 1) : ℂ) =
      ((γ 1 1 : ℂ) ^ 2 + (γ 1 0 : ℂ) ^ 2 + 1) / (12 * γ 1 1 * γ 1 0) - 1 / 4 -
        dedekindSum (γ 1 1) (γ 1 0) := by linear_combination hrec
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast det_eq_one γ
  rw [dedekindForm, dedekindForm, ha, hc', hd', dedekindSum_neg, Rat.cast_neg, sub_neg_eq_add,
    hs, ← Complex.exp_add]
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
  etaMultiplier_eq_of_c_pos_ind
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
theorem etaMultiplier_of_c_pos_eq_sum_fract (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * (γ 1 0 : ℂ)) -
        ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
          (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) -
        1 / 4)) := by
  have hsum : ((dedekindSum (γ 1 1) (γ 1 0) : ℚ) : ℂ) =
      ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
        (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) := by
    rw [(isCoprime_d_c γ).dedekindSum_eq, ← Complex.ofReal_ratCast]
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
  have hneg := etaMultiplier_neg_of_c_neg γ hc
  have hpi : π * I / 2 = π / 2 * I := by ring
  have hI : etaMultiplier γ = cexp (π * I / 2) * etaMultiplier (-γ) := by
    rw [hpi, exp_pi_div_two_mul_I]
    linear_combination -I * hneg + etaMultiplier γ * I_sq
  rw [hI, etaMultiplier_of_c_pos (-γ) hc', ← Complex.exp_add]
  congr 1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, dedekindSum_neg,
    Rat.cast_neg]
  field_simp
  ring

/-- Every lower-triangular transvection `(1 0; c 1) ∈ SL(2, ℤ)` has `ε(γ) = e^{-π i c / 12}`, for
all `c ∈ ℤ` (positive, zero, or negative). -/
theorem etaMultiplier_of_b_eq_zero_of_d_eq_one (γ : SL(2, ℤ)) (hb : γ 0 1 = 0) (hd : γ 1 1 = 1) :
    etaMultiplier γ = cexp (-(π * I * γ 1 0 / 12)) := by
  have ha : γ 0 0 = 1 := by
    have hdet := det_eq_one γ
    rw [hb, hd, mul_one, zero_mul, sub_zero] at hdet
    exact hdet
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
    rw [etaMultiplier_of_c_neg γ hc, ha, hd, dedekindSum_one_left (by omega)]
    congr 1
    push_cast
    field_simp
    ring
  · rw [etaMultiplier_of_c_eq_zero_of_d_pos γ hc (by omega), hb, hc]
    simp
  · have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
    rw [etaMultiplier_of_c_pos γ hc, ha, hd, dedekindSum_one_left hc.le]
    congr 1
    push_cast
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

private theorem cexp_pi_I_int_div_twelve_eq_of_dvd {x y : ℤ} (h : 24 ∣ x - y) :
    cexp (π * I * (x : ℂ) / 12) = cexp (π * I * (y : ℂ) / 12) := by
  obtain ⟨k, hk⟩ := h
  have hx : π * I * (x : ℂ) / 12 = π * I * (y : ℂ) / 12 + (k : ℤ) * (2 * π * I) := by
    have hk' : (x : ℂ) = (y : ℂ) + 24 * (k : ℂ) := by
      have : x = y + 24 * k := by omega
      exact_mod_cast this
    rw [hk']
    ring
  rw [hx, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

private theorem cexp_pi_I_int_div_twelve_eq_neg_of_dvd {x y : ℤ} (h : 24 ∣ x - y - 12) :
    cexp (π * I * (x : ℂ) / 12) = -cexp (π * I * (y : ℂ) / 12) := by
  obtain ⟨k, hk⟩ := h
  have hx : π * I * (x : ℂ) / 12 = π * I * (y : ℂ) / 12 + π * I + (k : ℤ) * (2 * π * I) := by
    have hk' : (x : ℂ) = (y : ℂ) + 12 + 24 * (k : ℂ) := by
      have : x = y + 12 + 24 * k := by omega
      exact_mod_cast this
    rw [hk']
    ring
  rw [hx, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add, exp_pi_mul_I,
    mul_neg_one]

private theorem twentyFour_dvd_mul_sq_sub_one {c : ℤ} (hc : Odd c) :
    24 ∣ c * (c ^ 2 - 1) := by
  have h8 : 8 ∣ c * (c ^ 2 - 1) := by
    obtain ⟨k, rfl⟩ := hc
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨(4 * m + 1) * m * (2 * m + 1), by ring⟩
    · exact ⟨(4 * m + 3) * (2 * m + 1) * (m + 1), by ring⟩
  have h3 : 3 ∣ c * (c ^ 2 - 1) := by
    have hr : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    let q := c / 3
    rcases hr with h | h | h
    · have hc' : c = 3 * q := by omega
      exact ⟨q * ((3 * q) ^ 2 - 1), by rw [hc']; ring⟩
    · have hc' : c = 3 * q + 1 := by omega
      exact ⟨(3 * q + 1) * q * (3 * q + 2), by rw [hc']; ring⟩
    · have hc' : c = 3 * q + 2 := by omega
      exact ⟨(3 * q + 2) * (3 * q + 1) * (q + 1), by rw [hc']; ring⟩
  exact isCoprime_eight_three.mul_dvd h8 h3

private theorem kroneckerOddForm_mul_T (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hodd : Odd (γ 1 0)) :
    kroneckerOddForm (γ * T) = cexp (π * I / 12) * kroneckerOddForm γ := by
  obtain ⟨ha, hb, hc', hd⟩ := mul_T_zpow_entries γ 1
  simp only [zpow_one, mul_one] at ha hb hc' hd
  have hcodd : Odd (γ 1 0).natAbs := Int.natAbs_odd.mpr hodd
  have hc_abs : ((γ 1 0).natAbs : ℤ) = γ 1 0 := Int.natAbs_of_nonneg hc.le
  have hk : kroneckerSym (γ 1 1 + γ 1 0) (γ 1 0) = kroneckerSym (γ 1 1) (γ 1 0) := by
    have h1 := kroneckerSym_eq_jacobiSym (γ 1 1 + γ 1 0) hcodd
    have h2 := kroneckerSym_eq_jacobiSym (γ 1 1) hcodd
    rw [hc_abs] at h1 h2
    rw [h1, h2]
    exact jacobiSym.mod_left' (by rw [hc_abs]; simp)
  have hdiff : oddPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 1 + γ 1 0) -
      (oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) =
      -(γ 0 0 + 2 * γ 0 1) * (γ 1 0 * (γ 1 0 ^ 2 - 1)) := by
    unfold oddPhaseInt
    linear_combination -((γ 1 0) ^ 2 - 1) * det_eq_one γ
  have hdvd : 24 ∣ oddPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 1 + γ 1 0) -
      (oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) := by
    rw [hdiff]
    exact dvd_mul_of_dvd_right (twentyFour_dvd_mul_sq_sub_one hodd) _
  rw [kroneckerOddForm, kroneckerOddForm, ha, hb, hc', hd, hk,
    cexp_pi_I_int_div_twelve_eq_of_dvd hdvd]
  rw [Int.cast_add, Int.cast_one, mul_add, mul_one, add_div, Complex.exp_add]
  ring

private theorem three_dvd_evenPhase_T_diff (a b c : ℤ) :
    3 ∣ -c * (c - 1) * ((a + 2 * b) * (c + 1) + 3) := by
  have hr : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
  let q := c / 3
  rcases hr with h | h | h
  · have hc' : c = 3 * q := by omega
    exact ⟨-q * (3 * q - 1) * ((a + 2 * b) * (3 * q + 1) + 3), by rw [hc']; ring⟩
  · have hc' : c = 3 * q + 1 := by omega
    exact ⟨-(3 * q + 1) * q * ((a + 2 * b) * (3 * q + 2) + 3), by rw [hc']; ring⟩
  · have hc' : c = 3 * q + 2 := by omega
    exact ⟨-(3 * q + 2) * (3 * q + 1) * ((a + 2 * b) * (q + 1) + 1), by rw [hc']; ring⟩

private theorem eight_dvd_evenPhase_T_diff_of_mod_two (γ : SL(2, ℤ)) (hc2 : γ 1 0 % 4 = 2) :
    (γ 1 1 % 4 = 1 →
      8 ∣ -γ 1 0 * (γ 1 0 - 1) * ((γ 0 0 + 2 * γ 0 1) * (γ 1 0 + 1) + 3) - 12) ∧
    (γ 1 1 % 4 = 3 →
      8 ∣ -γ 1 0 * (γ 1 0 - 1) * ((γ 0 0 + 2 * γ 0 1) * (γ 1 0 + 1) + 3)) := by
  have hdet := det_eq_one γ
  let qc := γ 1 0 / 4
  let qd := γ 1 1 / 4
  have hc_eq : γ 1 0 = 4 * qc + 2 := by omega
  refine ⟨fun hd1 ↦ ?_, fun hd3 ↦ ?_⟩
  · have hd_eq : γ 1 1 = 4 * qd + 1 := by omega
    let qu := γ 0 1 * (qc + 1) - γ 0 0 * qd
    have hu_eq : γ 0 0 + 2 * γ 0 1 = 4 * qu + 1 := by
      have hdet' := hdet
      rw [hc_eq, hd_eq] at hdet'
      dsimp only [qu]
      linear_combination hdet'
    rw [hc_eq, hu_eq]
    let A := 4 * qc ^ 2 + 3 * qc
    let B := 4 * qc * qu + 3 * qu + qc + 1
    exact ⟨-(2 * A * B + A + B + 2), by dsimp only [A, B]; ring⟩
  · have hd_eq : γ 1 1 = 4 * qd + 3 := by omega
    let qu := γ 0 0 * (qd + 1) - γ 0 1 * qc - 1
    have hu_eq : γ 0 0 + 2 * γ 0 1 = 4 * qu + 3 := by
      have hdet' := hdet
      rw [hc_eq, hd_eq] at hdet'
      dsimp only [qu]
      linear_combination -hdet'
    rw [hc_eq, hu_eq]
    exact ⟨-(2 * qc + 1) * (4 * qc + 1) * (4 * qu * qc + 3 * qu + 3 * qc + 3), by ring⟩

private theorem kroneckerEvenForm_mul_T (γ : SL(2, ℤ)) (heven : Even (γ 1 0)) :
    kroneckerEvenForm (γ * T) = cexp (π * I / 12) * kroneckerEvenForm γ := by
  obtain ⟨ha, hb, hc', hd⟩ := mul_T_zpow_entries γ 1
  simp only [zpow_one, mul_one] at ha hb hc' hd
  have hdiff : evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 1 + γ 1 0) -
      (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) =
      -γ 1 0 * (γ 1 0 - 1) * ((γ 0 0 + 2 * γ 0 1) * (γ 1 0 + 1) + 3) := by
    unfold evenPhaseInt
    linear_combination -((γ 1 0) ^ 2 - 1) * det_eq_one γ
  have h3 : 3 ∣ evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 1 + γ 1 0) -
      (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) := by
    rw [hdiff]; exact three_dvd_evenPhase_T_diff (γ 0 0) (γ 0 1) (γ 1 0)
  have hc4 : γ 1 0 % 4 = 0 ∨ γ 1 0 % 4 = 2 := by obtain ⟨k, hk⟩ := heven; omega
  rw [kroneckerEvenForm, kroneckerEvenForm, ha, hb, hc', hd]
  rcases hc4 with hc0 | hc2
  · have hmod : γ 1 0 ≡ 0 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk : kroneckerSym (γ 1 0) (γ 1 1 + γ 1 0) = kroneckerSym (γ 1 0) (γ 1 1) :=
      kroneckerSym_mod_right' (.inl hmod) (by simp)
    obtain ⟨qa, ha_eq⟩ := odd_a_of_even_c γ heven
    let qc := γ 1 0 / 4
    have hc_eq : γ 1 0 = 4 * qc := by omega
    have h8 : 8 ∣ evenPhaseInt (γ 0 0) (γ 0 0 + γ 0 1) (γ 1 0) (γ 1 1 + γ 1 0) -
        (evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) + 1) := by
      rw [hdiff, hc_eq, ha_eq]
      exact ⟨-qc * (4 * qc - 1) * ((qa + γ 0 1) * (4 * qc + 1) + 2 * qc + 2), by ring⟩
    rw [hk, cexp_pi_I_int_div_twelve_eq_of_dvd (isCoprime_eight_three.mul_dvd h8 h3),
      Int.cast_add, Int.cast_one, mul_add, mul_one, add_div, Complex.exp_add]
    ring
  · have hmod : γ 1 0 ≡ 2 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk := kroneckerSym_add_self_right_of_modEq_two hmod (γ 1 1)
    have hd4 : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3 := by
      obtain ⟨k, hk'⟩ := odd_d_of_even_c γ heven; omega
    have h8_pair := eight_dvd_evenPhase_T_diff_of_mod_two γ hc2
    rcases hd4 with hd1 | hd3
    · have hχ : (χ₄ (γ 1 1) : ℤ) = 1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
      have h8 := hdiff ▸ h8_pair.1 hd1
      have h3' := dvd_sub h3 (by norm_num : (3 : ℤ) ∣ 12)
      rw [hk, hχ, cexp_pi_I_int_div_twelve_eq_neg_of_dvd (isCoprime_eight_three.mul_dvd h8 h3'),
        Int.cast_add, Int.cast_one, mul_add, mul_one, add_div, Complex.exp_add]
      push_cast
      ring
    · have hχ : (χ₄ (γ 1 1) : ℤ) = -1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
      have h8 := hdiff ▸ h8_pair.2 hd3
      rw [hk, hχ, cexp_pi_I_int_div_twelve_eq_of_dvd (isCoprime_eight_three.mul_dvd h8 h3),
        Int.cast_add, Int.cast_one, mul_add, mul_one, add_div, Complex.exp_add]
      push_cast
      ring

private theorem kroneckerForm_mul_T (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    kroneckerForm (γ * T) = cexp (π * I / 12) * kroneckerForm γ := by
  have hc' : (γ * T) 1 0 = γ 1 0 := by simpa using (mul_T_zpow_entries γ 1).2.2.1
  rw [kroneckerForm, kroneckerForm, hc']
  split_ifs with hodd
  · exact kroneckerOddForm_mul_T γ hc hodd
  · exact kroneckerEvenForm_mul_T γ (Int.not_odd_iff_even.mp hodd)

private theorem kroneckerForm_mul_T_zpow (γ : SL(2, ℤ)) (n : ℤ) (hc : 0 < γ 1 0) :
    kroneckerForm (γ * T ^ n) = cexp (π * I * n / 12) * kroneckerForm γ := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hc_k : 0 < (γ * T ^ (k : ℤ)) 1 0 := by
      rw [(mul_T_zpow_entries γ k).2.2.1]; exact hc
    rw [zpow_add_one, ← mul_assoc, kroneckerForm_mul_T _ hc_k, ih, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  | pred k ih =>
    have hc_k : 0 < (γ * T ^ (-(k : ℤ) - 1)) 1 0 := by
      rw [(mul_T_zpow_entries γ (-(k : ℤ) - 1)).2.2.1]; exact hc
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
  have hdiff : evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) -
      oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) = -3 * (γ 1 0 - 1) * (γ 1 1 - 1) := by
    unfold evenPhaseInt oddPhaseInt; ring
  have hc4 : γ 1 0 % 4 = 1 ∨ γ 1 0 % 4 = 3 := by obtain ⟨k, hk⟩ := hcodd; omega
  rw [kroneckerOddForm, kroneckerEvenForm]
  rcases hc4 with hc1 | hc3
  · have hD : γ 1 0 ≡ 1 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk : kroneckerSym (γ 1 1) (γ 1 0) = kroneckerSym (γ 1 0) (γ 1 1) :=
      hJ.trans (kroneckerSym_eq_jacobiSym_natAbs hD (γ 1 1)).symm
    let qc := γ 1 0 / 4; obtain ⟨qd, hqd⟩ := hdodd
    have hc_eq : γ 1 0 = 4 * qc + 1 := by omega
    have hdvd : 24 ∣ evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) -
        oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
      rw [hdiff, hc_eq, hqd]; exact ⟨-qc * qd, by ring⟩
    rw [hk, cexp_pi_I_int_div_twelve_eq_of_dvd hdvd]
  · have hD : -γ 1 0 ≡ 1 [ZMOD 4] := by rw [Int.ModEq]; omega
    have hk : kroneckerSym (γ 1 1) (γ 1 0) = χ₄ (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
      have h1 : kroneckerSym (-γ 1 0) (γ 1 1) = kroneckerSym (γ 1 1) (γ 1 0) := by
        rw [kroneckerSym_eq_jacobiSym_natAbs hD (γ 1 1), Int.natAbs_neg, hJ]
      rw [← h1, neg_eq_neg_one_mul, kroneckerSym_mul_left (by norm_num) hc.ne',
        kroneckerSym_neg_one_left_of_odd hdodd]
    let qc := γ 1 0 / 4; have hc_eq : γ 1 0 = 4 * qc + 3 := by omega
    have hd4 : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3 := by obtain ⟨k, hk'⟩ := hdodd; omega
    rcases hd4 with hd1 | hd3
    · have hχ : (χ₄ (γ 1 1) : ℤ) = 1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
      let qd := γ 1 1 / 4; have hd_eq : γ 1 1 = 4 * qd + 1 := by omega
      have hdvd : 24 ∣ evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) -
          oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
        rw [hdiff, hc_eq, hd_eq]; exact ⟨-(2 * qc + 1) * qd, by ring⟩
      rw [hk, hχ, cexp_pi_I_int_div_twelve_eq_of_dvd hdvd]
      push_cast; ring
    · have hχ : (χ₄ (γ 1 1) : ℤ) = -1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
      let qd := γ 1 1 / 4; have hd_eq : γ 1 1 = 4 * qd + 3 := by omega
      have hdvd : 24 ∣ evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) -
          oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) - 12 := by
        rw [hdiff, hc_eq, hd_eq]; exact ⟨-(2 * qc * qd + qc + qd + 1), by ring⟩
      rw [hk, hχ, cexp_pi_I_int_div_twelve_eq_neg_of_dvd hdvd]
      push_cast; ring

private theorem kroneckerOddForm_mul_S_of_even (γ : SL(2, ℤ)) (hd : 0 < γ 1 1) :
    cexp (π * I / 4) * kroneckerEvenForm (γ * S) = kroneckerOddForm γ := by
  obtain ⟨ha, hb, hc', hd'⟩ := mul_S_entries γ
  have hk := kroneckerSym_neg_right_of_nonneg hd.le (γ 1 0)
  have hphase : evenPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3 =
      oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
    unfold evenPhaseInt oddPhaseInt
    linear_combination -γ 1 0 * γ 1 1 * det_eq_one γ
  have hexp : cexp (π * I / 4) *
      cexp (π * I * (evenPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) : ℂ) / 12) =
      cexp (π * I * (oddPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) : ℂ) / 12) := by
    rw [← Complex.exp_add, ← hphase]
    congr 1
    push_cast
    ring
  rw [kroneckerEvenForm, kroneckerOddForm, ha, hb, hc', hd', hk, ← mul_assoc,
    mul_comm (cexp (π * I / 4)), mul_assoc, hexp]

private theorem kroneckerEvenForm_mul_S_of_odd (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0)
    (hdodd : Odd (γ 1 1)) :
    cexp (π * I / 4) * kroneckerOddForm (γ * S) = kroneckerEvenForm γ := by
  obtain ⟨ha, hb, hc', hd'⟩ := mul_S_entries γ
  have hk : kroneckerSym (-γ 1 0) (γ 1 1) = χ₄ (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
    rw [neg_eq_neg_one_mul, kroneckerSym_mul_left (by norm_num) hc,
      kroneckerSym_neg_one_left_of_odd hdodd]
  have hdiff : (oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3) -
      evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) = -6 * (γ 1 1 - 1) := by
    unfold oddPhaseInt evenPhaseInt
    linear_combination -γ 1 0 * γ 1 1 * det_eq_one γ
  have hexp1 : cexp (π * I / 4) *
      cexp (π * I * (oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) : ℂ) / 12) =
      cexp (π * I * ((oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3 : ℤ) : ℂ) / 12) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [kroneckerOddForm, kroneckerEvenForm, ha, hb, hc', hd', hk, ← mul_assoc,
    mul_comm (cexp (π * I / 4)), mul_assoc, hexp1]
  have hd4 : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3 := by obtain ⟨k, hk'⟩ := hdodd; omega
  rcases hd4 with hd1 | hd3
  · have hχ : (χ₄ (γ 1 1) : ℤ) = 1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
    let qd := γ 1 1 / 4; have hd_eq : γ 1 1 = 4 * qd + 1 := by omega
    have hdvd : 24 ∣ (oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
      rw [hdiff, hd_eq]; exact ⟨-qd, by ring⟩
    rw [hχ, cexp_pi_I_int_div_twelve_eq_of_dvd hdvd]
    push_cast; ring
  · have hχ : (χ₄ (γ 1 1) : ℤ) = -1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
    let qd := γ 1 1 / 4; have hd_eq : γ 1 1 = 4 * qd + 3 := by omega
    have hdvd : 24 ∣ (oddPhaseInt (γ 0 1) (-γ 0 0) (γ 1 1) (-γ 1 0) + 3) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) - 12 := by
      rw [hdiff, hd_eq]; exact ⟨-(qd + 1), by ring⟩
    rw [hχ, cexp_pi_I_int_div_twelve_eq_neg_of_dvd hdvd]
    push_cast; ring

private theorem kroneckerForm_of_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    cexp (π * I / 4) * kroneckerForm (γ * S) = kroneckerForm γ := by
  rw [kroneckerForm, kroneckerForm, (mul_S_entries γ).2.2.1]
  split_ifs with hd_odd hc_odd hc_odd
  · rw [kroneckerEvenForm_mul_S_of_odd γ hc.ne' hd_odd,
      kroneckerOddForm_eq_kroneckerEvenForm γ hc hc_odd hd_odd]
  · exact kroneckerEvenForm_mul_S_of_odd γ hc.ne' hd_odd
  · exact kroneckerOddForm_mul_S_of_even γ hd
  · exact absurd (odd_d_of_even_c γ (Int.not_odd_iff_even.mp hc_odd)) hd_odd

private theorem etaMultiplier_eq_kroneckerForm (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = kroneckerForm γ :=
  etaMultiplier_eq_of_c_pos_ind
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
  have hI : etaMultiplier γ = cexp (π * I / 2) * etaMultiplier (-γ) := by
    have hneg := etaMultiplier_neg_of_c_neg γ hc
    have hpi : π * I / 2 = π / 2 * I := by ring
    rw [hpi, exp_pi_div_two_mul_I]
    linear_combination -I * hneg + etaMultiplier γ * I_sq
  have hk : kroneckerSym (-γ 1 0) (-γ 1 1) = χ₄ (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
    rw [kroneckerSym_neg_right_of_nonneg (by omega), neg_eq_neg_one_mul,
      kroneckerSym_mul_left (by norm_num) hc.ne, kroneckerSym_neg_one_left_of_odd hd]
  have hdiff : (evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) + 6) -
      evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) = -6 * (γ 1 1 - 1) := by
    unfold evenPhaseInt; ring
  have hexp : cexp (π * I / 2) *
      cexp (π * I * (evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) : ℂ) / 12) =
      cexp (π * I * ((evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) + 6 : ℤ) : ℂ) / 12) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hI, hpos, kroneckerEvenForm, kroneckerEvenForm]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  rw [hk, ← mul_assoc, mul_comm (cexp (π * I / 2)), mul_assoc, hexp]
  have hd4 : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3 := by obtain ⟨k, hk'⟩ := hd; omega
  rcases hd4 with hd1 | hd3
  · have hχ : (χ₄ (γ 1 1) : ℤ) = 1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
    let qd := γ 1 1 / 4; have hd_eq : γ 1 1 = 4 * qd + 1 := by omega
    have hdvd : 24 ∣ (evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) + 6) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
      rw [hdiff, hd_eq]; exact ⟨-qd, by ring⟩
    rw [hχ, cexp_pi_I_int_div_twelve_eq_of_dvd hdvd]
    push_cast; ring
  · have hχ : (χ₄ (γ 1 1) : ℤ) = -1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
    let qd := γ 1 1 / 4; have hd_eq : γ 1 1 = 4 * qd + 3 := by omega
    have hdvd : 24 ∣ (evenPhaseInt (-γ 0 0) (-γ 0 1) (-γ 1 0) (-γ 1 1) + 6) -
        evenPhaseInt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) - 12 := by
      rw [hdiff, hd_eq]; exact ⟨-(qd + 1), by ring⟩
    rw [hχ, cexp_pi_I_int_div_twelve_eq_neg_of_dvd hdvd]
    push_cast; ring

private theorem etaMultiplier_eq_kroneckerEvenForm_of_d_odd (γ : SL(2, ℤ)) (hd : Odd (γ 1 1)) :
    etaMultiplier γ = kroneckerEvenForm γ := by
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · exact etaMultiplier_eq_kroneckerEvenForm_of_d_odd_c_neg γ hc hd
  · rcases entries_of_c_eq_zero hc with ⟨_, hd1⟩ | ⟨_, hd1⟩
    · rw [etaMultiplier_of_c_eq_zero_of_d_pos γ hc (by omega), kroneckerEvenForm, hc, hd1,
        kroneckerSym_zero_left]
      unfold evenPhaseInt
      simp
    · have harg : π * I * ((evenPhaseInt (γ 0 0) (γ 0 1) 0 (-1) : ℤ) : ℂ) / 12 =
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
theorem etaMultiplier_eq_kroneckerSym_of_c_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
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
theorem etaMultiplier_eq_kroneckerSym_of_d_odd (γ : SL(2, ℤ)) (hd : Odd (γ 1 1)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 12) :=
  etaMultiplier_eq_kroneckerEvenForm_of_d_odd γ hd

/-- **The Kronecker-symbol formula for `ε(γ)` at even `c`** (Strömberg, Remark 2.5, eq. (2.5)):
for every `γ = (a b; c d) ∈ SL(2, ℤ)` with `c` even (of any sign, including `c = 0`),
`ε(γ) = (c / d) exp(π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_c_even (γ : SL(2, ℤ)) (hc : Even (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 12) :=
  etaMultiplier_eq_kroneckerSym_of_d_odd γ (odd_d_of_even_c γ hc)

/-- **The unified Kronecker-symbol formula for `ε(γ)`** (Strömberg, Remark 2.5, eq. (2.5)):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`, `ε(γ)` is given by `(d / c)` when `c` is odd and by
`(c / d)` when `c` is even. -/
theorem etaMultiplier_eq_kroneckerSym (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        kroneckerSym (γ 1 1) (γ 1 0) *
          cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) -
            3 * γ 1 0 : ℤ) : ℂ) / 12)
      else
        kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 12) :=
  etaMultiplier_eq_kroneckerForm γ hc

end TauCeti.ModularForm
