/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Analysis.Complex.Sqrt

/-!
# The Dedekind-sum formula for the eta multiplier

This file evaluates the 24th root of unity `TauCeti.ModularForm.etaMultiplier γ` in the
transformation law `η(γ τ) = ε(γ) √(c τ + d) η(τ)` of the Dedekind eta function for every
`γ = (a b; c d) ∈ SL(2, ℤ)` in terms of the Dedekind sum `TauCeti.dedekindSum`:

* when `0 < c`, `ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`
  (`TauCeti.ModularForm.etaMultiplier_of_c_pos`), where the `-1/4` converts `√(-i (c τ + d))` to
  the principal square root `√(c τ + d)`;
* under negation `γ ↦ -γ`, `ε(-γ) = i ε(γ)` when `0 < c` and `ε(-γ) = -i ε(γ)` when `c < 0`
  (`TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`);
* when `c < 0`, `ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`
  (`TauCeti.ModularForm.etaMultiplier_of_c_neg`);
* when `c = 0`, `γ = ±T^{±b}`, giving `exp(π i b / 12)` for `0 < d` and
  `-i exp(-π i b / 12)` for `d < 0` (`TauCeti.ModularForm.etaMultiplier_of_c_eq_zero`).

## Implementation notes

For `0 < c`, the proof inducts strongly on `c` along the Euclidean algorithm on `(d, c)`. Right
multiplication by `T ^ (-q)` with `q = d / c` reduces `d` to `r = d % c`, which lies strictly
between `0` and `c` when `1 < c`; right multiplication by `S` then swaps `(c, r)` to `(r, -c)` via
`etaMultiplier_mul_S`, and Dedekind's reciprocity law `dedekindSum_add_dedekindSum` combines with
`a r - b₁ c = 1` to match the exponents (`dedekindRhs_mul_S`).

## Main results

* `TauCeti.ModularForm.etaMultiplier_of_c_pos`: the Dedekind-sum formula for `ε(γ)` when `0 < c`.
* `TauCeti.ModularForm.etaMultiplier_eq_cexp_sum_fract_of_c_pos`: the same formula with `s(d, c)`
  expanded as a sum of `Int.fract` terms over `ℝ`.
* `TauCeti.ModularForm.eta_smul_of_c_pos`,
  `TauCeti.ModularForm.exists_pow_twentyFour_eq_one_and_eta_smul`: Dedekind's functional equation
  for `η` under `SL(2, ℤ)`.
* `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`: the transformation of `ε(γ)` under `γ ↦ -γ`
  for `c ≠ 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_neg`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero`: the explicit formulas when `c < 0` and `c = 0`.
* `TauCeti.ModularForm.etaMultiplier_of_b_eq_zero_of_d_eq_one`: `ε(1 0; c 1) = exp(-π i c / 12)`
  for every lower-triangular transvection in `SL(2, ℤ)`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4.
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, Chapter 4.
-/

public section

open Complex ModularGroup
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Auxiliary lemmas for the Euclidean induction -/

/-- The Dedekind-sum expression `exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))` for `ε(γ)`. -/
private noncomputable def dedekindRhs (γ : SL(2, ℤ)) : ℂ :=
  cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4))

/-- Right multiplication by `Tⁿ` multiplies `dedekindRhs γ` by `exp(π i n / 12)`, matching
`etaMultiplier_mul_T_zpow`. -/
private theorem dedekindRhs_mul_T_zpow (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) (n : ℤ) :
    dedekindRhs (γ * T ^ n) = cexp (π * I * n / 12) * dedekindRhs γ := by
  have h00 : (γ * T ^ n) 0 0 = γ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (γ * T ^ n) 1 0 = γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (γ * T ^ n) 1 1 = γ 1 0 * n + γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  rw [dedekindRhs, dedekindRhs, h00, h10, h11, dedekindSum_self_mul_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Right multiplication by `S` multiplies `dedekindRhs γ` by `exp(-π i / 4)` when `0 < c` and
`0 < d`, matching `etaMultiplier_mul_S` via Dedekind's reciprocity law. -/
private theorem dedekindRhs_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    dedekindRhs (γ * S) = cexp (-(π * I / 4)) * dedekindRhs γ := by
  have h00 : (γ * S) 0 0 = γ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (γ * S) 1 0 = γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (γ * S) 1 1 = -γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hdetQ : (γ 0 0 : ℚ) * γ 1 1 - (γ 0 1 : ℚ) * γ 1 0 = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hrec := dedekindSum_add_dedekindSum hd hc (γ.isCoprime_row 1).symm
  have hcQ : (γ 1 0 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  have hdQ : (γ 1 1 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne'
  have hrat : ((γ 0 1 : ℚ) + -γ 1 0) / (12 * γ 1 1) - -dedekindSum (γ 1 0) (γ 1 1) - 1 / 4 =
      -(1 / 4) + (((γ 0 0 : ℚ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4) := by
    have hcd : dedekindSum (γ 1 0) (γ 1 1) =
        ((γ 1 1 : ℚ) ^ 2 + (γ 1 0 : ℚ) ^ 2 + 1) / (12 * γ 1 1 * γ 1 0) - 1 / 4 -
          dedekindSum (γ 1 1) (γ 1 0) := by
      linarith
    rw [hcd]
    field_simp
    linarith
  have hratC := congrArg (Rat.cast : ℚ → ℂ) hrat
  rw [dedekindRhs, dedekindRhs, h00, h10, h11, dedekindSum_neg, ← Complex.exp_add]
  congr 1
  push_cast at hratC ⊢
  linear_combination (π * I) * hratC

/-! ### The Dedekind-sum formula for `0 < c` -/

/-- Strong induction on `c` for `etaMultiplier_of_c_pos`. -/
private theorem etaMultiplier_eq_dedekindRhs_of_natCast :
    ∀ c : ℕ, 0 < c → ∀ γ : SL(2, ℤ), γ 1 0 = c → etaMultiplier γ = dedekindRhs γ := by
  intro c
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    intro hc γ hγc
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hc) with rfl | hc_gt_one
    · simp only [Nat.cast_one] at hγc
      rw [etaMultiplier_of_c_eq_one γ hγc, dedekindRhs, hγc, dedekindSum_one_right]
      simp
    · -- Reduce `d = γ 1 1` modulo `c` via `γ₁ = γ * T ^ (-q)`, then invert via `S`.
      have hcZ_pos : (0 : ℤ) < c := Nat.cast_pos.mpr hc
      have hcZ_gt : (1 : ℤ) < c := by exact_mod_cast hc_gt_one
      let q : ℤ := γ 1 1 / (c : ℤ)
      set γ₁ : SL(2, ℤ) := γ * T ^ (-q) with hγ₁_def
      have hγ_eq : γ = γ₁ * T ^ q := by simp [hγ₁_def, mul_assoc]
      have hγ₁_10 : γ₁ 1 0 = (c : ℤ) := by
        simp [hγ₁_def, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply,
          Fin.sum_univ_two, hγc]
      rw [hγ_eq, etaMultiplier_mul_T_zpow, dedekindRhs_mul_T_zpow γ₁ (hγ₁_10 ▸ hcZ_pos.ne') q]
      congr 1
      have hγ₁_11 : γ₁ 1 1 = γ 1 1 % (c : ℤ) := by
        have hmul : (γ * T ^ (-q)) 1 1 = γ 1 0 * (-q) + γ 1 1 := by
          simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
        rw [hγ₁_def, hmul, hγc, Int.emod_def]
        ring
      have hr_nonneg : 0 ≤ γ₁ 1 1 := hγ₁_11 ▸ Int.emod_nonneg _ hcZ_pos.ne'
      have hr_lt_Z : γ₁ 1 1 < c := hγ₁_11 ▸ Int.emod_lt_of_pos _ hcZ_pos
      have hdet₁ : γ₁ 0 0 * γ₁ 1 1 - γ₁ 0 1 * (c : ℤ) = 1 := by
        have h := γ₁.det_coe
        rwa [Matrix.det_fin_two, hγ₁_10] at h
      have hr_ne_zero : γ₁ 1 1 ≠ 0 := by
        intro hr0
        rw [hr0, mul_zero, zero_sub] at hdet₁
        exact (Int.le_of_dvd one_pos ⟨-γ₁ 0 1, by linarith⟩).not_gt hcZ_gt
      have hr_pos : 0 < γ₁ 1 1 := lt_of_le_of_ne hr_nonneg hr_ne_zero.symm
      obtain ⟨r, hr_eq⟩ := Int.eq_ofNat_of_zero_le hr_nonneg
      have hr_nat_pos : 0 < r := Nat.cast_pos.mp (hr_eq ▸ hr_pos)
      have hr_nat_lt : r < c := Nat.cast_lt.mp (hr_eq ▸ hr_lt_Z)
      have hγ₂_10 : (γ₁ * S) 1 0 = (r : ℤ) := by
        simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two, hr_eq]
      have hih := ih r hr_nat_lt hr_nat_pos (γ₁ * S) hγ₂_10
      rw [etaMultiplier_mul_S γ₁ hr_pos, dedekindRhs_mul_S γ₁ (hγ₁_10 ▸ hcZ_pos) hr_pos] at hih
      exact mul_left_cancel₀ (Complex.exp_ne_zero _) hih

/-- **The Dedekind-sum formula for the eta multiplier** (Apostol, Theorem 3.4):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `0 < c`,
`ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, where `s(d, c)` is the Dedekind sum and
the `-1/4` converts `√(-i (c τ + d))` to the principal square root `√(c τ + d)`. -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  obtain ⟨c, hc_eq⟩ := Int.eq_ofNat_of_zero_le hc.le
  exact etaMultiplier_eq_dedekindRhs_of_natCast c (Nat.cast_pos.mp (hc_eq ▸ hc)) γ hc_eq

/-- The Dedekind-sum formula for `ε(γ)` when `0 < c`, with `s(d, c)` expanded as a sum of
`Int.fract` terms over `ℝ`. -/
theorem etaMultiplier_eq_cexp_sum_fract_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * (γ 1 0 : ℂ)) -
        ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
          (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) -
        1 / 4)) := by
  rw [etaMultiplier_of_c_pos γ hc]
  congr 4
  · push_cast; rfl
  · rw [← Complex.ofReal_ratCast, (γ.isCoprime_row 1).symm.dedekindSum_eq]
    push_cast; rfl

/-- **The transformation law of `η` for `0 < c`** (Apostol, Theorem 3.4):
`η(γ τ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4)) √(c τ + d) η(τ)` on the upper half-plane. -/
theorem eta_smul_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    η (γ • τ : ℍ) =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) *
        Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [eta_smul γ τ, etaMultiplier_of_c_pos γ hc]

/-- **Dedekind's functional equation for the eta function** (Apostol, Theorem 3.4):
under each `γ = (a b; c d) ∈ SL(2, ℤ)`, `η` transforms by a 24th root of unity times the
principal square root `√(c τ + d)`, given for `0 < c` by
`exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`. -/
theorem exists_pow_twentyFour_eq_one_and_eta_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ ε : ℂ, ε ^ 24 = 1 ∧
      (∀ τ : UpperHalfPlane, _root_.ModularForm.eta ((γ • τ : UpperHalfPlane) : ℂ) =
        ε * Complex.sqrt ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * _root_.ModularForm.eta τ) ∧
      (0 < γ 1 0 → ε = Complex.exp (Real.pi * Complex.I *
        (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * (γ 1 0 : ℂ)) -
          ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
            (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) -
          1 / 4))) :=
  ⟨etaMultiplier γ, etaMultiplier_pow_twentyFour γ, eta_smul γ,
    etaMultiplier_eq_cexp_sum_fract_of_c_pos γ⟩

/-! ### Negation and the cases `c < 0` and `c = 0` -/

/-- When `0 < c`, negating `γ` multiplies the eta multiplier by `i`, compensating for the rotation
`√(-(c τ + d)) = -i √(c τ + d)` of the principal square root on the upper half-plane. -/
theorem etaMultiplier_neg_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  rw [SL_neg_smul, eta_smul]
  have him : 0 < ((γ 1 0 : ℂ) * I + γ 1 1).im := by
    simpa using (Int.cast_pos.mpr hc : (0 : ℝ) < γ 1 0)
  have hdenom : ((-γ) 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (-γ) 1 1 =
      -((γ 1 0 : ℂ) * I + γ 1 1) := by
    simp
    ring
  rw [hdenom, Complex.sqrt_neg_of_im_pos him]
  simp only [UpperHalfPlane.coe_I]
  linear_combination (etaMultiplier γ * Complex.sqrt ((γ 1 0 : ℂ) * I + γ 1 1) * η I) * I_mul_I

/-- When `c < 0`, negating `γ` multiplies the eta multiplier by `-i`. -/
theorem etaMultiplier_neg_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  have hc' : 0 < (-γ) 1 0 := by simp [hc]
  have h := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at h
  rw [h]
  linear_combination (etaMultiplier (-γ)) * I_mul_I

/-- **The Dedekind-sum formula for `c < 0`**: for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c < 0`,
`ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`. -/
theorem etaMultiplier_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) + dedekindSum (γ 1 1) (-γ 1 0) + 1 / 4)) := by
  have hc' : 0 < (-γ) 1 0 := by simp [hc]
  have hneg := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at hneg
  have hImul (z : ℂ) : I * cexp z = cexp (π / 2 * I + z) := by
    rw [Complex.exp_add, ← Complex.log_I, Complex.exp_log I_ne_zero]
  rw [hneg, etaMultiplier_of_c_pos (-γ) hc', hImul]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, dedekindSum_neg,
    Rat.cast_neg]
  congr 1
  have hc0 : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
  field_simp
  ring

/-- When `c = 0` and `0 < d`, `γ = T ^ b` and `ε(γ) = exp(π i b / 12)`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd_le : γ 1 1 ≤ 1 := Int.le_of_dvd one_pos ⟨γ 0 0, by linarith⟩
  have hd1 : γ 1 1 = 1 := by omega
  have ha1 : γ 0 0 = 1 := by rw [hd1, mul_one] at hdet; exact hdet
  have hγ : γ = T ^ (γ 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, ha1, hc, hd1]
  rw [congrArg etaMultiplier hγ, etaMultiplier_T_zpow]

/-- When `c = 0` and `d < 0`, `γ = -T ^ (-b)` and `ε(γ) = -i exp(-π i b / 12)`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd_le : -γ 1 1 ≤ 1 := Int.le_of_dvd one_pos ⟨-γ 0 0, by linarith⟩
  have hd1 : γ 1 1 = -1 := by omega
  have hpos : etaMultiplier (-γ) = cexp (-(π * I * γ 0 1 / 12)) := by
    rw [etaMultiplier_of_c_eq_zero_of_d_pos (-γ) (by simp [hc]) (by simp [hd1])]
    simp [neg_div, mul_neg]
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hsmul := eta_smul (-γ) UpperHalfPlane.I
  rw [SL_neg_smul, hpos] at hsmul
  rw [hsmul]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hc, hd1, neg_zero, neg_neg,
    Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, zero_add, Complex.sqrt_one, mul_one,
    Complex.sqrt_neg_one]
  linear_combination (cexp (-(π * I * (γ 0 1 : ℂ) / 12)) * η (UpperHalfPlane.I : ℂ)) * I_mul_I

/-- When `c = 0`, `ε(γ)` is `exp(π i b / 12)` if `0 < d` and `-i exp(-π i b / 12)` if `d < 0`. -/
theorem etaMultiplier_of_c_eq_zero (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    etaMultiplier γ =
      if 0 < γ 1 1 then cexp (π * I * γ 0 1 / 12)
      else -I * cexp (-(π * I * γ 0 1 / 12)) := by
  split_ifs with hd
  · exact etaMultiplier_of_c_eq_zero_of_d_pos γ hc hd
  · have hne : γ 1 1 ≠ 0 := by
      intro hd0
      have hdet := γ.det_coe
      rw [Matrix.det_fin_two, hc, hd0] at hdet
      norm_num at hdet
    exact etaMultiplier_of_c_eq_zero_of_d_neg γ hc (lt_of_le_of_ne (not_lt.mp hd) hne)

/-- For any lower-triangular transvection `γ = (1 0; c 1) ∈ SL(2, ℤ)`,
`ε(γ) = exp(-π i c / 12)` regardless of the sign of `c`. -/
theorem etaMultiplier_of_b_eq_zero_of_d_eq_one (γ : SL(2, ℤ)) (hb : γ 0 1 = 0) (hd : γ 1 1 = 1) :
    etaMultiplier γ = cexp (-(π * I * γ 1 0 / 12)) := by
  have ha : γ 0 0 = 1 := by
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hb, hd] at hdet
    linarith
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · rw [etaMultiplier_of_c_neg γ hc, ha, hd, dedekindSum_one_left (by omega)]
    congr 1
    have hc0 : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
    push_cast
    field_simp
    ring
  · rw [etaMultiplier_of_c_eq_zero_of_d_pos γ hc (by omega), hb, hc]
    simp
  · rw [etaMultiplier_of_c_pos γ hc, ha, hd, dedekindSum_one_left hc.le]
    congr 1
    have hc0 : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
    push_cast
    field_simp
    ring

end TauCeti.ModularForm
