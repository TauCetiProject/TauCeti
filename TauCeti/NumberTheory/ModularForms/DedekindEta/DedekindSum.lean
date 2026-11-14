/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# Dedekind's functional equation and the explicit eta multiplier

This file evaluates the Dedekind eta multiplier `TauCeti.ModularForm.etaMultiplier` of an arbitrary
matrix `γ = (a b; c d) ∈ SL(2, ℤ)` in terms of Dedekind sums `TauCeti.dedekindSum`:

* When `c > 0`,
  $$\varepsilon(\gamma) =
    \exp\!\left(\pi i \left(\frac{a + d}{12 c} - s(d, c) - \frac{1}{4}\right)\right),$$
  so `η(γ • τ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4)) √(c τ + d) η(τ)` on the upper
  half-plane (`etaMultiplier_of_c_pos`, `eta_smul_of_c_pos`).
* Negating `γ` multiplies `ε(γ)` by `i` when `c > 0` and by `-i` when `c < 0`
  (`etaMultiplier_neg_of_c_pos`, `etaMultiplier_neg_of_c_neg`). For all `c ≠ 0` this yields the
  Rademacher sign-unified formula
  $$\varepsilon(\gamma) =
    \exp\!\left(\pi i \left(\frac{a + d}{12 c}
      - \operatorname{sgn}(c)\left(s(d, |c|) + \frac{1}{4}\right)\right)\right)$$
  (`etaMultiplier_of_c_ne_zero`), as well as `ε(γ⁻¹) = ε(γ)⁻¹` (`etaMultiplier_inv_of_c_ne_zero`).
* When `c = 0`, `γ = ±T^{±b}` and `ε(γ)` is `e^{π i b / 12}` if `d > 0` and
  `-i e^{-π i b / 12}` if `d < 0` (`etaMultiplier_of_c_eq_zero_of_d_pos`,
  `etaMultiplier_of_c_eq_zero_of_d_neg`).

The proof of `etaMultiplier_of_c_pos` inducts on `c` along the Euclidean algorithm using the
generator laws `etaMultiplier_mul_T_zpow`, `etaMultiplier_mul_S`, and `etaMultiplier_of_c_eq_one`
from `TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation`, matched at the inversion step
by Dedekind's reciprocity law `TauCeti.dedekindSum_add_dedekindSum`.

## Main results

* `TauCeti.ModularForm.etaMultiplier_ne_zero`, `TauCeti.ModularForm.norm_etaMultiplier`:
  `ε(γ) ≠ 0` and `‖ε(γ)‖ = 1`.
* `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`: behavior of `ε(-γ)` for `c > 0` and `c < 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_pos_eq_exp_sum_fract`,
  `TauCeti.ModularForm.eta_smul_of_c_pos`: **Dedekind's functional equation** for `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_neg`,
  `TauCeti.ModularForm.etaMultiplier_of_c_ne_zero`: explicit formulas for `c < 0` and all `c ≠ 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_neg`: explicit formulas when `c = 0`.
* `TauCeti.ModularForm.etaMultiplier_inv_of_c_ne_zero`: `ε(γ⁻¹) = ε(γ)⁻¹` when `c ≠ 0`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., Theorem 3.4.
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, 1972, Ch. 4.
-/

public section

open Complex ModularGroup
open scoped UpperHalfPlane
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Norm and nonvanishing of the eta multiplier -/

/-- The eta multiplier never vanishes. -/
@[simp]
theorem etaMultiplier_ne_zero (γ : SL(2, ℤ)) : etaMultiplier γ ≠ 0 := by
  intro h
  have h24 := etaMultiplier_pow_twentyFour γ
  simp [h] at h24

/-- The eta multiplier has unit norm, since its 24th power is `1`. -/
@[simp]
theorem norm_etaMultiplier (γ : SL(2, ℤ)) : ‖etaMultiplier γ‖ = 1 := by
  have h := congrArg norm (etaMultiplier_pow_twentyFour γ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide)).mp h

/-! ### Action of `-1 ∈ SL(2, ℤ)` on the eta multiplier -/

/-- When `c > 0`, negating `γ ∈ SL(2, ℤ)` multiplies the eta multiplier by `i`:
`ε(-γ) = i ε(γ)`. -/
theorem etaMultiplier_neg_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  -- Shift on the right by `T ^ (-n)` so the lower-right entry becomes negative; then both `-γ'`
  -- and `(-γ') * S` have positive lower-right entry, so `etaMultiplier_mul_S` applies twice.
  let n : ℤ := |γ 1 1| + 1
  let γ' : SL(2, ℤ) := γ * T ^ (-n)
  have hn_pos : 0 < n := by have := abs_nonneg (γ 1 1); omega
  have hγ'10 : γ' 1 0 = γ 1 0 := by
    simp [γ', Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  have hγ'11 : γ' 1 1 = γ 1 0 * (-n) + γ 1 1 := by
    simp [γ', Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  have hγ'11_neg : γ' 1 1 < 0 := by
    have hle : γ 1 1 ≤ |γ 1 1| := le_abs_self _
    have hmul : n ≤ γ 1 0 * n := le_mul_of_one_le_left hn_pos.le hc
    linarith [hγ'11, mul_neg (γ 1 0) n]
  have hd1 : 0 < (-γ') 1 1 := by
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff]
    exact hγ'11_neg
  have hd2 : 0 < ((-γ') * S) 1 1 := by
    have hS11 : ((-γ') * S) 1 1 = -((-γ') 1 0) := by
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hS11, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, neg_neg, hγ'10]
    exact hc
  have hS1 := etaMultiplier_mul_S (-γ') hd1
  have hS2 := etaMultiplier_mul_S ((-γ') * S) hd2
  have hSS : ((-γ') * S) * S = γ' := by
    rw [mul_assoc, ← sq, TauCeti.ModularGroup.S_sq, mul_neg_one, neg_neg]
  rw [hSS, hS1, ← mul_assoc, ← Complex.exp_add] at hS2
  have hexp : cexp (-(π * I / 4) + -(π * I / 4)) = -I := by
    have harg : -(π * I / 4) + -(π * I / 4) = -(π / 2 * I) := by ring
    rw [harg, Complex.exp_neg, exp_pi_div_two_mul_I, inv_I]
  rw [hexp] at hS2
  have hγ' : etaMultiplier (-γ') = I * etaMultiplier γ' := by rw [hS2, ← mul_assoc]; simp
  have hrestore : γ' * T ^ n = γ := by simp [γ', mul_assoc]
  have hrestore_neg : (-γ') * T ^ n = -γ := by rw [neg_mul, hrestore]
  rw [← hrestore_neg, etaMultiplier_mul_T_zpow, hγ', ← mul_left_comm, ← etaMultiplier_mul_T_zpow,
    hrestore]

/-- When `c < 0`, negating `γ ∈ SL(2, ℤ)` multiplies the eta multiplier by `-i`:
`ε(-γ) = -i ε(γ)`. -/
theorem etaMultiplier_neg_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  have hc' : 0 < (-γ) 1 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff]
    exact hc
  have h := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at h
  rw [h, ← mul_assoc]
  simp

/-! ### Dedekind's functional equation (`c > 0`) -/

private theorem euclidean_step_exp {a b₁ c d q r : ℤ} (hc : 0 < c) (hr : 0 < r)
    (hdiv : c * q + r = d) (hdet : a * r - b₁ * c = 1) :
    (q : ℚ) / 12 + 1 / 4 +
        (((b₁ : ℚ) + (-c : ℤ)) / (12 * r) - dedekindSum (-c) r - 1 / 4) =
      ((a : ℚ) + d) / (12 * c) - dedekindSum d c - 1 / 4 := by
  have hcop : IsCoprime r c := ⟨a, -b₁, by linarith⟩
  have hrec := dedekindSum_add_dedekindSum hr hc hcop
  have hmod : dedekindSum d c = dedekindSum r c := by
    rw [← hdiv, add_comm, mul_comm, dedekindSum_add_mul_self]
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  have hrQ : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr.ne'
  have hdetQ : (a : ℚ) * r - (b₁ : ℚ) * c = 1 := by exact_mod_cast hdet
  have hdivQ : (c : ℚ) * q + r = d := by exact_mod_cast hdiv
  have hsr : dedekindSum c r =
      ((r : ℚ) ^ 2 + (c : ℚ) ^ 2 + 1) / (12 * r * c) - 1 / 4 - dedekindSum r c := by
    linarith
  rw [dedekindSum_neg, hmod, hsr]
  push_cast
  field_simp
  linear_combination 4 * (r : ℚ) * hdivQ - 4 * hdetQ

/-- **Dedekind's functional equation for the eta multiplier** (Apostol, Theorem 3.4):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`,
$$\varepsilon(\gamma) =
  \exp\!\left(\pi i \left(\frac{a + d}{12 c} - s(d, c) - \frac{1}{4}\right)\right).$$ -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  suffices hmain : ∀ n : ℕ, 0 < n → ∀ γ : SL(2, ℤ), γ 1 0 = n →
      etaMultiplier γ =
        cexp (π * I *
          (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) by
    exact hmain (γ 1 0).toNat (by omega) γ (Int.toNat_of_nonneg hc.le).symm
  intro n
  refine Nat.strongRecOn n fun n ih hn γ hc ↦ ?_
  by_cases hn1 : n = 1
  · subst hn1
    rw [etaMultiplier_of_c_eq_one γ (by simpa using hc)]
    simp [hc]
  · let c : ℤ := γ 1 0
    let d : ℤ := γ 1 1
    let a : ℤ := γ 0 0
    let q : ℤ := d / c
    let r : ℤ := d % c
    have hc_pos : 0 < c := by omega
    have hdiv : c * q + r = d := Int.mul_ediv_add_emod d c
    have hr_nonneg : 0 ≤ r := Int.emod_nonneg d hc_pos.ne'
    have hr_lt : r < c := Int.emod_lt_of_pos d hc_pos
    have hr_pos : 0 < r := by
      refine lt_of_le_of_ne hr_nonneg fun hr0 ↦ ?_
      have hcr : c ∣ 1 := (γ.isCoprime_row 1).isUnit_of_dvd' dvd_rfl ⟨q, by linarith⟩ |>.dvd
      exact absurd (Int.le_of_dvd zero_lt_one hcr) (by omega)
    let γ₁ : SL(2, ℤ) := γ * T ^ (-q)
    let γ₂ : SL(2, ℤ) := γ₁ * S
    have hγ₁_00 : γ₁ 0 0 = a := by
      simp [γ₁, a, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply,
        Fin.sum_univ_two]
    have hγ₁_10 : γ₁ 1 0 = c := by
      simp [γ₁, c, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply,
        Fin.sum_univ_two]
    have hγ₁_11 : γ₁ 1 1 = r := by
      have h11 : γ₁ 1 1 = c * (-q) + d := by
        simp [γ₁, c, d, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply,
          Fin.sum_univ_two]
      linarith [h11, mul_neg c q, hdiv]
    have hγ₂_00 : γ₂ 0 0 = γ₁ 0 1 := by
      simp [γ₂, Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
    have hγ₂_10 : γ₂ 1 0 = r := by
      simp [γ₂, hγ₁_11, Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply,
        Fin.sum_univ_two]
    have hγ₂_11 : γ₂ 1 1 = -c := by
      simp [γ₂, hγ₁_10, Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply,
        Fin.sum_univ_two]
    have hdet₁ : a * r - γ₁ 0 1 * c = 1 := by
      simpa only [hγ₁_00, hγ₁_10, hγ₁_11] using γ₁.fin_two_mul_sub_mul_eq_one
    have hrestore : γ₁ * T ^ q = γ := by simp [γ₁, mul_assoc]
    have hT := etaMultiplier_mul_T_zpow γ₁ q
    rw [hrestore] at hT
    have hγ₁_eq : etaMultiplier γ₁ = cexp (π * I / 4) * etaMultiplier γ₂ := by
      rw [etaMultiplier_mul_S γ₁ (hγ₁_11 ▸ hr_pos), ← mul_assoc, ← Complex.exp_add]
      simp
    have hIH := ih r.toNat (by omega) (by omega) γ₂
      (hγ₂_10.trans (Int.toNat_of_nonneg hr_nonneg).symm)
    rw [hT, hγ₁_eq, hIH, hγ₂_00, hγ₂_10, hγ₂_11, ← Complex.exp_add, ← Complex.exp_add]
    have hexpC :=
      congrArg (fun x : ℚ ↦ π * I * (x : ℂ)) (euclidean_step_exp hc_pos hr_pos hdiv hdet₁)
    push_cast at hexpC
    congr 1
    push_cast
    linear_combination hexpC

/-- Explicit fractional-part form of `etaMultiplier_of_c_pos`: for `γ = (a b; c d) ∈ SL(2, ℤ)`
with `c > 0`, `s(d, c)` expands to the unguarded fractional-part sum over `Finset.Ioo 0 c`. -/
theorem etaMultiplier_of_c_pos_eq_exp_sum_fract (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
          (∑ r ∈ Finset.Ioo 0 (γ 1 0),
            ((r : ℂ) / γ 1 0) * (((Int.fract ((γ 1 1 * r : ℝ) / γ 1 0) : ℝ) : ℂ) - 1 / 2)) -
          1 / 4)) := by
  have hsum : ((dedekindSum (γ 1 1) (γ 1 0) : ℚ) : ℂ) =
      ∑ r ∈ Finset.Ioo 0 (γ 1 0),
        ((r : ℂ) / γ 1 0) * (((Int.fract ((γ 1 1 * r : ℝ) / γ 1 0) : ℝ) : ℂ) - 1 / 2) := by
    rw [(γ.isCoprime_row 1).symm.dedekindSum_eq]
    push_cast
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hfract : ((Int.fract ((γ 1 1 * r : ℚ) / γ 1 0) : ℚ) : ℝ) =
        Int.fract ((γ 1 1 * r : ℝ) / γ 1 0) := by
      simp
    rw [← Complex.ofReal_ratCast (Int.fract _), hfract]
  rw [etaMultiplier_of_c_pos γ hc, hsum]

/-- **Dedekind's functional equation for `η`** (Apostol, Theorem 3.4):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` and `τ ∈ ℍ`,
$$\eta(\gamma \cdot \tau) =
  \exp\!\left(\pi i \left(\frac{a + d}{12 c} - s(d, c) - \frac{1}{4}\right)\right)
  \sqrt{c \tau + d}\,\eta(\tau).$$ -/
theorem eta_smul_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    η (γ • τ : ℍ) =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) *
      Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [eta_smul, etaMultiplier_of_c_pos γ hc]

/-! ### Formulas for `c < 0`, `c ≠ 0`, `c = 0`, and `γ⁻¹` -/

/-- Explicit eta multiplier when `c < 0`:
`ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`. -/
theorem etaMultiplier_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) + dedekindSum (γ 1 1) (-γ 1 0) + 1 / 4)) := by
  have hc' : 0 < (-γ) 1 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff]
    exact hc
  have hneg := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg, ← exp_pi_div_two_mul_I] at hneg
  rw [hneg, etaMultiplier_of_c_pos (-γ) hc', ← Complex.exp_add]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, dedekindSum_neg]
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
  congr 1
  push_cast
  field_simp
  ring

/-- **Rademacher's sign-unified formula** for the eta multiplier when `c ≠ 0`:
$$\varepsilon(\gamma) =
  \exp\!\left(\pi i \left(\frac{a + d}{12 c}
    - \operatorname{sgn}(c)\left(s(d, |c|) + \frac{1}{4}\right)\right)\right).$$ -/
theorem etaMultiplier_of_c_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
          (γ 1 0).sign * (dedekindSum (γ 1 1) (γ 1 0).natAbs + 1 / 4))) := by
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · rw [etaMultiplier_of_c_neg γ hlt, Int.sign_eq_neg_one_of_neg hlt,
      Int.natCast_natAbs, abs_of_neg hlt]
    congr 1
    push_cast
    ring
  · rw [etaMultiplier_of_c_pos γ hgt, Int.sign_eq_one_of_pos hgt,
      Int.natCast_natAbs, abs_of_pos hgt]
    congr 1
    push_cast
    ring

/-- Explicit eta multiplier when `c = 0` and `d > 0`: then `γ = T ^ b` and
`ε(γ) = e^{π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hdet
  have hd1 : γ 1 1 = 1 :=
    le_antisymm (Int.le_of_dvd zero_lt_one ⟨γ 0 0, by linarith⟩) hd
  have ha1 : γ 0 0 = 1 := by simpa [hd1] using hdet
  have hγ : γ = T ^ (γ 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, hc, hd1, ha1]
  rw [congrArg etaMultiplier hγ, etaMultiplier_T_zpow]

/-- Explicit eta multiplier when `c = 0` and `d < 0`: then `γ = T ^ (-b) * (-1)` and
`ε(γ) = -i e^{-π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hdet
  have hd1 : γ 1 1 = -1 := by
    have hle : -γ 1 1 ≤ 1 := Int.le_of_dvd zero_lt_one ⟨-γ 0 0, by linarith⟩
    omega
  have ha1 : γ 0 0 = -1 := by rw [hd1] at hdet; omega
  have hγ : γ = T ^ (-γ 0 1) * (-1 : SL(2, ℤ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, hc, hd1, ha1]
  have harg : π * I * -(γ 0 1 : ℂ) / 12 = -(π * I * γ 0 1 / 12) := by ring
  rw [congrArg etaMultiplier hγ, etaMultiplier_T_zpow_mul, etaMultiplier_neg_one, Int.cast_neg,
    harg, mul_comm]

/-- When `c ≠ 0`, the eta multiplier of `γ⁻¹` is the inverse of the eta multiplier of `γ`:
`ε(γ⁻¹) = ε(γ)⁻¹`. (Note that `c ≠ 0` is sharp: at `γ = -1` one has `ε(-1) = -i ≠ i = ε(-1)⁻¹`.) -/
theorem etaMultiplier_inv_of_c_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ⁻¹ = (etaMultiplier γ)⁻¹ := by
  have hc_inv : (γ⁻¹ : SL(2, ℤ)) 1 0 ≠ 0 := by simp [hc]
  have hmod : γ 0 0 * γ 1 1 ≡ 1 [ZMOD (γ 1 0).natAbs] := by
    have hdet := γ.fin_two_mul_sub_mul_eq_one
    rw [Int.modEq_iff_dvd]
    have hdvd : γ 1 0 ∣ 1 - γ 0 0 * γ 1 1 := ⟨-γ 0 1, by linarith⟩
    exact Int.natCast_natAbs (γ 1 0) ▸ (abs_dvd _ _).mpr hdvd
  have hded : dedekindSum (γ 0 0) (γ 1 0).natAbs = dedekindSum (γ 1 1) (γ 1 0).natAbs :=
    dedekindSum_eq_of_mul_modEq_one hmod
  rw [etaMultiplier_of_c_ne_zero γ⁻¹ hc_inv, etaMultiplier_of_c_ne_zero γ hc]
  simp only [Matrix.SpecialLinearGroup.inv_apply_zero_zero,
    Matrix.SpecialLinearGroup.inv_apply_one_zero, Matrix.SpecialLinearGroup.inv_apply_one_one,
    Int.sign_neg, Int.natAbs_neg, hded, ← Complex.exp_neg]
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  congr 1
  push_cast
  field_simp
  ring

end TauCeti.ModularForm
