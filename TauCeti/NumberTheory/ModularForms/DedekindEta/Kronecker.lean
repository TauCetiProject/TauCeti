/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Multiplier
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# The Kronecker-symbol formula for the eta multiplier

For `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` and `e(x) = exp(2π i x)`, the Dedekind eta multiplier
`TauCeti.ModularForm.etaMultiplier` has the closed form (Strömberg, Remark 2.5, equation (2.5))
* `ε(γ) = (d / c) e(((a + d) c - b d (c² - 1) - 3 c) / 24)` when `c` is odd, and
* `ε(γ) = (c / d) e(((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)` when `c` is even,

where `(· / ·)` is the Kronecker symbol `TauCeti.kroneckerSym`. Unlike the Dedekind-sum formula in
`TauCeti.NumberTheory.ModularForms.DedekindEta.Multiplier`, this expression exhibits the quadratic
character in `d` and `c` directly, which is the input to the modularity criterion for eta quotients
on `Γ₀(N)`.

The proof applies the Euclidean uniqueness theorem `eq_etaMultiplier_of_c_pos`:
* at `c = 1`, `(d / 1) = 1` and the numerator simplifies to `a + d - 3`;
* under `γ ↦ γ T`, `c` keeps its parity: for odd `c` the symbol `(c + d / c) = (d / c)` is
  unchanged and the numerator shifts by `1` modulo `24`, while for even `c` both `4 ∣ c` and
  `c ≡ 2 (mod 4)` (`kroneckerSym_add_self_right_of_modEq_two`) match the shift of the numerator
  modulo `24`;
* under `γ ↦ γ S` (`c > 0` and `d > 0`), `a d - b c = 1` eliminates `a` and `b` from the numerator
  difference, and quadratic reciprocity together with its first supplement matches the sign change
  between the two Kronecker symbols across all three parity combinations of `(c, d)`.

Combining the Kronecker formula with `etaMultiplier_of_c_pos` also gives the closed evaluation of
`exp(-π i s(d, c))` in terms of the Kronecker symbol.

## Main results

* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym`: unified Kronecker-symbol formula for `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_odd`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_even`: the odd-`c` and even-`c` formulas.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_of_isCoprime_six`: simplified formula
  `ε(γ) = (d / c) e^{π i (a + d - 3) c / 12}` when `c > 0` is prime to `6`.
* `TauCeti.ModularForm.cexp_neg_pi_mul_I_mul_dedekindSum_of_odd`,
  `TauCeti.ModularForm.cexp_neg_pi_mul_I_mul_dedekindSum_of_even`: `exp(-π i s(d, c))` in terms of
  `kroneckerSym` for `γ ∈ SL(2, ℤ)` with `c > 0`.

## References

* F. Strömberg, *Maass waveforms on `(Γ₀(N), χ)` (computational aspects)*, in *Hyperbolic Geometry
  and Applications in Quantum Chaos and Cosmology*, LMS Lecture Note Series 397 (2012), Remark 2.5,
  equation (2.5).
* H. Rademacher, *Zur Theorie der Modulfunktionen*, J. Reine Angew. Math. 167 (1932), 312–336.
-/

public section

open Complex ModularGroup ZMod
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Arithmetic and exponential helpers modulo `24` -/

private theorem cexp_two_pi_I_intCast_div_twentyFour_congr {m n : ℤ} (h : 24 ∣ m - n) :
    cexp (2 * π * I * (m : ℂ) / 24) = cexp (2 * π * I * (n : ℂ) / 24) := by
  obtain ⟨k, hk⟩ := h
  have hm : (m : ℂ) = n + 24 * k := by
    have : m = n + 24 * k := by omega
    exact_mod_cast this
  have hexp : 2 * π * I * ((n : ℂ) + 24 * k) / 24 =
      2 * π * I * n / 24 + (k : ℤ) * (2 * π * I) := by ring
  rw [hm, hexp, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

private theorem cexp_two_pi_I_intCast_div_twentyFour_neg_of_dvd {m n : ℤ} (h : 24 ∣ m - n + 12) :
    cexp (2 * π * I * (m : ℂ) / 24) = -cexp (2 * π * I * (n : ℂ) / 24) := by
  have h12 : 24 ∣ m - (n - 12) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by omega⟩
  rw [cexp_two_pi_I_intCast_div_twentyFour_congr h12]
  have hexp : 2 * π * I * ((n - 12 : ℤ) : ℂ) / 24 = 2 * π * I * n / 24 - π * I := by
    push_cast
    ring
  rw [hexp, sub_eq_add_neg, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

private theorem eight_dvd_sq_sub_one_of_odd {c : ℤ} (hc : Odd c) : 8 ∣ c ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  exact ⟨m, by linear_combination 4 * hm⟩

private theorem three_dvd_mul_sq_sub_one (c : ℤ) : 3 ∣ c * (c ^ 2 - 1) := by
  obtain ⟨q, r, hr0, hr3, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 3 ∧ c = 3 * q + r :=
    ⟨c / 3, c % 3, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num), by omega⟩
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
  · exact ⟨9 * q ^ 3 - q, by ring⟩
  · exact ⟨9 * q ^ 3 + 9 * q ^ 2 + 2 * q, by ring⟩
  · exact ⟨9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2, by ring⟩

private theorem twentyFour_dvd_mul_sq_sub_one_of_odd {c : ℤ} (hc : Odd c) :
    24 ∣ c * (c ^ 2 - 1) :=
  IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3)
    (dvd_mul_of_dvd_right (eight_dvd_sq_sub_one_of_odd hc) c)
    (three_dvd_mul_sq_sub_one c)

private theorem odd_zero_zero_and_one_one_of_even {γ : SL(2, ℤ)} (heven : Even (γ 1 0)) :
    Odd (γ 0 0) ∧ Odd (γ 1 1) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨m, hm⟩ := heven
  refine ⟨by_contra fun ha ↦ ?_, by_contra fun hd ↦ ?_⟩
  · obtain ⟨k, hk⟩ := Int.not_odd_iff_even.mp ha
    have : (2 : ℤ) ∣ 1 :=
      ⟨k * γ 1 1 - γ 0 1 * m, by linear_combination -hdet + hk * γ 1 1 - γ 0 1 * hm⟩
    omega
  · obtain ⟨k, hk⟩ := Int.not_odd_iff_even.mp hd
    have : (2 : ℤ) ∣ 1 :=
      ⟨γ 0 0 * k - γ 0 1 * m, by linear_combination -hdet + γ 0 0 * hk - γ 0 1 * hm⟩
    omega

/-! ### Candidate Kronecker expression and Euclidean steps -/

private theorem cexp_two_pi_I_add_one_div_twentyFour (n : ℤ) :
    cexp (2 * π * I * ((n + 1 : ℤ) : ℂ) / 24) =
      cexp (π * I / 12) * cexp (2 * π * I * (n : ℂ) / 24) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private noncomputable def kroneckerEtaMultiplier (γ : SL(2, ℤ)) : ℂ :=
  if Odd (γ 1 0) then
    kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) / 24)
  else
    kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24)

private theorem kroneckerEtaMultiplier_of_c_eq_one {γ : SL(2, ℤ)} (hc : γ 1 0 = 1) :
    kroneckerEtaMultiplier γ = etaMultiplier γ := by
  rw [kroneckerEtaMultiplier, hc, ite_eq_left odd_one, kroneckerSym_one_right, Int.cast_one,
    one_mul, etaMultiplier_of_c_eq_one γ hc]
  congr 1
  push_cast
  ring

private theorem kroneckerEtaMultiplier_mul_T_of_odd {γ : SL(2, ℤ)} (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    kroneckerEtaMultiplier (γ * T) = cexp (π * I / 12) * kroneckerEtaMultiplier γ := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hsym : kroneckerSym (γ 1 0 + γ 1 1) (γ 1 0) = kroneckerSym (γ 1 1) (γ 1 0) := by
    have hc_nat : (γ 1 0 : ℤ) = (γ 1 0).natAbs := (Int.natAbs_of_nonneg hc.le).symm
    have hodd_nat : Odd (γ 1 0).natAbs := Int.natAbs_odd.mpr hodd
    rw [hc_nat, kroneckerSym_eq_jacobiSym _ hodd_nat, kroneckerSym_eq_jacobiSym _ hodd_nat]
    exact jacobiSym.mod_left' (Int.add_emod_left _ _)
  have hdvd : 24 ∣
      ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 - (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) -
        3 * γ 1 0) -
      (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) + 1) := by
    obtain ⟨m, hm⟩ := twentyFour_dvd_mul_sq_sub_one_of_odd hodd
    refine ⟨-(γ 0 0 + 2 * γ 0 1) * m, ?_⟩
    linear_combination -(γ 1 0 ^ 2 - 1) * hdet - (γ 0 0 + 2 * γ 0 1) * hm
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [TauCeti.ModularGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_left hodd, ite_eq_left hodd, hsym,
    cexp_two_pi_I_intCast_div_twentyFour_congr hdvd, cexp_two_pi_I_add_one_div_twentyFour]
  ring

private theorem even_T_num_diff (γ : SL(2, ℤ)) :
    ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 - (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) +
      3 * (γ 1 0 + γ 1 1) - 3 - 3 * γ 1 0 * (γ 1 0 + γ 1 1)) -
    (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
      3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) + 1) =
    -(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) + 3 * γ 1 0 * (1 - γ 1 0) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  linear_combination -(γ 1 0 ^ 2 - 1) * hdet

private theorem three_dvd_even_T_num_diff (a b c : ℤ) :
    3 ∣ -(a + 2 * b) * c * (c ^ 2 - 1) + 3 * c * (1 - c) := by
  obtain ⟨u, hu⟩ := three_dvd_mul_sq_sub_one c
  exact ⟨-(a + 2 * b) * u + c * (1 - c), by linear_combination -(a + 2 * b) * hu⟩

private theorem kroneckerEtaMultiplier_mul_T_of_four_dvd {γ : SL(2, ℤ)} (k : ℤ)
    (hc : γ 1 0 = 4 * k) :
    kroneckerEtaMultiplier (γ * T) = cexp (π * I / 12) * kroneckerEtaMultiplier γ := by
  have heven : Even (γ 1 0) := ⟨2 * k, by omega⟩
  have hnot_odd : ¬ Odd (γ 1 0) := Int.not_odd_iff_even.mpr heven
  have hodd_a : Odd (γ 0 0) := (odd_zero_zero_and_one_one_of_even heven).1
  have hc4 : γ 1 0 ≡ 0 [ZMOD 4] := by rw [Int.ModEq, hc]; omega
  have hsym : kroneckerSym (γ 1 0) (γ 1 0 + γ 1 1) = kroneckerSym (γ 1 0) (γ 1 1) :=
    kroneckerSym_mod_right' (.inl hc4) (Int.add_emod_left _ _)
  have h8 : 8 ∣ -(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) + 3 * γ 1 0 * (1 - γ 1 0) := by
    obtain ⟨t, ht⟩ := hodd_a
    refine ⟨k * (t + γ 0 1 + 2 - 8 * (2 * t + 1 + 2 * γ 0 1) * k ^ 2 - 6 * k), ?_⟩
    rw [ht, hc]
    ring
  have h24 : 24 ∣
      ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 - (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) +
        3 * (γ 1 0 + γ 1 1) - 3 - 3 * γ 1 0 * (γ 1 0 + γ 1 1)) -
      (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) + 1) := by
    rw [even_T_num_diff]
    exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3) h8
      (three_dvd_even_T_num_diff (γ 0 0) (γ 0 1) (γ 1 0))
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [TauCeti.ModularGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_right hnot_odd, ite_eq_right hnot_odd,
    hsym, cexp_two_pi_I_intCast_div_twentyFour_congr h24, cexp_two_pi_I_add_one_div_twentyFour]
  ring

private theorem kroneckerEtaMultiplier_mul_T_of_modEq_two {γ : SL(2, ℤ)} (s : ℤ)
    (hc : γ 1 0 = 2 * (2 * s + 1)) :
    kroneckerEtaMultiplier (γ * T) = cexp (π * I / 12) * kroneckerEtaMultiplier γ := by
  set a := γ 0 0; set b := γ 0 1; set c := γ 1 0; set d := γ 1 1
  have heven : Even c := ⟨2 * s + 1, by omega⟩
  have hnot_odd : ¬ Odd c := Int.not_odd_iff_even.mpr heven
  have hdet := γ.det_coe; rw [Matrix.det_fin_two] at hdet
  have hodd_d : Odd d := (odd_zero_zero_and_one_one_of_even heven).2
  have hc2 : c ≡ 2 [ZMOD 4] := by rw [Int.ModEq, hc]; omega
  have hsym := kroneckerSym_add_self_right_of_modEq_two hc2 hodd_d
  have h3 := three_dvd_even_T_num_diff a b c
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [TauCeti.ModularGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_right hnot_odd, ite_eq_right hnot_odd]
  -- Reducing `a d - b c = 1` modulo `4` gives `a + 2 b ≡ d (mod 4)`.
  rcases (by obtain ⟨t, ht⟩ := hodd_d; omega : d % 4 = 1 ∨ d % 4 = 3) with hd4 | hd4
  · have hχ : (χ₄ (d : ZMod 4) : ℤ) = 1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
    have hd_eq : d = 4 * (d / 4) + 1 := by omega
    obtain ⟨u, hu⟩ : 4 ∣ a + 2 * b - 1 := ⟨-a * (d / 4) + b * (s + 1), by
      have hdet' : a * d - b * c = 1 := hdet
      rw [hd_eq, hc] at hdet'
      linear_combination hdet'⟩
    have h8 : 8 ∣ -(a + 2 * b) * c * (c ^ 2 - 1) + 3 * c * (1 - c) + 12 := by
      have hab : a + 2 * b = 4 * u + 1 := by omega
      refine ⟨-(2 * s + 1) * u * (16 * s ^ 2 + 16 * s + 3) - 8 * s ^ 3 - 18 * s ^ 2 - 10 * s, ?_⟩
      rw [hc, hab]; ring
    have h24 : 24 ∣ ((a + (c + d)) * c - (a + b) * (c + d) * (c ^ 2 - 1) +
        3 * (c + d) - 3 - 3 * c * (c + d)) -
        (((a + d) * c - b * d * (c ^ 2 - 1) + 3 * d - 3 - 3 * c * d) + 1) + 12 := by
      rw [even_T_num_diff γ]
      exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3) h8 (dvd_add h3 ⟨4, by norm_num⟩)
    rw [hsym, hχ, cexp_two_pi_I_intCast_div_twentyFour_neg_of_dvd h24,
      cexp_two_pi_I_add_one_div_twentyFour]
    push_cast; ring
  · have hχ : (χ₄ (d : ZMod 4) : ℤ) = -1 := by rw [χ₄_int_eq_if_mod_four]; split_ifs <;> omega
    have hd_eq : d = 4 * (d / 4) + 3 := by omega
    obtain ⟨u, hu⟩ : 4 ∣ a + 2 * b - 3 :=
      ⟨-3 * a * (d / 4) - 2 * a + 3 * b * s + 2 * b, by
        have hdet' : a * d - b * c = 1 := hdet
        rw [hd_eq, hc] at hdet'
        linear_combination 3 * hdet'⟩
    have h8 : 8 ∣ -(a + 2 * b) * c * (c ^ 2 - 1) + 3 * c * (1 - c) := by
      have hab : a + 2 * b = 4 * u + 3 := by omega
      refine ⟨-(2 * s + 1) * (u * (16 * s ^ 2 + 16 * s + 3) + 12 * s ^ 2 + 15 * s + 3), ?_⟩
      rw [hc, hab]; ring
    have h24 : 24 ∣ ((a + (c + d)) * c - (a + b) * (c + d) * (c ^ 2 - 1) +
        3 * (c + d) - 3 - 3 * c * (c + d)) -
        (((a + d) * c - b * d * (c ^ 2 - 1) + 3 * d - 3 - 3 * c * d) + 1) := by
      rw [even_T_num_diff γ]
      exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3) h8 h3
    rw [hsym, hχ, cexp_two_pi_I_intCast_div_twentyFour_congr h24,
      cexp_two_pi_I_add_one_div_twentyFour]
    push_cast; ring

private theorem kroneckerEtaMultiplier_mul_T_of_even {γ : SL(2, ℤ)}
    (heven : Even (γ 1 0)) :
    kroneckerEtaMultiplier (γ * T) = cexp (π * I / 12) * kroneckerEtaMultiplier γ := by
  obtain ⟨m, hm⟩ := heven
  rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨s, rfl⟩
  · exact kroneckerEtaMultiplier_mul_T_of_four_dvd k (by omega)
  · exact kroneckerEtaMultiplier_mul_T_of_modEq_two s (by omega)

private theorem kroneckerEtaMultiplier_mul_S_of_odd_of_odd {γ : SL(2, ℤ)} (hc : 0 < γ 1 0)
    (hd : 0 < γ 1 1) (hodd_c : Odd (γ 1 0)) (hodd_d : Odd (γ 1 1)) :
    kroneckerEtaMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerEtaMultiplier γ := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  set c₀ : ℕ := (γ 1 0).natAbs
  set d₀ : ℕ := (γ 1 1).natAbs
  have hc₀ : (c₀ : ℤ) = γ 1 0 := Int.natAbs_of_nonneg hc.le
  have hd₀ : (d₀ : ℤ) = γ 1 1 := Int.natAbs_of_nonneg hd.le
  have hodd_c₀ : Odd c₀ := Int.natAbs_odd.mpr hodd_c
  have hodd_d₀ : Odd d₀ := Int.natAbs_odd.mpr hodd_d
  have hsym : (kroneckerSym (-γ 1 0) (γ 1 1) : ℂ) =
      (-1 : ℂ) ^ ((c₀ / 2 + 1) * (d₀ / 2)) * kroneckerSym (γ 1 1) (γ 1 0) := by
    rw [← hc₀, ← hd₀, kroneckerSym_eq_jacobiSym _ hodd_d₀, kroneckerSym_eq_jacobiSym _ hodd_c₀,
      jacobiSym.neg _ hodd_d₀, χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd_d₀),
      jacobiSym.quadratic_reciprocity hodd_c₀ hodd_d₀]
    push_cast
    rw [← mul_assoc, ← pow_add, show d₀ / 2 + c₀ / 2 * (d₀ / 2) = (c₀ / 2 + 1) * (d₀ / 2) by ring]
  have hnum : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) - 3 * γ 1 1 : ℤ) =
      (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) - 3) -
        12 * (((c₀ / 2 + 1) * (d₀ / 2) : ℕ) : ℤ) := by
    have hc_div : (γ 1 0 : ℤ) = 2 * (c₀ / 2 : ℕ) + 1 := by
      have := Nat.div_add_mod c₀ 2; have := Nat.odd_iff.mp hodd_c₀; omega
    have hd_div : (γ 1 1 : ℤ) = 2 * (d₀ / 2 : ℕ) + 1 := by
      have := Nat.div_add_mod d₀ 2; have := Nat.odd_iff.mp hodd_d₀; omega
    have hbase : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) - 3 * γ 1 1) -
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) - 3) =
        -3 * (γ 1 0 + 1) * (γ 1 1 - 1) := by
      linear_combination -γ 1 0 * γ 1 1 * hdet
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    linear_combination hbase + (by rw [hc_div, hd_div]; ring :
      -3 * (γ 1 0 + 1) * (γ 1 1 - 1) + 12 * (((c₀ / 2 : ℕ) : ℤ) + 1) * ((d₀ / 2 : ℕ) : ℤ) = 0)
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [TauCeti.ModularGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_left hodd_d, ite_eq_left hodd_c, hsym, hnum]
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0
  set k : ℕ := (c₀ / 2 + 1) * (d₀ / 2)
  have hexp : 2 * π * I * (((N - 3) - 12 * (k : ℤ) : ℤ) : ℂ) / 24 =
      -(k : ℂ) * (π * I) + (-(π * I / 4) + 2 * π * I * (N : ℂ) / 24) := by
    push_cast
    ring
  have hsign : (-1 : ℂ) ^ k * cexp (-(k : ℂ) * (π * I)) = 1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_pi_mul_I,
      mul_inv_cancel₀ (pow_ne_zero k (by norm_num))]
  rw [hexp, Complex.exp_add, Complex.exp_add]
  linear_combination cexp (-(π * I / 4)) * (kroneckerSym (γ 1 1) (γ 1 0) : ℂ) *
    cexp (2 * π * I * (N : ℂ) / 24) * hsign

private theorem kroneckerEtaMultiplier_mul_S_of_even_of_odd {γ : SL(2, ℤ)} (hd : 0 < γ 1 1)
    (heven_c : Even (γ 1 0)) (hodd_d : Odd (γ 1 1)) :
    kroneckerEtaMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerEtaMultiplier γ := by
  have hnot_odd_c : ¬ Odd (γ 1 0) := Int.not_odd_iff_even.mpr heven_c
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  set d₀ : ℕ := (γ 1 1).natAbs
  have hd₀ : (d₀ : ℤ) = γ 1 1 := Int.natAbs_of_nonneg hd.le
  have hodd_d₀ : Odd d₀ := Int.natAbs_odd.mpr hodd_d
  have hsym : (kroneckerSym (-γ 1 0) (γ 1 1) : ℂ) =
      (-1 : ℂ) ^ (d₀ / 2) * kroneckerSym (γ 1 0) (γ 1 1) := by
    rw [← hd₀, kroneckerSym_eq_jacobiSym _ hodd_d₀, kroneckerSym_eq_jacobiSym _ hodd_d₀,
      jacobiSym.neg _ hodd_d₀, χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd_d₀)]
    push_cast
    rfl
  have hnum : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) - 3 * γ 1 1 : ℤ) =
      (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) - 3) - 12 * ((d₀ / 2 : ℕ) : ℤ) := by
    have hd_div : (γ 1 1 : ℤ) = 2 * (d₀ / 2 : ℕ) + 1 := by
      have := Nat.div_add_mod d₀ 2; have := Nat.odd_iff.mp hodd_d₀; omega
    have hbase : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) - 3 * γ 1 1) -
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) - 3) = -6 * (γ 1 1 - 1) := by
      linear_combination -γ 1 0 * γ 1 1 * hdet
    linear_combination hbase +
      (by rw [hd_div]; ring : -6 * (γ 1 1 - 1) + 12 * ((d₀ / 2 : ℕ) : ℤ) = 0)
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [TauCeti.ModularGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_left hodd_d, ite_eq_right hnot_odd_c, hsym, hnum]
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
    3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1
  set k : ℕ := d₀ / 2
  have hexp : 2 * π * I * (((N - 3) - 12 * (k : ℤ) : ℤ) : ℂ) / 24 =
      -(k : ℂ) * (π * I) + (-(π * I / 4) + 2 * π * I * (N : ℂ) / 24) := by
    push_cast
    ring
  have hsign : (-1 : ℂ) ^ k * cexp (-(k : ℂ) * (π * I)) = 1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_pi_mul_I,
      mul_inv_cancel₀ (pow_ne_zero k (by norm_num))]
  rw [hexp, Complex.exp_add, Complex.exp_add]
  linear_combination cexp (-(π * I / 4)) * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
    cexp (2 * π * I * (N : ℂ) / 24) * hsign

private theorem kroneckerEtaMultiplier_mul_S_of_odd_of_even {γ : SL(2, ℤ)} (hd : 0 < γ 1 1)
    (hodd_c : Odd (γ 1 0)) (heven_d : Even (γ 1 1)) :
    kroneckerEtaMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerEtaMultiplier γ := by
  have hnot_odd_d : ¬ Odd (γ 1 1) := Int.not_odd_iff_even.mpr heven_d
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hnum : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) +
      3 * -γ 1 0 - 3 - 3 * γ 1 1 * -γ 1 0 : ℤ) =
      ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) - 3 := by
    linear_combination -γ 1 0 * γ 1 1 * hdet
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [TauCeti.ModularGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_right hnot_odd_d, ite_eq_left hodd_c,
    kroneckerSym_neg_right_of_nonneg hd.le, hnum]
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0
  have hexp : 2 * π * I * ((N - 3 : ℤ) : ℂ) / 24 = -(π * I / 4) + 2 * π * I * (N : ℂ) / 24 := by
    push_cast
    ring
  rw [hexp, Complex.exp_add]
  ring

/-! ### Main Kronecker-symbol formulas -/

/-- **Kronecker-symbol formula for the eta multiplier** (Strömberg, Remark 2.5, equation (2.5)):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`, `ε(γ)` is given in terms of the Kronecker symbol
`(d / c)` when `c` is odd and `(c / d)` when `c` is even. -/
theorem etaMultiplier_eq_kroneckerSym (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        kroneckerSym (γ 1 1) (γ 1 0) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) / 24)
      else
        kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
              3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  symm
  refine eq_etaMultiplier_of_c_pos (f := kroneckerEtaMultiplier)
    (fun δ hδ ↦ kroneckerEtaMultiplier_of_c_eq_one hδ)
    (fun δ hδ ↦ ?_) (fun δ hδ0 hδ1 ↦ ?_) γ hc
  · rcases Int.even_or_odd (δ 1 0) with heven | hodd
    · exact kroneckerEtaMultiplier_mul_T_of_even heven
    · exact kroneckerEtaMultiplier_mul_T_of_odd hδ hodd
  · rcases Int.even_or_odd (δ 1 0) with heven_c | hodd_c
    · exact kroneckerEtaMultiplier_mul_S_of_even_of_odd hδ1 heven_c
        (odd_zero_zero_and_one_one_of_even heven_c).2
    · rcases Int.even_or_odd (δ 1 1) with heven_d | hodd_d
      · exact kroneckerEtaMultiplier_mul_S_of_odd_of_even hδ1 hodd_c heven_d
      · exact kroneckerEtaMultiplier_mul_S_of_odd_of_odd hδ0 hδ1 hodd_c hodd_d

/-- **Kronecker-symbol formula for odd positive `c`** (Strömberg, Remark 2.5, equation (2.5)):
`ε(γ) = (d / c) exp(2π i ((a + d) c - b d (c² - 1) - 3 c) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  rw [etaMultiplier_eq_kroneckerSym γ hc, ite_eq_left hodd]

/-- **Kronecker-symbol formula for even positive `c`** (Strömberg, Remark 2.5, equation (2.5)):
`ε(γ) = (c / d) exp(2π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_even (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (heven : Even (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  rw [etaMultiplier_eq_kroneckerSym γ hc, ite_eq_right (Int.not_odd_iff_even.mpr heven)]

/-- When `c = γ 1 0 > 0` is coprime to `6`, `24 ∣ c² - 1`, so the `b d (c² - 1)` term drops out:
`ε(γ) = (d / c) exp(π i (a + d - 3) c / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_of_isCoprime_six (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hc6 : IsCoprime (γ 1 0) 6) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (π * I * (((γ 0 0 + γ 1 1 - 3) * γ 1 0 : ℤ) : ℂ) / 12) := by
  have hc2 : ¬ (2 : ℤ) ∣ γ 1 0 := fun h2 ↦ by
    rcases Int.isUnit_iff.mp (hc6.isUnit_of_dvd' h2 ⟨3, by norm_num⟩) with h | h <;> omega
  have hc3 : ¬ (3 : ℤ) ∣ γ 1 0 := fun h3 ↦ by
    rcases Int.isUnit_iff.mp (hc6.isUnit_of_dvd' h3 ⟨2, by norm_num⟩) with h | h <;> omega
  have hodd : Odd (γ 1 0) := Int.odd_iff.mpr (by omega)
  have h24 : 24 ∣ γ 1 0 ^ 2 - 1 := by
    have hmul := twentyFour_dvd_mul_sq_sub_one_of_odd hodd
    have hcop3 : IsCoprime (γ 1 0) 3 :=
      (Prime.coprime_iff_not_dvd Int.prime_three).mpr hc3 |>.symm
    have h3_sq : 3 ∣ γ 1 0 ^ 2 - 1 :=
      hcop3.symm.dvd_of_dvd_mul_left (dvd_trans ⟨8, by norm_num⟩ hmul)
    exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3)
      (eight_dvd_sq_sub_one_of_odd hodd) h3_sq
  have hdvd : 24 ∣ ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) -
      (γ 0 0 + γ 1 1 - 3) * γ 1 0 := by
    obtain ⟨m, hm⟩ := h24
    exact ⟨-γ 0 1 * γ 1 1 * m, by linear_combination -γ 0 1 * γ 1 1 * hm⟩
  rw [etaMultiplier_eq_kroneckerSym_of_odd γ hc hodd,
    cexp_two_pi_I_intCast_div_twentyFour_congr hdvd]
  congr 2
  ring

/-! ### Exponential Dedekind-sum evaluation via the Kronecker symbol -/

/-- For `γ = (a b; c d) ∈ SL(2, ℤ)` with odd `c > 0`, comparing the Dedekind-sum and Kronecker
formulas for `ε(γ)` evaluates `exp(-π i s(d, c))` in closed form via `(d / c)`. -/
theorem cexp_neg_pi_mul_I_mul_dedekindSum_of_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    cexp (-(π * I * dedekindSum (γ 1 1) (γ 1 0))) =
      kroneckerSym (γ 1 1) (γ 1 0) *
        cexp (π * I * ((((γ 0 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) -
          γ 0 1 * γ 1 1 * γ 1 0 * (γ 1 0 ^ 2 - 1) -
          3 * γ 1 0 * (γ 1 0 - 1) : ℤ) : ℂ) / (12 * γ 1 0))) := by
  have h := (etaMultiplier_of_c_pos γ hc).symm.trans
    (etaMultiplier_eq_kroneckerSym_of_odd γ hc hodd)
  have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  set E : ℂ := π * I * (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - 1 / 4)
  have hlhs : cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) =
      cexp E * cexp (-(π * I * dedekindSum (γ 1 1) (γ 1 0))) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [E]
    ring
  rw [hlhs] at h
  apply mul_left_cancel₀ (Complex.exp_ne_zero E)
  rw [h, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [E]
  push_cast
  field_simp
  ring

/-- For `γ = (a b; c d) ∈ SL(2, ℤ)` with even `c > 0`, comparing the Dedekind-sum and Kronecker
formulas for `ε(γ)` evaluates `exp(-π i s(d, c))` in closed form via `(c / d)`. -/
theorem cexp_neg_pi_mul_I_mul_dedekindSum_of_even (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (heven : Even (γ 1 0)) :
    cexp (-(π * I * dedekindSum (γ 1 1) (γ 1 0))) =
      kroneckerSym (γ 1 0) (γ 1 1) *
        cexp (π * I * ((((γ 0 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) -
          γ 0 1 * γ 1 1 * γ 1 0 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 0 * (γ 1 1 - γ 1 0 * γ 1 1 + 1) - 3 * γ 1 0 : ℤ) : ℂ) / (12 * γ 1 0))) := by
  have h := (etaMultiplier_of_c_pos γ hc).symm.trans
    (etaMultiplier_eq_kroneckerSym_of_even γ hc heven)
  have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  set E : ℂ := π * I * (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - 1 / 4)
  have hlhs : cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) =
      cexp E * cexp (-(π * I * dedekindSum (γ 1 1) (γ 1 0))) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [E]
    ring
  rw [hlhs] at h
  apply mul_left_cancel₀ (Complex.exp_ne_zero E)
  rw [h, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [E]
  push_cast
  field_simp
  ring

end TauCeti.ModularForm
