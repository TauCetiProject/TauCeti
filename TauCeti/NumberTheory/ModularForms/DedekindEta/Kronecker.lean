/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Data.Int.MulPred
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# The Kronecker-symbol formula for the eta multiplier

For `γ = (a b; c d) ∈ SL(2, ℤ)` and `e(x) = exp(2π i x)`, the Dedekind eta multiplier
`TauCeti.ModularForm.etaMultiplier` has the closed form (Strömberg, Remark 2.5, equation (2.5))
* `ε(γ) = (d / |c|) e(((a + d) c - b d (c² - 1) - 3 c) / 24)` when `c` is odd, and
* `ε(γ) = (c / d) e(((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)` when `c` is even,

where `(· / ·)` is the Kronecker symbol `TauCeti.kroneckerSym`. For `c ≥ 0`, `|c| = c`, so
`(d / |c|)` reduces to `(d / c)`. Unlike the Dedekind-sum formula in
`TauCeti.NumberTheory.ModularForms.DedekindEta.DedekindSum`, this expression exhibits the quadratic
character in `d` and `c` directly across all of `SL(2, ℤ)`, which is the input to the modularity
criterion for eta quotients on `Γ₀(N)`.

On `{c > 0}`, the proof applies the Euclidean uniqueness theorem `eq_etaMultiplier_of_c_pos`:
* at `c = 1`, `(d / 1) = 1` and the numerator simplifies to `a + d - 3`;
* under `γ ↦ γ T`, `c` keeps its parity: for odd `c` the symbol `(c + d / c) = (d / c)` is
  unchanged and the numerator shifts by `1` modulo `24`, while for even `c` both `4 ∣ c` and
  `c ≡ 2 (mod 4)` (`kroneckerSym_self_add_right_of_modEq_four_two`) match the shift of the
  numerator modulo `24`;
* under `γ ↦ γ S` (`c > 0` and `d > 0`), `a d - b c = 1` eliminates `a` and `b` from the numerator
  difference, and quadratic reciprocity together with its first supplement matches the sign change
  between the two Kronecker symbols across all three parity combinations of `(c, d)`.

The formulas then extend to `c = 0` via `etaMultiplier_of_c_eq_zero` and to `c < 0` via
`etaMultiplier_neg_of_c_neg`, where the sign factor `χ₄` from negating the Kronecker symbol
combines with `i` and the `-6 m` numerator shift.

## Main results

* `TauCeti.ModularForm.etaMultiplier_eq_ite_kroneckerSym_mul_cexp_of_c_nonneg`,
  `TauCeti.ModularForm.etaMultiplier_eq_ite_kroneckerSym_mul_cexp`: unified Kronecker-symbol
  formula for `c ≥ 0` and on all of `SL(2, ℤ)`.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_nonneg_of_odd_c`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_even_c`: the odd-`c` and
  even-`c` formulas.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_isCoprime_c_six`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_nonneg_of_isCoprime_c_six`:
  simplified formula `ε(γ) = (d / |c|) e^{π i (a + d - 3) c / 12}` when `c` is prime to `6`.

## References

* F. Strömberg, *Computation of Maass waveforms with non-trivial multiplier systems*,
  Math. Comp. 77 (2008), 2375–2416 (arXiv:math/0611146, 2006), Remark 2.5, equation (2.5).
* H. Rademacher, *Zur Theorie der Modulfunktionen*, J. Reine Angew. Math. 167 (1932), 312–336.
-/

public section

open Complex ModularGroup ZMod
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Candidate Kronecker expression and Euclidean steps -/

private theorem cexp_two_pi_I_add_one_div_twentyFour (n : ℤ) :
    cexp (2 * π * I * ((n + 1 : ℤ) : ℂ) / 24) =
      cexp (π * I / 12) * cexp (2 * π * I * (n : ℂ) / 24) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem neg_one_pow_mul_cexp_sub_three_sub_twelve_mul (n : ℤ) (k : ℕ) :
    (-1 : ℂ) ^ k * cexp (2 * π * I * (((n - 3) - 12 * (k : ℤ) : ℤ) : ℂ) / 24) =
      cexp (-(π * I / 4)) * cexp (2 * π * I * (n : ℂ) / 24) := by
  have hexp : 2 * π * I * (((n - 3) - 12 * (k : ℤ) : ℤ) : ℂ) / 24 =
      -(k : ℂ) * (π * I) + (-(π * I / 4) + 2 * π * I * (n : ℂ) / 24) := by
    push_cast
    ring
  have hsign : (-1 : ℂ) ^ k * cexp (-(k : ℂ) * (π * I)) = 1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_natCast_mul, Complex.exp_pi_mul_I,
      mul_inv_cancel₀ (pow_ne_zero k (by norm_num))]
  rw [hexp, Complex.exp_add, Complex.exp_add]
  linear_combination cexp (-(π * I / 4)) * cexp (2 * π * I * (n : ℂ) / 24) * hsign

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
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  have hsym : kroneckerSym (γ 1 0 + γ 1 1) (γ 1 0) = kroneckerSym (γ 1 1) (γ 1 0) := by
    have hc_nat : (γ 1 0 : ℤ) = (γ 1 0).natAbs := (Int.natAbs_of_nonneg hc.le).symm
    have hodd_nat : Odd (γ 1 0).natAbs := Int.natAbs_odd.mpr hodd
    rw [hc_nat, kroneckerSym_eq_jacobiSym _ hodd_nat, kroneckerSym_eq_jacobiSym _ hodd_nat]
    exact jacobiSym.mod_left' (Int.add_emod_left _ _)
  have hdvd : (24 : ℤ) ∣
      ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 - (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) -
        3 * γ 1 0) -
      (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) + 1) := by
    obtain ⟨m, hm⟩ := Int.twentyFour_dvd_mul_sq_sub_one_of_odd hodd
    refine ⟨-(γ 0 0 + 2 * γ 0 1) * m, ?_⟩
    linear_combination -(γ 1 0 ^ 2 - 1) * hdet - (γ 0 0 + 2 * γ 0 1) * hm
  have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub hdvd
  rw [Int.cast_ofNat] at hexp
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [Matrix.SpecialLinearGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_left hodd, ite_eq_left hodd, hsym, hexp, cexp_two_pi_I_add_one_div_twentyFour]
  ring

private theorem even_T_num_diff (γ : SL(2, ℤ)) :
    ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 - (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) +
      3 * (γ 1 0 + γ 1 1) - 3 - 3 * γ 1 0 * (γ 1 0 + γ 1 1)) -
    (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
      3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) + 1) =
    -(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) + 3 * γ 1 0 * (1 - γ 1 0) := by
  linear_combination -(γ 1 0 ^ 2 - 1) * γ.fin_two_mul_sub_mul_eq_one

private theorem three_dvd_even_T_num_diff (a b c : ℤ) :
    (3 : ℤ) ∣ -(a + 2 * b) * c * (c ^ 2 - 1) + 3 * c * (1 - c) := by
  obtain ⟨u, hu⟩ := Int.three_dvd_mul_sq_sub_one c
  exact ⟨-(a + 2 * b) * u + c * (1 - c), by linear_combination -(a + 2 * b) * hu⟩

/-- When `c = γ 1 0 = 2 m` with `m` odd, reducing `a d - b c = 1` modulo `4` yields
`a + 2 b ≡ d (mod 4)`. -/
private theorem four_dvd_add_two_mul_sub_of_even_c {γ : SL(2, ℤ)} {m : ℤ}
    (hc : γ 1 0 = 2 * m) (hm : Odd m) :
    (4 : ℤ) ∣ γ 0 0 + 2 * γ 0 1 - γ 1 1 := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  have hodd_d : Odd (γ 1 1) :=
    (Matrix.SpecialLinearGroup.odd_apply_zero_zero_and_apply_one_one_of_even_apply_one_zero
      ⟨m, by omega⟩).2
  obtain ⟨u, hu⟩ := Int.eight_dvd_sq_sub_one_of_odd hodd_d
  obtain ⟨v, hv⟩ : Even (m * γ 1 1 + 1) := (hm.mul hodd_d).add_odd odd_one
  refine ⟨-2 * γ 0 0 * u + γ 0 1 * v, ?_⟩
  rw [hc] at hdet
  linear_combination γ 1 1 * hdet - γ 0 0 * hu + 2 * γ 0 1 * hv

/-- When `c = γ 1 0 = 2 m` with `m` odd, the `T`-step numerator shift is congruent to
`-6 (d + 1)` modulo `24` (`-12` when `d ≡ 1 (mod 4)` and `0` when `d ≡ 3 (mod 4)`). -/
private theorem twentyFour_dvd_even_T_num_diff_add_six_mul {γ : SL(2, ℤ)} {m : ℤ}
    (hc : γ 1 0 = 2 * m) (hm : Odd m) :
    (24 : ℤ) ∣ (-(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) + 3 * γ 1 0 * (1 - γ 1 0)) +
      6 * (γ 1 1 + 1) := by
  have hodd_d : Odd (γ 1 1) :=
    (Matrix.SpecialLinearGroup.odd_apply_zero_zero_and_apply_one_one_of_even_apply_one_zero
      ⟨m, by omega⟩).2
  obtain ⟨q, hq⟩ := four_dvd_add_two_mul_sub_of_even_c hc hm
  have hab : γ 0 0 + 2 * γ 0 1 = γ 1 1 + 4 * q := by linear_combination hq
  have hdecomp : (-(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) +
      3 * γ 1 0 * (1 - γ 1 0)) + 6 * (γ 1 1 + 1) =
      8 * (-q * m * (γ 1 0 ^ 2 - 1) - γ 1 1 * m ^ 3 + γ 1 1 + m - 1) -
        12 * (m ^ 2 - 1) + 2 * (γ 1 1 - 1) * (m - 1) := by
    rw [hab, hc]
    ring
  have h8 : (8 : ℤ) ∣ (-(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) +
      3 * γ 1 0 * (1 - γ 1 0)) + 6 * (γ 1 1 + 1) := by
    rw [hdecomp]
    have h8_sq : (8 : ℤ) ∣ 12 * (m ^ 2 - 1) :=
      dvd_mul_of_dvd_right (Int.eight_dvd_sq_sub_one_of_odd hm) 12
    have h8_prod : (8 : ℤ) ∣ 2 * (γ 1 1 - 1) * (m - 1) := by
      obtain ⟨s, rfl⟩ := hm
      obtain ⟨t, ht⟩ := hodd_d
      rw [ht]
      exact ⟨t * s, by ring⟩
    exact dvd_add (dvd_sub (dvd_mul_right 8 _) h8_sq) h8_prod
  have h3 : (3 : ℤ) ∣ (-(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) +
      3 * γ 1 0 * (1 - γ 1 0)) + 6 * (γ 1 1 + 1) :=
    dvd_add (three_dvd_even_T_num_diff (γ 0 0) (γ 0 1) (γ 1 0)) ⟨2 * (γ 1 1 + 1), by ring⟩
  exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3) h8 h3

private theorem kroneckerEtaMultiplier_mul_T_of_four_dvd {γ : SL(2, ℤ)} (k : ℤ)
    (hc : γ 1 0 = 4 * k) :
    kroneckerEtaMultiplier (γ * T) = cexp (π * I / 12) * kroneckerEtaMultiplier γ := by
  have heven : Even (γ 1 0) := ⟨2 * k, by omega⟩
  have hnot_odd : ¬ Odd (γ 1 0) := Int.not_odd_iff_even.mpr heven
  have hodd_a : Odd (γ 0 0) :=
    (Matrix.SpecialLinearGroup.odd_apply_zero_zero_and_apply_one_one_of_even_apply_one_zero heven).1
  have hc4 : γ 1 0 ≡ 0 [ZMOD 4] := by
    rw [Int.ModEq, hc]
    omega
  have hsym : kroneckerSym (γ 1 0) (γ 1 0 + γ 1 1) = kroneckerSym (γ 1 0) (γ 1 1) :=
    kroneckerSym_mod_right' (.inl hc4) (Int.add_emod_left _ _)
  have h8 : (8 : ℤ) ∣ -(γ 0 0 + 2 * γ 0 1) * γ 1 0 * (γ 1 0 ^ 2 - 1) + 3 * γ 1 0 * (1 - γ 1 0) := by
    obtain ⟨t, ht⟩ := hodd_a
    refine ⟨k * (t + γ 0 1 + 2 - 8 * (2 * t + 1 + 2 * γ 0 1) * k ^ 2 - 6 * k), ?_⟩
    rw [ht, hc]
    ring
  have h24 : (24 : ℤ) ∣
      ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 - (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) +
        3 * (γ 1 0 + γ 1 1) - 3 - 3 * γ 1 0 * (γ 1 0 + γ 1 1)) -
      (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) + 1) := by
    rw [even_T_num_diff]
    exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3) h8
      (three_dvd_even_T_num_diff (γ 0 0) (γ 0 1) (γ 1 0))
  have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub h24
  rw [Int.cast_ofNat] at hexp
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [Matrix.SpecialLinearGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_right hnot_odd, ite_eq_right hnot_odd, hsym, hexp,
    cexp_two_pi_I_add_one_div_twentyFour]
  ring

private theorem kroneckerEtaMultiplier_mul_T_of_modEq_two {γ : SL(2, ℤ)} {m : ℤ}
    (hc : γ 1 0 = 2 * m) (hm : Odd m) :
    kroneckerEtaMultiplier (γ * T) = cexp (π * I / 12) * kroneckerEtaMultiplier γ := by
  have heven : Even (γ 1 0) := ⟨m, by omega⟩
  have hnot_odd : ¬ Odd (γ 1 0) := Int.not_odd_iff_even.mpr heven
  have hodd_d : Odd (γ 1 1) :=
    (Matrix.SpecialLinearGroup.odd_apply_zero_zero_and_apply_one_one_of_even_apply_one_zero heven).2
  have hc2 : γ 1 0 ≡ 2 [ZMOD 4] := by
    obtain ⟨s, rfl⟩ := hm
    rw [Int.ModEq, hc]
    omega
  have hsym := kroneckerSym_self_add_right_of_modEq_four_two hc2 (γ 1 1)
  obtain ⟨u, hu⟩ := twentyFour_dvd_even_T_num_diff_add_six_mul hc hm
  rw [← even_T_num_diff γ] at hu
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [Matrix.SpecialLinearGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_right hnot_odd, ite_eq_right hnot_odd, hsym]
  set M : ℤ := (γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 -
    (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) +
    3 * (γ 1 0 + γ 1 1) - 3 - 3 * γ 1 0 * (γ 1 0 + γ 1 1)
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
    3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1
  rcases (by obtain ⟨t, ht⟩ := hodd_d; omega : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3) with hd4 | hd4
  · have hχ : χ₄ (γ 1 1 : ZMod 4) = 1 := χ₄_int_one_mod_four hd4
    obtain ⟨v, hv⟩ : (4 : ℤ) ∣ γ 1 1 - 1 := ⟨γ 1 1 / 4, by omega⟩
    have h24 : (2 * 12 : ℤ) ∣ M - (N + 1) + 12 := ⟨u - v, by linear_combination hu - 6 * hv⟩
    have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_two_mul_eq_neg_of_dvd
      (by decide : (12 : ℤ) ≠ 0) h24
    have h24_cast : (2 : ℂ) * ((12 : ℤ) : ℂ) = 24 := by norm_num
    rw [h24_cast] at hexp
    rw [hχ, hexp, cexp_two_pi_I_add_one_div_twentyFour]
    push_cast
    ring
  · have hχ : χ₄ (γ 1 1 : ZMod 4) = -1 := χ₄_int_three_mod_four hd4
    obtain ⟨v, hv⟩ : (4 : ℤ) ∣ γ 1 1 + 1 := ⟨γ 1 1 / 4 + 1, by omega⟩
    have h24 : (24 : ℤ) ∣ M - (N + 1) := ⟨u - v, by linear_combination hu - 6 * hv⟩
    have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub h24
    rw [Int.cast_ofNat] at hexp
    rw [hχ, hexp, cexp_two_pi_I_add_one_div_twentyFour]
    push_cast
    ring

private theorem kroneckerEtaMultiplier_mul_T_of_even {γ : SL(2, ℤ)}
    (heven : Even (γ 1 0)) :
    kroneckerEtaMultiplier (γ * T) = cexp (π * I / 12) * kroneckerEtaMultiplier γ := by
  obtain ⟨m, hm⟩ := heven
  rcases Int.even_or_odd m with ⟨k, rfl⟩ | hm_odd
  · exact kroneckerEtaMultiplier_mul_T_of_four_dvd k (by omega)
  · exact kroneckerEtaMultiplier_mul_T_of_modEq_two (by omega) hm_odd

private theorem kroneckerEtaMultiplier_mul_S_of_odd_of_odd {γ : SL(2, ℤ)} (hc : 0 < γ 1 0)
    (hd : 0 < γ 1 1) (hodd_c : Odd (γ 1 0)) (hodd_d : Odd (γ 1 1)) :
    kroneckerEtaMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerEtaMultiplier γ := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  set c₀ : ℕ := (γ 1 0).natAbs
  set d₀ : ℕ := (γ 1 1).natAbs
  have hc₀ : (c₀ : ℤ) = γ 1 0 := Int.natAbs_of_nonneg hc.le
  have hd₀ : (d₀ : ℤ) = γ 1 1 := Int.natAbs_of_nonneg hd.le
  have hodd_c₀ : Odd c₀ := Int.natAbs_odd.mpr hodd_c
  have hodd_d₀ : Odd d₀ := Int.natAbs_odd.mpr hodd_d
  have hsym : (kroneckerSym (-γ 1 0) (γ 1 1) : ℂ) =
      (-1 : ℂ) ^ ((c₀ / 2 + 1) * (d₀ / 2)) * kroneckerSym (γ 1 1) (γ 1 0) := by
    have hpow : d₀ / 2 + c₀ / 2 * (d₀ / 2) = (c₀ / 2 + 1) * (d₀ / 2) := by ring
    rw [← hc₀, ← hd₀, kroneckerSym_eq_jacobiSym _ hodd_d₀, kroneckerSym_eq_jacobiSym _ hodd_c₀,
      jacobiSym.neg _ hodd_d₀, χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd_d₀),
      jacobiSym.quadratic_reciprocity hodd_c₀ hodd_d₀]
    push_cast
    rw [← mul_assoc, ← pow_add, hpow]
  have hnum : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) - 3 * γ 1 1 : ℤ) =
      (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) - 3) -
        12 * (((c₀ / 2 + 1) * (d₀ / 2) : ℕ) : ℤ) := by
    have hc_div : (γ 1 0 : ℤ) = 2 * (c₀ / 2 : ℕ) + 1 := by
      rw [← hc₀]
      exact_mod_cast (Nat.two_mul_div_two_add_one_of_odd hodd_c₀).symm
    have hd_div : (γ 1 1 : ℤ) = 2 * (d₀ / 2 : ℕ) + 1 := by
      rw [← hd₀]
      exact_mod_cast (Nat.two_mul_div_two_add_one_of_odd hodd_d₀).symm
    have hbase : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) - 3 * γ 1 1) -
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) - 3) =
        -3 * (γ 1 0 + 1) * (γ 1 1 - 1) := by
      linear_combination -γ 1 0 * γ 1 1 * hdet
    have hprod : -3 * (γ 1 0 + 1) * (γ 1 1 - 1) +
        12 * (((c₀ / 2 : ℕ) : ℤ) + 1) * ((d₀ / 2 : ℕ) : ℤ) = 0 := by
      rw [hc_div, hd_div]
      ring
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    linear_combination hbase + hprod
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [Matrix.SpecialLinearGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_left hodd_d, ite_eq_left hodd_c, hsym, hnum, mul_right_comm,
    neg_one_pow_mul_cexp_sub_three_sub_twelve_mul]
  ring

private theorem kroneckerEtaMultiplier_mul_S_of_even_of_odd {γ : SL(2, ℤ)} (hd : 0 < γ 1 1)
    (heven_c : Even (γ 1 0)) (hodd_d : Odd (γ 1 1)) :
    kroneckerEtaMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerEtaMultiplier γ := by
  have hnot_odd_c : ¬ Odd (γ 1 0) := Int.not_odd_iff_even.mpr heven_c
  have hdet := γ.fin_two_mul_sub_mul_eq_one
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
      rw [← hd₀]
      exact_mod_cast (Nat.two_mul_div_two_add_one_of_odd hodd_d₀).symm
    have hbase : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) - 3 * γ 1 1) -
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1) - 3) = -6 * (γ 1 1 - 1) := by
      linear_combination -γ 1 0 * γ 1 1 * hdet
    have hprod : -6 * (γ 1 1 - 1) + 12 * ((d₀ / 2 : ℕ) : ℤ) = 0 := by
      rw [hd_div]
      ring
    linear_combination hbase + hprod
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [Matrix.SpecialLinearGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_left hodd_d, ite_eq_right hnot_odd_c, hsym, hnum, mul_right_comm,
    neg_one_pow_mul_cexp_sub_three_sub_twelve_mul]
  ring

private theorem kroneckerEtaMultiplier_mul_S_of_odd_of_even {γ : SL(2, ℤ)} (hd : 0 < γ 1 1)
    (hodd_c : Odd (γ 1 0)) (heven_d : Even (γ 1 1)) :
    kroneckerEtaMultiplier (γ * S) = cexp (-(π * I / 4)) * kroneckerEtaMultiplier γ := by
  have hnot_odd_d : ¬ Odd (γ 1 1) := Int.not_odd_iff_even.mpr heven_d
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  have hnum : ((γ 0 1 + -γ 1 0) * γ 1 1 - -γ 0 0 * -γ 1 0 * (γ 1 1 ^ 2 - 1) +
      3 * -γ 1 0 - 3 - 3 * γ 1 1 * -γ 1 0 : ℤ) =
      ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) - 3 := by
    linear_combination -γ 1 0 * γ 1 1 * hdet
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0
  have hexp : cexp (2 * π * I * ((N - 3 : ℤ) : ℂ) / 24) =
      cexp (-(π * I / 4)) * cexp (2 * π * I * (N : ℂ) / 24) := by
    simpa using neg_one_pow_mul_cexp_sub_three_sub_twelve_mul N 0
  rw [kroneckerEtaMultiplier, kroneckerEtaMultiplier]
  simp only [Matrix.SpecialLinearGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ite_eq_right hnot_odd_d, ite_eq_left hodd_c,
    kroneckerSym_neg_right_of_nonneg hd.le, hnum, hexp]
  ring

private theorem etaMultiplier_eq_kronecker_even_of_c_eq_zero {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  rw [hc, mul_zero, sub_zero] at hdet
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨_, hd⟩ | ⟨_, hd⟩
  · rw [etaMultiplier_of_c_eq_zero_of_d_pos γ hc (by omega), hc, hd, kroneckerSym_one_right,
      Int.cast_one, one_mul]
    congr 1
    push_cast
    ring
  · have hexp : 2 * π * I *
        (((γ 0 0 + -1) * 0 - γ 0 1 * -1 * (0 ^ 2 - 1) + 3 * -1 - 3 - 3 * 0 * -1 : ℤ) : ℂ) / 24 =
        -π / 2 * I + -(π * I * γ 0 1 / 12) := by
      push_cast
      ring
    rw [etaMultiplier_of_c_eq_zero_of_d_neg γ hc (by omega), hc, hd,
      kroneckerSym_zero_left, ite_eq_left (Or.inr rfl), Int.cast_one, one_mul,
      hexp, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]

/-! ### Main Kronecker-symbol formulas -/

/-- **Kronecker-symbol formula for the eta multiplier for `c ≥ 0`** (Strömberg, Remark 2.5,
equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c ≥ 0`, `|c| = c`, so `ε(γ)` is given in
terms of `(d / c)` when `c` is odd and `(c / d)` when `c` is even. -/
theorem etaMultiplier_eq_ite_kroneckerSym_mul_cexp_of_c_nonneg (γ : SL(2, ℤ)) (hc : 0 ≤ γ 1 0) :
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
  rcases hc.eq_or_lt with hc0 | hc_pos
  · rw [ite_eq_right (hc0 ▸ Int.not_odd_zero)]
    exact etaMultiplier_eq_kronecker_even_of_c_eq_zero hc0.symm
  · symm
    refine eq_etaMultiplier_of_c_pos (f := kroneckerEtaMultiplier)
      (fun δ hδ ↦ kroneckerEtaMultiplier_of_c_eq_one hδ)
      (fun δ hδ ↦ ?_) (fun δ hδ0 hδ1 ↦ ?_) γ hc_pos
    · rcases Int.even_or_odd (δ 1 0) with heven | hodd
      · exact kroneckerEtaMultiplier_mul_T_of_even heven
      · exact kroneckerEtaMultiplier_mul_T_of_odd hδ hodd
    · rcases Int.even_or_odd (δ 1 0) with heven_c | hodd_c
      · exact kroneckerEtaMultiplier_mul_S_of_even_of_odd hδ1 heven_c
          (Matrix.SpecialLinearGroup.odd_apply_zero_zero_and_apply_one_one_of_even_apply_one_zero
            heven_c).2
      · rcases Int.even_or_odd (δ 1 1) with heven_d | hodd_d
        · exact kroneckerEtaMultiplier_mul_S_of_odd_of_even hδ1 hodd_c heven_d
        · exact kroneckerEtaMultiplier_mul_S_of_odd_of_odd hδ0 hδ1 hodd_c hodd_d

/-- For odd `m`, the sign factor `χ₄ m * i` cancels the `-6 m` numerator shift in
`exp(2π i (N - 6 m) / 24)`: for `m ≡ 1 (mod 4)` it is `1 * i * (-i) = 1`, and for `m ≡ 3 (mod 4)`
it is `(-1) * i * i = 1`. -/
private theorem chi4_mul_I_mul_cexp_sub_six_mul (N : ℤ) {m : ℤ} (hm : Odd m) :
    (χ₄ (m : ZMod 4) : ℂ) * I * cexp (2 * π * I * ((N - 6 * m : ℤ) : ℂ) / 24) =
      cexp (2 * π * I * (N : ℂ) / 24) := by
  rcases (by obtain ⟨t, rfl⟩ := hm; omega : m % 4 = 1 ∨ m % 4 = 3) with hm4 | hm4
  · have hχ : χ₄ (m : ZMod 4) = 1 := χ₄_int_one_mod_four hm4
    have hI : (I : ℂ) * -I = 1 := by simp
    have hdvd : (24 : ℤ) ∣ (N - 6 * m) - (N - 6) := ⟨-(m / 4), by omega⟩
    have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub hdvd
    have hsplit : 2 * π * I * ((N - 6 : ℤ) : ℂ) / 24 =
        -π / 2 * I + 2 * π * I * (N : ℂ) / 24 := by
      push_cast
      ring
    rw [Int.cast_ofNat] at hexp
    rw [hχ, Int.cast_one, one_mul, hexp, hsplit, Complex.exp_add,
      Complex.exp_neg_pi_div_two_mul_I, ← mul_assoc, hI, one_mul]
  · have hχ : χ₄ (m : ZMod 4) = -1 := χ₄_int_three_mod_four hm4
    have hI : (-1 : ℂ) * I * I = 1 := by simp
    have hdvd : (24 : ℤ) ∣ (N - 6 * m) - (N + 6) := ⟨-(m / 4 + 1), by omega⟩
    have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub hdvd
    have hsplit : 2 * π * I * ((N + 6 : ℤ) : ℂ) / 24 =
        π / 2 * I + 2 * π * I * (N : ℂ) / 24 := by
      push_cast
      ring
    rw [Int.cast_ofNat] at hexp
    rw [hχ, Int.cast_neg, Int.cast_one, hexp, hsplit, Complex.exp_add,
      Complex.exp_pi_div_two_mul_I, ← mul_assoc, hI, one_mul]

private theorem etaMultiplier_eq_kronecker_even_of_c_neg {γ : SL(2, ℤ)} (hc : γ 1 0 < 0)
    (heven : Even (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  have hodd_d : Odd (γ 1 1) :=
    (Matrix.SpecialLinearGroup.odd_apply_zero_zero_and_apply_one_one_of_even_apply_one_zero heven).2
  have hneg_pos : 0 < (-γ) 1 0 := by simpa using hc
  have hnot_odd : ¬ Odd ((-γ) 1 0) :=
    Int.not_odd_iff_even.mpr (by simpa using heven.neg)
  have hmul : etaMultiplier γ = I * etaMultiplier (-γ) := by
    rw [etaMultiplier_neg_of_c_neg γ hc, ← mul_assoc]
    simp
  have hsym : kroneckerSym (-γ 1 0) (-γ 1 1) =
      χ₄ (γ 1 1 : ZMod 4) * kroneckerSym (γ 1 0) (γ 1 1) := by
    have hneg_eq : (-γ 1 0 : ℤ) = (-1) * γ 1 0 := by ring
    rw [kroneckerSym_neg_right_of_nonneg (by omega), hneg_eq,
      kroneckerSym_mul_left (by norm_num) hc.ne, kroneckerSym_neg_one_left_of_odd hodd_d]
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
    3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1
  have hnum : (((-γ 0 0 + -γ 1 1) * -γ 1 0 - -γ 0 1 * -γ 1 1 * ((-γ 1 0) ^ 2 - 1) +
      3 * -γ 1 1 - 3 - 3 * -γ 1 0 * -γ 1 1 : ℤ)) = N - 6 * γ 1 1 := by
    simp only [N]
    ring
  rw [hmul, etaMultiplier_eq_ite_kroneckerSym_mul_cexp_of_c_nonneg (-γ) hneg_pos.le,
    ite_eq_right hnot_odd]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  rw [hsym, hnum, Int.cast_mul, ← chi4_mul_I_mul_cexp_sub_six_mul N hodd_d]
  ring

private theorem etaMultiplier_eq_kronecker_odd_of_c_neg {γ : SL(2, ℤ)} (hc : γ 1 0 < 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0).natAbs *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  have hneg_pos : 0 < (-γ) 1 0 := by simpa using hc
  have hodd_neg : Odd ((-γ) 1 0) := by simpa using hodd.neg
  have hodd_abs : Odd (γ 1 0).natAbs := Int.natAbs_odd.mpr hodd
  have habs : ((γ 1 0).natAbs : ℤ) = -γ 1 0 := Int.ofNat_natAbs_of_nonpos hc.le
  have hmul : etaMultiplier γ = I * etaMultiplier (-γ) := by
    rw [etaMultiplier_neg_of_c_neg γ hc, ← mul_assoc]
    simp
  have hsym : kroneckerSym (-γ 1 1) (-γ 1 0) =
      χ₄ ((-γ 1 0 : ℤ) : ZMod 4) * kroneckerSym (γ 1 1) (γ 1 0).natAbs := by
    rw [← habs, kroneckerSym_eq_jacobiSym _ hodd_abs, kroneckerSym_eq_jacobiSym _ hodd_abs,
      jacobiSym.neg _ hodd_abs, Int.cast_natCast]
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0
  have hnum : (((-γ 0 0 + -γ 1 1) * -γ 1 0 - -γ 0 1 * -γ 1 1 * ((-γ 1 0) ^ 2 - 1) -
      3 * -γ 1 0 : ℤ)) = N - 6 * (-γ 1 0) := by
    simp only [N]
    ring
  rw [hmul, etaMultiplier_eq_ite_kroneckerSym_mul_cexp_of_c_nonneg (-γ) hneg_pos.le,
    ite_eq_left hodd_neg]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  rw [hsym, hnum, Int.cast_mul, ← chi4_mul_I_mul_cexp_sub_six_mul N hodd.neg]
  ring

/-- **Kronecker-symbol formula for the eta multiplier** on all of `SL(2, ℤ)` (Strömberg,
Remark 2.5, equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)`, `ε(γ)` is given in terms of the
Kronecker symbol `(d / |c|)` when `c` is odd and `(c / d)` when `c` is even. -/
theorem etaMultiplier_eq_ite_kroneckerSym_mul_cexp (γ : SL(2, ℤ)) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        kroneckerSym (γ 1 1) (γ 1 0).natAbs *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) / 24)
      else
        kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
              3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  rcases lt_or_ge (γ 1 0) 0 with hc | hc
  · by_cases hodd : Odd (γ 1 0)
    · rw [ite_eq_left hodd]
      exact etaMultiplier_eq_kronecker_odd_of_c_neg hc hodd
    · rw [ite_eq_right hodd]
      exact etaMultiplier_eq_kronecker_even_of_c_neg hc (Int.not_odd_iff_even.mp hodd)
  · rw [etaMultiplier_eq_ite_kroneckerSym_mul_cexp_of_c_nonneg γ hc, Int.natAbs_of_nonneg hc]

/-- **Kronecker-symbol formula for odd `c`** on `SL(2, ℤ)`:
`ε(γ) = (d / |c|) exp(2π i ((a + d) c - b d (c² - 1) - 3 c) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c (γ : SL(2, ℤ)) (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0).natAbs *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  rw [etaMultiplier_eq_ite_kroneckerSym_mul_cexp γ, ite_eq_left hodd]

/-- **Kronecker-symbol formula for odd nonnegative `c`** (Strömberg, Remark 2.5, equation (2.5)):
`ε(γ) = (d / c) exp(2π i ((a + d) c - b d (c² - 1) - 3 c) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_nonneg_of_odd_c (γ : SL(2, ℤ))
    (hc : 0 ≤ γ 1 0) (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  rw [etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c γ hodd, Int.natAbs_of_nonneg hc]

/-- **Kronecker-symbol formula for even `c`** on all of `SL(2, ℤ)` (Strömberg, Remark 2.5,
equation (2.5)): `ε(γ) = (c / d) exp(2π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_even_c (γ : SL(2, ℤ)) (heven : Even (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  rw [etaMultiplier_eq_ite_kroneckerSym_mul_cexp γ,
    ite_eq_right (Int.not_odd_iff_even.mpr heven)]

/-- When `c = γ 1 0` is coprime to `6`, `24 ∣ c² - 1`, so the `b d (c² - 1)` term drops out:
`ε(γ) = (d / |c|) exp(π i (a + d - 3) c / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_isCoprime_c_six (γ : SL(2, ℤ))
    (hc6 : IsCoprime (γ 1 0) 6) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0).natAbs *
      cexp (π * I * (((γ 0 0 + γ 1 1 - 3) * γ 1 0 : ℤ) : ℂ) / 12) := by
  have hc' : IsCoprime (γ 1 0) (2 * 3) := hc6
  have hodd : Odd (γ 1 0) := Int.isCoprime_two_right.mp hc'.of_mul_right_left
  obtain ⟨m, hm⟩ := Int.twentyFour_dvd_sq_sub_one_of_isCoprime_six hc6
  have hdvd : (24 : ℤ) ∣ ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) -
      (γ 0 0 + γ 1 1 - 3) * γ 1 0 :=
    ⟨-γ 0 1 * γ 1 1 * m, by linear_combination -γ 0 1 * γ 1 1 * hm⟩
  have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub hdvd
  rw [Int.cast_ofNat] at hexp
  rw [etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c γ hodd, hexp]
  congr 2
  ring

/-- When `c = γ 1 0 ≥ 0` is coprime to `6`, `24 ∣ c² - 1`, so the `b d (c² - 1)` term drops out:
`ε(γ) = (d / c) exp(π i (a + d - 3) c / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_nonneg_of_isCoprime_c_six (γ : SL(2, ℤ))
    (hc : 0 ≤ γ 1 0) (hc6 : IsCoprime (γ 1 0) 6) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (π * I * (((γ 0 0 + γ 1 1 - 3) * γ 1 0 : ℤ) : ℂ) / 12) := by
  rw [etaMultiplier_eq_kroneckerSym_mul_cexp_of_isCoprime_c_six γ hc6,
    Int.natAbs_of_nonneg hc]

end TauCeti.ModularForm
