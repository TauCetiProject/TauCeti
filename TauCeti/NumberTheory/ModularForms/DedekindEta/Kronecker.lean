/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.DedekindSum
import TauCeti.Data.Int.MulPred

/-!
# The Kronecker-symbol formula for the eta multiplier

For `γ = (a b; c d) ∈ SL(2, ℤ)` with `0 < c` and `e(x) = exp(2π i x)`, the Dedekind-sum formula
`TauCeti.ModularForm.etaMultiplier_of_c_pos` does not directly exhibit the quadratic character in
the eta multiplier `ε(γ)`. Rewriting it via the Kronecker symbol `TauCeti.kroneckerSym` gives:

* when `c` is odd (`TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd`),
  `ε(γ) = (d / c) e(((a + d) c - b d (c² - 1) - 3 c) / 24)`;
* when `c` is even (`TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_even`),
  `ε(γ) = (c / d) e(((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`.

This form is the input to the modularity and nebentypus criterion for eta quotients on `Γ₀(N)`,
where the product of the Kronecker factors across the divisors of `N` collapses to a quadratic
Dirichlet character. Combining the Kronecker and Dedekind-sum formulas also evaluates
`exp(-π i s(d, c))` in terms of the Kronecker symbol for `γ ∈ SL(2, ℤ)` with `0 < c`.

## Implementation notes

The proof inducts strongly on `c` along the Euclidean algorithm on `(d, c)`:
* under right translation `γ ↦ γ T`, `24 ∣ c (c² - 1)` when `c` is odd, `4 ∣ c` makes `(c / ·)`
  periodic modulo `c` while shifting the numerator by `1 (mod 24)`, and when `c = 2 m` with `m` odd
  both `(2 m / ·)` (`TauCeti.kroneckerSym_two_mul_add_self_of_odd`) and `e(num / 24)` pick up the
  compensating sign `(-1) ^ ((d + 1) / 2)`;
* under right inversion `γ ↦ γ S` for `0 < c` and `0 < d`, quadratic reciprocity and the first
  supplementary law for the Jacobi symbol match the sign flips of `(d / c)` and `(c / d)` with the
  exact polynomial differences of the numerators.

## Main results

* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd`: the Kronecker-symbol formula
  for `ε(γ)` when `0 < c` and `c` is odd.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_even`: the Kronecker-symbol formula
  for `ε(γ)` when `0 < c` and `c` is even.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_pos`: the unified `0 < c`
  formula.
* `TauCeti.ModularForm.kroneckerSym_mul_cexp_eq_cexp_dedekindSum_of_odd`,
  `TauCeti.ModularForm.kroneckerSym_mul_cexp_eq_cexp_dedekindSum_of_even`: comparison identities
  with the Dedekind sum `s(d, c)`.

## References

* F. Strömberg, *Maass waveforms on `(Γ₀(N), χ)` (computational aspects)*, LMS Lecture Note Series
  403, Remark 2.5, equation (2.5).
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, Chapter 4.
-/

public section

open Complex ModularGroup ZMod
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### The unified Kronecker right-hand side and its generator laws -/

/-- The Kronecker-symbol sign `(d / c)` (for odd `c`) or `(c / d)` (for even `c`). -/
private def kroneckerSign (γ : SL(2, ℤ)) : ℤ :=
  if Odd (γ 1 0) then kroneckerSym (γ 1 1) (γ 1 0) else kroneckerSym (γ 1 0) (γ 1 1)

/-- The integer numerator inside `e(· / 24)` in the Kronecker formula for `ε(γ)`. -/
private def kroneckerNum (γ : SL(2, ℤ)) : ℤ :=
  if Odd (γ 1 0) then
    (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0
  else
    (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
      3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1

/-- The Kronecker expression for `ε(γ)`. -/
private noncomputable def kroneckerRhs (γ : SL(2, ℤ)) : ℂ :=
  (kroneckerSign γ : ℂ) * cexp (2 * π * I * ((kroneckerNum γ : ℂ) / 24))

/-- When `γ ∈ SL(2, ℤ)` has even lower-left entry `c`, both `a` and `d` are odd. -/
private theorem odd_entry_of_even_c (γ : SL(2, ℤ)) (heven : Even (γ 1 0)) :
    Odd (γ 0 0) ∧ Odd (γ 1 1) := by
  obtain ⟨k, hk⟩ := heven
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hk] at hdet
  have had : γ 0 0 * γ 1 1 = 2 * (γ 0 1 * k) + 1 := by linarith
  exact Int.odd_mul.mp ⟨γ 0 1 * k, had⟩

/-- Simultaneous sign flip `(-1)^t` and congruence `n₁ ≡ n₂ + δ + 12 t (mod 24)` multiply
`s * e(n / 24)` by `e(δ / 24)`. -/
private theorem sign_mul_cexp_eq {s₁ s₂ n₁ n₂ δ t : ℤ}
    (hs : s₁ = (t.negOnePow : ℤ) * s₂)
    (hn : 24 ∣ n₁ - (n₂ + δ + 12 * t)) :
    (s₁ : ℂ) * cexp (2 * π * I * ((n₁ : ℂ) / 24)) =
      cexp (2 * π * I * ((δ : ℂ) / 24)) * ((s₂ : ℂ) * cexp (2 * π * I * ((n₂ : ℂ) / 24))) := by
  obtain ⟨k, hk⟩ := hn
  rcases Int.even_or_odd t with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rw [hs, Int.negOnePow_even _ ⟨u, rfl⟩, Units.val_one, one_mul]
    have hn1 : n₁ = δ + n₂ + 24 * (u + k) := by linarith
    have harg : 2 * π * I * ((n₁ : ℂ) / 24) =
        2 * π * I * ((δ : ℂ) / 24) + 2 * π * I * ((n₂ : ℂ) / 24) +
          ((u + k : ℤ) : ℂ) * (2 * π * I) := by
      rw [hn1]
      push_cast
      ring
    rw [harg, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add]
    ring
  · rw [hs, Int.negOnePow_two_mul_add_one, Units.val_neg, Units.val_one, neg_one_mul, Int.cast_neg]
    have hn1 : n₁ = δ + n₂ + 12 + 24 * (u + k) := by linarith
    have harg : 2 * π * I * ((n₁ : ℂ) / 24) =
        π * I + (2 * π * I * ((δ : ℂ) / 24) + 2 * π * I * ((n₂ : ℂ) / 24)) +
          ((u + k : ℤ) : ℂ) * (2 * π * I) := by
      rw [hn1]
      push_cast
      ring
    rw [harg, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
      Complex.exp_pi_mul_I, Complex.exp_add]
    ring

/-- Modulo `24`, the numerator shift `kroneckerNum (γ * T) - kroneckerNum γ` at `c = 2 k` is `1`
when `k` is even and `1 + 12 * ((d + 1) / 2)` when `k` is odd. -/
private theorem twentyFour_dvd_kroneckerNum_mul_T_of_even (γ : SL(2, ℤ)) {k : ℤ}
    (hk_eq : γ 1 0 = 2 * k) :
    24 ∣ kroneckerNum (γ * T) -
      (kroneckerNum γ + 1 + 12 * if Even k then 0 else (γ 1 1 + 1) / 2) := by
  have h00 : (γ * T) 0 0 = γ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (γ * T) 0 1 = γ 0 0 + γ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (γ * T) 1 0 = γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (γ * T) 1 1 = γ 1 0 + γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rwa [Matrix.det_fin_two] at h
  have hnot_odd : ¬ Odd (γ 1 0) := Int.not_odd_iff_even.mpr ⟨k, by linarith⟩
  obtain ⟨ha_odd, hd_odd⟩ := odd_entry_of_even_c γ ⟨k, by linarith⟩
  have hdvd24 {n : ℤ} (h3 : 3 ∣ n) (h8 : 8 ∣ n) : 24 ∣ n := by
    have hcop38 : IsCoprime (3 : ℤ) 8 := ⟨3, -1, by norm_num⟩
    simpa using hcop38.mul_dvd h3 h8
  rw [kroneckerNum, kroneckerNum, h00, h01, h10, h11, ite_eq_right hnot_odd, ite_eq_right hnot_odd]
  rcases Int.even_or_odd k with hk_even | hk_odd
  · rw [ite_eq_left hk_even, mul_zero, add_zero]
    obtain ⟨u, rfl⟩ := hk_even
    obtain ⟨v, hv⟩ := ha_odd
    have hc4 : γ 1 0 = 4 * u := by linarith
    have hexpr : ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 -
          (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) +
            3 * (γ 1 0 + γ 1 1) - 3 - 3 * γ 1 0 * (γ 1 0 + γ 1 1)) -
        ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 + 1) =
        -(γ 0 0 + 2 * γ 0 1) * (4 * u) * ((4 * u) ^ 2 - 1) + 12 * u - 48 * u ^ 2 := by
      linear_combination -(γ 1 0 ^ 2 - 1) * hdet +
        (-(γ 0 0 + 2 * γ 0 1) * (γ 1 0 ^ 2 + 4 * u * γ 1 0 + 16 * u ^ 2 - 1) +
          3 - 3 * (γ 1 0 + 4 * u)) * hc4
    rw [hexpr]
    refine hdvd24 ?_ ?_
    · obtain ⟨q3, hq3⟩ := Int.three_dvd_mul_sq_sub_one u
      exact ⟨-(γ 0 0 + 2 * γ 0 1) * 4 * (5 * u ^ 3 + q3) + 4 * u - 16 * u ^ 2,
        by linear_combination -4 * (γ 0 0 + 2 * γ 0 1) * hq3⟩
    · rw [hv]
      exact ⟨-((v + γ 0 1) * u * (16 * u ^ 2 - 1)) - 8 * u ^ 3 + 2 * u - 6 * u ^ 2, by ring⟩
  · rw [ite_eq_right (Int.not_even_iff_odd.mpr hk_odd)]
    have hexpr : ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 -
          (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) +
            3 * (γ 1 0 + γ 1 1) - 3 - 3 * γ 1 0 * (γ 1 0 + γ 1 1)) -
        ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
          3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 + 1 + 12 * ((γ 1 1 + 1) / 2)) =
        -(γ 0 0 + 2 * γ 0 1) * (2 * k) * ((2 * k) ^ 2 - 1) + 6 * k - 12 * k ^ 2 -
          12 * ((γ 1 1 + 1) / 2) := by
      linear_combination -(γ 1 0 ^ 2 - 1) * hdet +
        (-(γ 0 0 + 2 * γ 0 1) * (γ 1 0 ^ 2 + 2 * k * γ 1 0 + 4 * k ^ 2 - 1) +
          3 - 3 * (γ 1 0 + 2 * k)) * hk_eq
    rw [hexpr]
    refine hdvd24 ?_ ?_
    · obtain ⟨q3, hq3⟩ := Int.three_dvd_mul_sq_sub_one k
      exact ⟨-(γ 0 0 + 2 * γ 0 1) * (2 * q3 + 2 * k ^ 3) + 2 * k - 4 * k ^ 2 -
          4 * ((γ 1 1 + 1) / 2), by linear_combination -2 * (γ 0 0 + 2 * γ 0 1) * hq3⟩
    · obtain ⟨u, rfl⟩ := hk_odd
      obtain ⟨w, hw⟩ := hd_odd
      have h4d : (4 : ℤ) ∣ γ 1 1 * (γ 0 0 + 2 * γ 0 1 - γ 1 1) := by
        refine ⟨γ 0 1 * (u + w + 1) - w ^ 2 - w, ?_⟩
        have hdet' : γ 0 0 * (2 * w + 1) - γ 0 1 * (2 * (2 * u + 1)) = 1 := by
          rw [← hw, ← hk_eq]; exact hdet
        rw [hw]; linear_combination hdet'
      have hcop4 : IsCoprime (4 : ℤ) (γ 1 1) := by rw [hw]; exact ⟨w ^ 2, 1 - 2 * w, by ring⟩
      obtain ⟨q4, hq4⟩ := hcop4.dvd_of_dvd_mul_left h4d
      have hab : γ 0 0 + 2 * γ 0 1 = γ 1 1 + 4 * q4 := by linarith
      have hdiv : (γ 1 1 + 1) / 2 = w + 1 := by omega
      rw [hab, hdiv, hw]
      exact ⟨-q4 * (2 * u + 1) * (16 * u ^ 2 + 16 * u + 3) +
          w * (-16 * u ^ 3 - 24 * u ^ 2 - 11 * u - 3) +
          (-8 * u ^ 3 - 18 * u ^ 2 - 10 * u - 3), by ring⟩

/-- Right multiplication by `T` multiplies `kroneckerRhs γ` by `exp(π i / 12)` when `0 < c`. -/
private theorem kroneckerRhs_mul_T (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    kroneckerRhs (γ * T) = cexp (π * I / 12) * kroneckerRhs γ := by
  have h00 : (γ * T) 0 0 = γ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (γ * T) 0 1 = γ 0 0 + γ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (γ * T) 1 0 = γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (γ * T) 1 1 = γ 1 0 + γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rwa [Matrix.det_fin_two] at h
  have hexp1 : cexp (2 * π * I * (((1 : ℤ) : ℂ) / 24)) = cexp (π * I / 12) := by
    congr 1; push_cast; ring
  rw [kroneckerRhs, kroneckerRhs, ← hexp1]
  by_cases hodd : Odd (γ 1 0)
  · refine sign_mul_cexp_eq (t := 0) ?_ ?_
    · rw [Int.negOnePow_zero, Units.val_one, one_mul, kroneckerSign, kroneckerSign, h10, h11,
        ite_eq_left hodd, ite_eq_left hodd]
      obtain ⟨c, hc_eq⟩ := Int.eq_ofNat_of_zero_le hc.le
      have hc_odd : Odd c := (Int.odd_natCast c).mp (hc_eq ▸ hodd)
      rw [hc_eq, kroneckerSym_eq_jacobiSym _ hc_odd, kroneckerSym_eq_jacobiSym _ hc_odd]
      exact jacobiSym.mod_left' (by simp)
    · rw [kroneckerNum, kroneckerNum, h00, h01, h10, h11, ite_eq_left hodd, ite_eq_left hodd]
      have hdiff : ((γ 0 0 + (γ 1 0 + γ 1 1)) * γ 1 0 -
            (γ 0 0 + γ 0 1) * (γ 1 0 + γ 1 1) * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) -
          ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 + 1 + 12 * 0) =
          -(γ 0 0 + 2 * γ 0 1) * (γ 1 0 * (γ 1 0 ^ 2 - 1)) := by
        linear_combination -(γ 1 0 ^ 2 - 1) * hdet
      rw [hdiff]
      exact (Int.twentyFour_dvd_mul_sq_sub_one_of_odd hodd).mul_left _
  · obtain ⟨k, hk⟩ := Int.not_odd_iff_even.mp hodd
    have hk_eq : γ 1 0 = 2 * k := by linarith
    obtain ⟨_, hd_odd⟩ := odd_entry_of_even_c γ ⟨k, hk⟩
    refine sign_mul_cexp_eq (t := if Even k then 0 else (γ 1 1 + 1) / 2) ?_
      (twentyFour_dvd_kroneckerNum_mul_T_of_even γ hk_eq)
    rw [kroneckerSign, kroneckerSign, h10, h11, ite_eq_right hodd, ite_eq_right hodd]
    rcases Int.even_or_odd k with hk_even | hk_odd
    · rw [ite_eq_left hk_even, Int.negOnePow_zero, Units.val_one, one_mul]
      obtain ⟨u, rfl⟩ := hk_even
      have hmod4 : γ 1 0 ≡ 0 [ZMOD 4] := Int.modEq_zero_iff_dvd.mpr ⟨u, by linarith⟩
      exact kroneckerSym_mod_right' (.inl hmod4) (by simp)
    · rw [ite_eq_right (Int.not_even_iff_odd.mpr hk_odd), hk_eq]
      exact kroneckerSym_two_mul_add_self_of_odd hk_odd hd_odd

/-- Right multiplication by `Tⁿ` multiplies `kroneckerRhs γ` by `exp(π i n / 12)` when `0 < c`. -/
private theorem kroneckerRhs_mul_T_zpow (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (n : ℤ) :
    kroneckerRhs (γ * T ^ n) = cexp (π * I * n / 12) * kroneckerRhs γ := by
  have h10 (k : ℤ) : (γ * T ^ k) 1 0 = γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  induction n using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have hc' : 0 < (γ * T ^ (m : ℤ)) 1 0 := by rw [h10]; exact hc
    rw [zpow_add_one, ← mul_assoc, kroneckerRhs_mul_T _ hc', ih, ← mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  | pred m ih =>
    have hstep : (γ * T ^ (-(m : ℤ) - 1)) * T = γ * T ^ (-(m : ℤ)) := by
      rw [mul_assoc, ← zpow_add_one]; simp
    have hc' : 0 < (γ * T ^ (-(m : ℤ) - 1)) 1 0 := by rw [h10]; exact hc
    have hT := kroneckerRhs_mul_T (γ * T ^ (-(m : ℤ) - 1)) hc'
    rw [hstep, ih] at hT
    have hmul : kroneckerRhs (γ * T ^ (-(m : ℤ) - 1)) =
        cexp (-(π * I / 12)) * (cexp (π * I * (-(m : ℤ) : ℤ) / 12) * kroneckerRhs γ) := by
      rw [hT, ← mul_assoc, ← Complex.exp_add]; simp
    rw [hmul, ← mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring

/-- Right multiplication by `S` multiplies `kroneckerRhs γ` by `exp(-π i / 4)` when `0 < c` and
`0 < d`. -/
private theorem kroneckerRhs_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    kroneckerRhs (γ * S) = cexp (-(π * I / 4)) * kroneckerRhs γ := by
  have h00 : (γ * S) 0 0 = γ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (γ * S) 0 1 = -γ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (γ * S) 1 0 = γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (γ * S) 1 1 = -γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rwa [Matrix.det_fin_two] at h
  have hexp3 : cexp (2 * π * I * (((-3 : ℤ) : ℂ) / 24)) = cexp (-(π * I / 4)) := by
    congr 1; push_cast; ring
  rw [kroneckerRhs, kroneckerRhs, ← hexp3]
  by_cases hodd_c : Odd (γ 1 0)
  · by_cases hodd_d : Odd (γ 1 1)
    · -- Both `c` and `d` are odd: quadratic reciprocity + `(-1 / d)` match the numerator flip.
      obtain ⟨c, hc_eq⟩ := Int.eq_ofNat_of_zero_le hc.le
      obtain ⟨d, hd_eq⟩ := Int.eq_ofNat_of_zero_le hd.le
      have hc_odd : Odd c := (Int.odd_natCast c).mp (hc_eq ▸ hodd_c)
      have hd_odd : Odd d := (Int.odd_natCast d).mp (hd_eq ▸ hodd_d)
      refine sign_mul_cexp_eq (t := -(((c / 2 + 1) * (d / 2) : ℕ) : ℤ)) ?_ ?_
      · have hexp : d / 2 + c / 2 * (d / 2) = (c / 2 + 1) * (d / 2) := by ring
        rw [kroneckerSign, kroneckerSign, h10, h11, ite_eq_left hodd_d, ite_eq_left hodd_c,
          hc_eq, hd_eq, kroneckerSym_eq_jacobiSym _ hd_odd, kroneckerSym_eq_jacobiSym _ hc_odd,
          neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hd_odd,
          χ₄_eq_neg_one_pow (Nat.odd_iff.mp hd_odd), jacobiSym.quadratic_reciprocity hc_odd hd_odd,
          ← mul_assoc, ← pow_add, Int.negOnePow_neg, hexp, ← Int.coe_negOnePow_natCast]
      · rw [kroneckerNum, kroneckerNum, h00, h01, h10, h11, ite_eq_left hodd_d, ite_eq_left hodd_c]
        have hc2 : (c : ℤ) = 2 * ((c / 2 : ℕ) : ℤ) + 1 := by
          have := Nat.div_add_mod c 2; have := Nat.odd_iff.mp hc_odd; omega
        have hd2 : (d : ℤ) = 2 * ((d / 2 : ℕ) : ℤ) + 1 := by
          have := Nat.div_add_mod d 2; have := Nat.odd_iff.mp hd_odd; omega
        refine ⟨0, ?_⟩
        rw [mul_zero]
        rw [hc_eq, hd_eq] at hdet ⊢
        push_cast at hc2 hd2 ⊢
        linear_combination -(c : ℤ) * (d : ℤ) * hdet -
          3 * ((d : ℤ) - 1) * hc2 - 3 * (2 * ((c : ℤ) / 2) + 2) * hd2
    · -- `c` is odd and `d` is even (`t = 0`).
      refine sign_mul_cexp_eq (t := 0) ?_ ?_
      · rw [Int.negOnePow_zero, Units.val_one, one_mul, kroneckerSign, kroneckerSign, h10, h11,
          ite_eq_right hodd_d, ite_eq_left hodd_c, kroneckerSym_of_odd _ hodd_c.neg,
          kroneckerSym_of_odd _ hodd_c, Int.natAbs_neg,
          ite_eq_right (fun h ↦ lt_asymm hd h.1), ite_eq_right (fun h ↦ lt_asymm hd h.1)]
      · rw [kroneckerNum, kroneckerNum, h00, h01, h10, h11, ite_eq_right hodd_d,
          ite_eq_left hodd_c]
        exact ⟨0, by linear_combination -γ 1 0 * γ 1 1 * hdet⟩
  · -- `c` is even, so `d` is odd (`t = -(d / 2)`).
    obtain ⟨_, hodd_d⟩ := odd_entry_of_even_c γ (Int.not_odd_iff_even.mp hodd_c)
    obtain ⟨d, hd_eq⟩ := Int.eq_ofNat_of_zero_le hd.le
    have hd_odd : Odd d := (Int.odd_natCast d).mp (hd_eq ▸ hodd_d)
    refine sign_mul_cexp_eq (t := -(((d / 2 : ℕ) : ℤ))) ?_ ?_
    · rw [kroneckerSign, kroneckerSign, h10, h11, ite_eq_left hodd_d, ite_eq_right hodd_c,
        neg_eq_neg_one_mul (γ 1 0), kroneckerSym_mul_left (by norm_num) hc.ne',
        hd_eq, kroneckerSym_eq_jacobiSym (-1) hd_odd, jacobiSym.at_neg_one hd_odd,
        χ₄_eq_neg_one_pow (Nat.odd_iff.mp hd_odd), Int.negOnePow_neg, ← Int.coe_negOnePow_natCast]
    · rw [kroneckerNum, kroneckerNum, h00, h01, h10, h11, ite_eq_left hodd_d, ite_eq_right hodd_c]
      have hd2 : (d : ℤ) = 2 * ((d / 2 : ℕ) : ℤ) + 1 := by
        have := Nat.div_add_mod d 2; have := Nat.odd_iff.mp hd_odd; omega
      refine ⟨0, ?_⟩
      rw [mul_zero]
      rw [hd_eq] at hdet ⊢
      linear_combination -γ 1 0 * (d : ℤ) * hdet - 6 * hd2

/-! ### Main theorems -/

/-- Strong induction on `c` proving `etaMultiplier γ = kroneckerRhs γ` for `0 < c`. -/
private theorem etaMultiplier_eq_kroneckerRhs_of_natCast :
    ∀ c : ℕ, 0 < c → ∀ γ : SL(2, ℤ), γ 1 0 = c → etaMultiplier γ = kroneckerRhs γ := by
  intro c
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    intro hc γ hγc
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hc) with rfl | hc_gt_one
    · simp only [Nat.cast_one] at hγc
      rw [etaMultiplier_of_c_eq_one γ hγc, kroneckerRhs, kroneckerSign, kroneckerNum, hγc,
        ite_eq_left odd_one, ite_eq_left odd_one, kroneckerSym_one_right]
      simp only [Int.cast_one, one_mul, one_pow, sub_self, mul_zero]
      congr 1; push_cast; ring
    · -- Reduce `d = γ 1 1` modulo `c` via `γ₁ = γ * T ^ (-q)`, then invert via `S`.
      have hcZ_pos : (0 : ℤ) < c := Nat.cast_pos.mpr hc
      have hcZ_gt : (1 : ℤ) < c := by exact_mod_cast hc_gt_one
      let q : ℤ := γ 1 1 / (c : ℤ)
      set γ₁ : SL(2, ℤ) := γ * T ^ (-q) with hγ₁_def
      have hγ_eq : γ = γ₁ * T ^ q := by simp [hγ₁_def, mul_assoc]
      have hγ₁_10 : γ₁ 1 0 = (c : ℤ) := by
        simp [hγ₁_def, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply,
          Fin.sum_univ_two, hγc]
      rw [hγ_eq, etaMultiplier_mul_T_zpow, kroneckerRhs_mul_T_zpow γ₁ (hγ₁_10 ▸ hcZ_pos) q]
      congr 1
      have hγ₁_11 : γ₁ 1 1 = γ 1 1 % (c : ℤ) := by
        have hmul : (γ * T ^ (-q)) 1 1 = γ 1 0 * (-q) + γ 1 1 := by
          simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
        rw [hγ₁_def, hmul, hγc, Int.emod_def]
        ring
      have hr_nonneg : 0 ≤ γ₁ 1 1 := hγ₁_11 ▸ Int.emod_nonneg _ hcZ_pos.ne'
      have hr_lt_Z : γ₁ 1 1 < c := hγ₁_11 ▸ Int.emod_lt_of_pos _ hcZ_pos
      have hdet₁ : γ₁ 0 0 * γ₁ 1 1 - γ₁ 0 1 * (c : ℤ) = 1 := by
        have h := γ₁.det_coe; rwa [Matrix.det_fin_two, hγ₁_10] at h
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
      rw [etaMultiplier_mul_S γ₁ hr_pos, kroneckerRhs_mul_S γ₁ (hγ₁_10 ▸ hcZ_pos) hr_pos] at hih
      exact mul_left_cancel₀ (Complex.exp_ne_zero _) hih

/-- **The Kronecker-symbol formula for the eta multiplier** (Strömberg, Remark 2.5, eq. (2.5)):
unified form for `γ = (a b; c d) ∈ SL(2, ℤ)` with `0 < c`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        kroneckerSym (γ 1 1) (γ 1 0) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) / 24))
      else
        kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
              3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) / 24)) := by
  obtain ⟨c, hc_eq⟩ := Int.eq_ofNat_of_zero_le hc.le
  rw [etaMultiplier_eq_kroneckerRhs_of_natCast c (Nat.cast_pos.mp (hc_eq ▸ hc)) γ hc_eq,
    kroneckerRhs, kroneckerSign, kroneckerNum]
  split_ifs <;> rfl

/-- **The Kronecker-symbol formula for the eta multiplier at odd `c > 0`** (Strömberg,
Remark 2.5): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `0 < c` and `Odd c`,
`ε(γ) = (d / c) exp(2π i ((a + d) c - b d (c² - 1) - 3 c) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ =
      kroneckerSym (γ 1 1) (γ 1 0) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) / 24)) := by
  rw [etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_pos γ hc, ite_eq_left hodd]

/-- **The Kronecker-symbol formula for the eta multiplier at even `c > 0`** (Strömberg,
Remark 2.5): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `0 < c` and `Even c`,
`ε(γ) = (c / d) exp(2π i ((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_even (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (heven : Even (γ 1 0)) :
    etaMultiplier γ =
      kroneckerSym (γ 1 0) (γ 1 1) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) / 24)) := by
  rw [etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_pos γ hc,
    ite_eq_right (Int.not_odd_iff_even.mpr heven)]

/-! ### Comparison with the Dedekind sum -/

/-- Equating the Kronecker-symbol and Dedekind-sum formulas for `γ ∈ SL(2, ℤ)` at odd `c > 0`. -/
theorem kroneckerSym_mul_cexp_eq_cexp_dedekindSum_of_odd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    (kroneckerSym (γ 1 1) (γ 1 0) : ℂ) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) / 24)) =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) :=
  (etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd γ hc hodd).symm.trans (etaMultiplier_of_c_pos γ hc)

/-- Equating the Kronecker-symbol and Dedekind-sum formulas for `γ ∈ SL(2, ℤ)` at even `c > 0`. -/
theorem kroneckerSym_mul_cexp_eq_cexp_dedekindSum_of_even (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (heven : Even (γ 1 0)) :
    (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        cexp (2 * π * I *
          (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) / 24)) =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) :=
  (etaMultiplier_eq_kroneckerSym_mul_cexp_of_even γ hc heven).symm.trans
    (etaMultiplier_of_c_pos γ hc)

end TauCeti.ModularForm
