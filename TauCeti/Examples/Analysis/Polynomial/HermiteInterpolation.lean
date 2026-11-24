/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.FinCases
import TauCeti.Analysis.Polynomial.HermiteInterpolation
import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.RingTheory.LaurentSeries.LocalField

/-!
# Examples of ultrametric Hermite interpolation bounds

Concrete evaluations and sharpness witnesses for the ultrametric Hermite interpolation bounds in
`TauCeti.Analysis.Polynomial.HermiteInterpolation`:

* Over `ℚ_[3]` with single node `0`, `S = 3`, and `s = 2`, the ordinary-derivative Hermite witness
  is `(1 / 2) X ^ 2`; both its maximum coefficient norm and the bound
  `‖((2! : ℕ) : ℚ_[3])⁻¹‖ * (1 ^ 3)⁻¹` equal `1`.
* Over `ℚ_[2]` with the same data, `‖((2! : ℕ) : ℚ_[2])⁻¹‖ = 2`, and every polynomial `W` with
  `(derivative^[2] W).eval 0 = 1` satisfies `‖W.coeff 2‖ = 2`, showing the factorial denominator
  factor is sharp across all witnesses.
* Over the characteristic-`2` ultrametric normed field `LaurentSeries (ZMod 2)`, no polynomial `W`
  satisfies `(derivative^[2] W).eval 0 = 1` (while
  `‖((2! : ℕ) : LaurentSeries (ZMod 2))⁻¹‖ = 0`), whereas the Hasse-derivative basis polynomial
  `hermiteBasis _ ![3] ⟨0, 2⟩ = X ^ 2` exists and has coefficient norms at most `1`.
* Over `ℚ_[3]` at the two close nodes `![0, 3]` (`ϱ = 1 / 3`) with multiplicities `![2, 2]` and
  jet `(0, 0)`, `Polynomial.norm_coeff_hermiteBasis_le_inv_pow_sub` gives the bound
  `((1 / 3) ^ 3)⁻¹ = 27`, which is attained by the leading coefficient `(2 / 27) X ^ 3` of
  `(X - 3) ^ 2 * (1 / 9 + (2 / 27) X)`.
* At `![0, 1, 10]` in `ℚ_[3]` with multiplicities `![1, 1, 1]` and base node `0`,
  `Polynomial.norm_coeff_hermiteBasis_le_inv_prod_mul_inv_pow` uses only the distances from `0`
  (both equal to `1`) and bounds all coefficients by `1` despite `‖(1 : ℚ_[3]) - 10‖ = 1 / 9`.
* Dropping `[IsUltrametricDist K]` (over `ℝ` at node `1`, `m = ![3]`, `s = 2`) or `∀ i, ‖a i‖ ≤ 1`
  (over `ℚ_[3]` at `![3⁻¹, 3⁻¹ + 1]`, `m = ![1, 1]`) breaks the unit bound on `hermiteBasis`.
-/

namespace TauCeti.HermiteInterpolationExample

open Finset Polynomial
open scoped Nat

/-- Over `ℚ_[3]` at `σ = ![0]` with `ϱ = 1`, `S = 3`, `s = 2`,
`Polynomial.exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist` produces a polynomial whose
derivatives below order `3` at `0` are `0, 0, 1` and whose coefficients all have `3`-adic norm at
most `1`. -/
example : ∃ W : ℚ_[3][X],
    (∀ j < 3, (derivative^[j] W).eval 0 = if j = 2 then 1 else 0) ∧
      ∀ n, ‖W.coeff n‖ ≤ 1 := by
  obtain ⟨W, hderiv, hcoeff⟩ :=
    exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist (![0] : Fin 1 → ℚ_[3])
      (by simp) zero_lt_one le_rfl (fun i j hij ↦ absurd (Subsingleton.elim i j) hij)
      3 0 (s := 2) (by decide)
  refine ⟨W, fun j hj ↦ by simpa using hderiv 0 j hj, fun n ↦ (hcoeff n).trans_eq ?_⟩
  have h2 : ‖(2 : ℚ_[3])‖ = 1 := mod_cast Padic.norm_natCast_p_sub_one (p := 3)
  simp [Nat.factorial_two, h2]

/-- Over `ℚ_[3]`, the explicit scaled Hermite basis polynomial at `σ = ![0]`, `S = 3`, `s = 2` is
`C 2⁻¹ * X ^ 2`, attaining coefficient norm `1` in degree `2`. -/
example :
    let ha : Pairwise fun i j : Fin 1 ↦
      IsUnit ((![0] : Fin 1 → ℚ_[3]) i - (![0] : Fin 1 → ℚ_[3]) j) :=
      fun i j hij ↦ absurd (Subsingleton.elim i j) hij
    let W : ℚ_[3][X] := (2 : ℚ_[3])⁻¹ • (hermiteBasis ha ![3] ⟨0, ⟨2, by decide⟩⟩ : ℚ_[3][X])
    W = C (2 : ℚ_[3])⁻¹ * X ^ 2 ∧ ‖W.coeff 2‖ = 1 := by
  intro ha W
  have h2 : ‖(2 : ℚ_[3])‖ = 1 := mod_cast Padic.norm_natCast_p_sub_one (p := 3)
  have hW : W = C (2 : ℚ_[3])⁻¹ * X ^ 2 := by
    simp [W, hermiteBasis_of_subsingleton, Algebra.smul_def]
  refine ⟨hW, ?_⟩
  simp [hW, h2]

/-- Over `ℚ_[2]` at `σ = ![0]` with `ϱ = 1`, `S = 3`, `s = 2`, the bound
`‖((2! : ℕ) : ℚ_[2])⁻¹‖ * (1 ^ 3)⁻¹` equals `2`, and every polynomial `W` with
`(derivative^[2] W).eval 0 = 1` satisfies `‖W.coeff 2‖ = 2`. -/
example :
    (∃ W : ℚ_[2][X],
      (∀ j < 3, (derivative^[j] W).eval 0 = if j = 2 then 1 else 0) ∧
        ∀ n, ‖W.coeff n‖ ≤ 2) ∧
    (∀ W : ℚ_[2][X], (derivative^[2] W).eval 0 = 1 → ‖W.coeff 2‖ = 2) := by
  have h2 : ‖((2 : ℕ) : ℚ_[2])‖ = 2⁻¹ := Padic.norm_p (p := 2)
  refine ⟨?_, fun W hW ↦ ?_⟩
  · obtain ⟨W, hderiv, hcoeff⟩ :=
      exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist (![0] : Fin 1 → ℚ_[2])
        (by simp) zero_lt_one le_rfl (fun i j hij ↦ absurd (Subsingleton.elim i j) hij)
        3 0 (s := 2) (by decide)
    refine ⟨W, fun j hj ↦ by simpa using hderiv 0 j hj, fun n ↦ (hcoeff n).trans_eq ?_⟩
    simpa [Nat.factorial_two] using congrArg Inv.inv h2
  · rw [← factorial_smul_hasseDeriv] at hW
    have hc : (2 : ℚ_[2]) * W.coeff 2 = 1 := by
      simpa [Nat.factorial_two, ← coeff_zero_eq_eval_zero, hasseDeriv_coeff] using hW
    have hnorm := congrArg norm hc
    have h2' : ‖(2 : ℚ_[2])‖ = 2⁻¹ := mod_cast h2
    rw [norm_mul, norm_one, h2'] at hnorm
    linarith

/-- `[CharZero K]` is essential in `exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist`:
over the characteristic-`2` ultrametric normed field `LaurentSeries (ZMod 2)`, no polynomial `W`
satisfies `(derivative^[2] W).eval 0 = 1` and `‖((2! : ℕ) : LaurentSeries (ZMod 2))⁻¹‖ = 0`,
whereas the Hasse-jet Hermite basis polynomial `hermiteBasis _ ![3] ⟨0, 2⟩ = X ^ 2` exists and has
coefficient norms at most `1`. -/
example :
    letI := TauCeti.normalizedNormedField (LaurentSeries (ZMod 2))
    (¬ ∃ W : (LaurentSeries (ZMod 2))[X], (derivative^[2] W).eval 0 = 1) ∧
    ‖(((2! : ℕ) : LaurentSeries (ZMod 2))⁻¹)‖ = 0 ∧
    ∀ n, ‖(hermiteBasis (a := (![0] : Fin 1 → LaurentSeries (ZMod 2)))
      (fun i j hij ↦ absurd (Subsingleton.elim i j) hij) ![3]
      ⟨0, ⟨2, by decide⟩⟩ : (LaurentSeries (ZMod 2))[X]).coeff n‖ ≤ 1 := by
  let _ := TauCeti.normalizedNormedField (LaurentSeries (ZMod 2))
  have _ : IsUltrametricDist (LaurentSeries (ZMod 2)) :=
    TauCeti.normalizedNormedField_isUltrametricDist (LaurentSeries (ZMod 2))
  have hchar : ((2! : ℕ) : LaurentSeries (ZMod 2)) = 0 := by
    rw [← map_natCast (algebraMap (ZMod 2) (LaurentSeries (ZMod 2))), Nat.factorial_two,
      ZMod.natCast_self, map_zero]
  refine ⟨?_, ?_, fun n ↦ ?_⟩
  · rintro ⟨W, hW⟩
    rw [← factorial_smul_hasseDeriv, ← Nat.cast_smul_eq_nsmul (LaurentSeries (ZMod 2)), hchar,
      zero_smul] at hW
    simp at hW
  · rw [hchar, inv_zero, norm_zero]
  · simpa using norm_coeff_hermiteBasis_le (a := (![0] : Fin 1 → LaurentSeries (ZMod 2)))
      (fun i j hij ↦ absurd (Subsingleton.elim i j) hij) ![3] ⟨0, ⟨2, by decide⟩⟩
      (by simp) zero_lt_one le_rfl (fun i hi ↦ absurd (Subsingleton.elim i 0) hi) n

/-- **Sharpness of `norm_coeff_hermiteBasis_le_inv_pow_sub` on close `3`-adic nodes.** At
`a = ![0, 3]` in `ℚ_[3]` (`ϱ = 1 / 3`) with multiplicities `![2, 2]` and jet `(0, 0)`,
`hermiteBasis ha ![2, 2] ⟨0, 0⟩` equals `(2 / 27) X ^ 3 - (1 / 3) X ^ 2 + 1`, every coefficient
has norm at most `((1 / 3) ^ 3)⁻¹ = 27`, and its degree-`3` coefficient attains norm `27`. -/
example :
    let a : Fin 2 → ℚ_[3] := ![0, 3]
    have ha : Pairwise fun i j ↦ IsUnit (a i - a j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [a] at hij ⊢
    let b : ℚ_[3][X] := hermiteBasis ha ![2, 2] ⟨0, ⟨0, by decide⟩⟩
    b = C (2 / 27) * X ^ 3 - C 3⁻¹ * X ^ 2 + 1 ∧
      (∀ n, ‖b.coeff n‖ ≤ 27) ∧ ‖b.coeff 3‖ = 27 := by
  intro a ha b
  have herase : (univ.erase (0 : Fin 2)) = {1} := by decide
  have hb_eq : b = C (2 / 27) * X ^ 3 - C 3⁻¹ * X ^ 2 + 1 := by
    set h : ℚ_[3][X] := C 9⁻¹ + C (2 / 27) * X
    have hdeg : h.degree < ((![2, 2] (0 : Fin 2) - 0 : ℕ) : WithBot ℕ) := by
      rw [degree_lt_iff_coeff_zero]
      intro k hk
      rcases k with _ | _ | k
      · simp at hk
      · simp at hk
      · simp [h]
    have hmul : (X - C (3 : ℚ_[3])) ^ 2 * h = C (2 / 27) * X ^ 3 - C 3⁻¹ * X ^ 2 + 1 := by
      have hc :
          (X - C (3 : ℚ_[3])) ^ 2 * h =
            C (2 / 27) * X ^ 3 + C (9⁻¹ - 6 * (2 / 27)) * X ^ 2 +
              C (9 * (2 / 27) - 6 * 9⁻¹) * X + C (9 * 9⁻¹) := by
        simp only [h, map_sub, map_mul, map_ofNat]
        ring
      rw [hc]
      norm_num
      ring
    have htaylor :
        taylor (a 0) (∏ i ∈ univ.erase 0, (X - C (a i)) ^ (![2, 2] i)) * h =
          C (2 / 27) * X ^ 3 - C 3⁻¹ * X ^ 2 + 1 := by
      simpa [herase, a] using hmul
    have hdvd : X ^ (![2, 2] (0 : Fin 2) - 0) ∣
        taylor (a 0) (∏ i ∈ univ.erase 0, (X - C (a i)) ^ (![2, 2] i)) * h - 1 := by
      rw [htaylor, Matrix.cons_val_zero, Nat.sub_zero]
      exact ⟨C (2 / 27) * X - C 3⁻¹, by ring⟩
    dsimp only [b]
    rw [hermiteBasis_eq_of_dvd_taylor_mul_sub_one ha ![2, 2] ⟨0, ⟨0, by decide⟩⟩ hdeg hdvd]
    simpa [herase, a] using hmul
  have h3 : ‖((3 : ℕ) : ℚ_[3])‖ = 3⁻¹ := Padic.norm_p (p := 3)
  have ha1 (i : Fin 2) : ‖a i‖ ≤ 1 := by
    fin_cases i
    · simp [a]
    · simpa [a] using h3.le.trans (by norm_num)
  have hsep (i : Fin 2) (hi : i ≠ 0) : (1 / 3 : ℝ) ≤ ‖a 0 - a i‖ := by
    fin_cases i
    · exact absurd rfl hi
    · simpa [a] using h3.ge
  refine ⟨hb_eq, fun n ↦ ?_, ?_⟩
  · have hb := norm_coeff_hermiteBasis_le_inv_pow_sub ha ![2, 2] ⟨0, ⟨0, by decide⟩⟩
      ha1 (by norm_num) (by norm_num) hsep n
    refine hb.trans_eq ?_
    norm_num [Fin.sum_univ_two]
  · have hc3 : b.coeff 3 = (2 : ℚ_[3]) / 27 := by
      rw [hb_eq]
      simp [coeff_X_pow, coeff_one]
    have h2 : ‖(2 : ℚ_[3])‖ = 1 := mod_cast Padic.norm_natCast_p_sub_one (p := 3)
    have h27 : (27 : ℚ_[3]) = ((3 : ℕ) : ℚ_[3]) ^ 3 := by norm_num
    rw [hc3, norm_div, h2, h27, norm_pow, h3]
    norm_num

/-- **Local-separation advantage on unevenly spaced nodes.** At `a = ![0, 1, 10]` in `ℚ_[3]` with
multiplicities `![1, 1, 1]` and base node `0`, the nodes `1` and `10` have distance `1 / 9`, yet
`Polynomial.norm_coeff_hermiteBasis_le_inv_prod_mul_inv_pow` bounds all coefficients at node `0`
by `1` because both `1` and `10` have distance `1` from `0`. -/
example :
    let a : Fin 3 → ℚ_[3] := ![0, 1, 10]
    have ha : Pairwise fun i j ↦ IsUnit (a i - a j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [a] at hij ⊢ <;> norm_num
    ‖a 1 - a 2‖ = 1 / 9 ∧
      ∀ n, ‖(hermiteBasis ha ![1, 1, 1] ⟨0, ⟨0, by decide⟩⟩ : ℚ_[3][X]).coeff n‖ ≤ 1 := by
  intro a ha
  have h3 : ‖((3 : ℕ) : ℚ_[3])‖ = 3⁻¹ := Padic.norm_p (p := 3)
  have h9 : ‖((3 : ℕ) : ℚ_[3]) ^ 2‖ = 1 / 9 := by rw [norm_pow, h3]; norm_num
  have h10 : ‖(10 : ℚ_[3])‖ = 1 :=
    mod_cast (Padic.norm_natCast_eq_one_iff (p := 3) (n := 10)).2 (by decide)
  refine ⟨?_, fun n ↦ ?_⟩
  · have hdiff : a 1 - a 2 = -(((3 : ℕ) : ℚ_[3]) ^ 2) := by simp [a]; norm_num
    rw [hdiff, norm_neg, h9]
  · have ha1 (i : Fin 3) : ‖a i‖ ≤ 1 := by
      fin_cases i <;> simp [a, h10]
    have hsep (i : Fin 3) (hi : i ≠ 0) : (1 : ℝ) ≤ ‖a 0 - a i‖ := by
      fin_cases i
      · exact absurd rfl hi
      · simp [a]
      · simp [a, h10]
    have herase : (univ.erase (0 : Fin 3)) = {1, 2} := by decide
    have hb := norm_coeff_hermiteBasis_le_inv_prod_mul_inv_pow ha ![1, 1, 1] ⟨0, ⟨0, by decide⟩⟩
      ha1 zero_lt_one le_rfl hsep n
    refine hb.trans_eq ?_
    simp [herase, a, h10]

/-- Without `[IsUltrametricDist K]`, the unit-ball bound `norm_coeff_hermiteBasis_le` fails over
`ℝ`: at the single node `1` (`‖(1 : ℝ)‖ ≤ 1`) with `m = ![3]` and `s = 2`, the Hermite basis
polynomial `(X - 1) ^ 2` has linear coefficient `-2` of archimedean norm `2 > 1`. -/
example :
    let ha : Pairwise fun i j : Fin 1 ↦ IsUnit ((![1] : Fin 1 → ℝ) i - (![1] : Fin 1 → ℝ) j) :=
      fun i j hij ↦ absurd (Subsingleton.elim i j) hij
    ‖(![1] : Fin 1 → ℝ) 0‖ ≤ 1 ∧
      ‖(hermiteBasis ha ![3] ⟨0, ⟨2, by decide⟩⟩ : ℝ[X]).coeff 1‖ = 2 := by
  intro ha
  refine ⟨by simp, ?_⟩
  rw [hermiteBasis_of_subsingleton]
  simp [sq, sub_mul, mul_sub, coeff_X, coeff_one]
  norm_num

/-- Without the unit-ball hypothesis `∀ i, ‖a i‖ ≤ 1`, `norm_coeff_hermiteBasis_le` fails over
`ℚ_[3]`: the nodes `![3⁻¹, 3⁻¹ + 1]` have separation `‖a 0 - a 1‖ = 1`, yet the degree-`< 2`
Lagrange basis polynomial `C (3⁻¹ + 1) - X` at node `0` has constant term of `3`-adic norm
`3 > 1`. -/
example :
    let a : Fin 2 → ℚ_[3] := ![3⁻¹, 3⁻¹ + 1]
    have ha : Pairwise fun i j ↦ IsUnit (a i - a j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [a] at hij ⊢
    ‖a 0 - a 1‖ = 1 ∧
      ‖(hermiteBasis ha ![1, 1] ⟨0, ⟨0, by decide⟩⟩ : ℚ_[3][X]).coeff 0‖ = 3 := by
  intro a ha
  have h3 : ‖(3 : ℚ_[3])⁻¹‖ = 3 := by
    rw [norm_inv]
    simpa using congrArg Inv.inv (Padic.norm_p (p := 3))
  refine ⟨by simp [a], ?_⟩
  have hv (i : Fin 2) (hi : i ≠ 0) : (a 0 - a i) * (-1 : ℚ_[3]) = 1 := by
    fin_cases i
    · exact absurd rfl hi
    · simp [a]
  have herase : (univ.erase (0 : Fin 2)) = {1} := by decide
  have hc0 : ‖(hermiteBasis ha ![1, 1] ⟨0, ⟨0, by decide⟩⟩ : ℚ_[3][X]).coeff 0‖ =
      ‖(3 : ℚ_[3])⁻¹ + 1‖ := by
    rw [hermiteBasis_eq_prod_mul_pow_mul_taylor ha ![1, 1] ⟨0, ⟨0, by decide⟩⟩ hv]
    simp [herase, a, PowerSeries.trunc_one_left]
  rw [hc0, Padic.add_eq_max_of_ne (by rw [h3, norm_one]; norm_num), h3, norm_one]
  norm_num

end TauCeti.HermiteInterpolationExample
