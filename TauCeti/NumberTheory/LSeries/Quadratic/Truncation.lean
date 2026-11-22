/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import TauCeti.NumberTheory.ArithmeticFunction.Zeta
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.DirichletEulerProduct
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization

/-!
# Truncating `L(1, χ_D)` for every nonsquare discriminant

For a discriminant `D ≡ 0, 1 (mod 4)` that is not a square, the Kronecker character
`χ_D = (D / ·)` of modulus `|D|` is a nontrivial quadratic Dirichlet character, primitive only
when `D` is fundamental. Writing `D = f² D₀` with `D₀` fundamental, `χ_D` is induced from the
primitive character `χ_{D₀}` of conductor `|D₀|`, so the Pólya–Vinogradov inequality for
imprimitive characters bounds its partial sums by `2 ^ ω f * √|D₀| * (1 + log |D₀|)`. Since
`2 ^ ω f ≤ f`, this gives the bound `√|D| * (1 + log |D|)`, uniformly over all discriminants and
with no dependence on the factorization of `D`.

Abel summation then truncates `L(1, χ_D)`: the partial sum `∑ n ≤ K, χ_D(n) / n` is within
`2 √|D| (1 + log |D|) / (K + 1)` of `L(1, χ_D)`. Summed over discriminants, these are the
truncation errors in the evaluation of the mean value of `L(1, χ_D)` over all quadratic orders,
which, through the class number formula for quadratic orders, gives Siegel's mean value of class
numbers weighted by regulators.

## Main results

* `TauCeti.norm_sum_Icc_kroneckerChar_le`: `‖∑ n ∈ Icc 1 K, χ_D n‖ ≤ √|D| * (1 + log |D|)`.
* `TauCeti.norm_LFunction_kroneckerChar_one_sub_sum_Icc_le`: the partial sum of
  `∑ χ_D(n) / n` up to `K` is within `2 √|D| (1 + log |D|) / (K + 1)` of `L(1, χ_D)`.

## References

* C. L. Siegel, *The average measure of quadratic forms with given determinant and signature*,
  Ann. of Math. (2) 45 (1944), 667–685.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Graduate Texts in Mathematics 74,
  Springer, 2000, Chapter 23.
-/

public section

open Finset DirichletCharacter
open scoped ArithmeticFunction.omega

namespace TauCeti

variable {D : ℤ}

/-- **Pólya–Vinogradov for Kronecker characters.** For a nonsquare discriminant
`D ≡ 0, 1 (mod 4)`, every partial sum `∑ n ∈ Icc 1 K, χ_D n` of the Kronecker character
`χ_D = (D / ·)` has norm at most `√|D| * (1 + log |D|)`, whether or not `χ_D` is primitive. -/
theorem norm_sum_Icc_kroneckerChar_le (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD₀ : D ≠ 0)
    (hsq : ¬ IsSquare D) (K : ℕ) :
    ‖∑ n ∈ Icc 1 K, kroneckerChar ℂ D hD hD₀ n‖ ≤
      Real.sqrt D.natAbs * (1 + Real.log D.natAbs) := by
  -- Write `D = f² D₀` with `D₀` fundamental, so that `χ_D` is induced from `χ_{D₀}`.
  obtain ⟨f, D₀, hfund, rfl⟩ :=
    Int.exists_isFundamentalDiscr_eq_sq_mul (by unfold Int.ModEq at hD; omega) hD₀
  have hf : (f : ℤ) ≠ 0 := by
    rintro h
    simp [h] at hD₀
  have hD₀' : D₀ ≡ 0 [ZMOD 4] ∨ D₀ ≡ 1 [ZMOD 4] := by
    have := hfund.emod_four_eq_zero_or_one
    unfold Int.ModEq
    omega
  have := hfund.neZero_natAbs
  rw [← changeLevel_kroneckerChar_sq_mul hD₀' hfund.ne_zero hf]
  have hprim : (kroneckerChar ℂ D₀ hD₀' hfund.ne_zero).IsPrimitive := by
    rw [← Multiquadratic.fundamentalDiscriminantCharCast_eq_kroneckerChar hfund]
    exact Multiquadratic.isPrimitive_fundamentalDiscriminantCharCast hfund
  have hne : kroneckerChar ℂ D₀ hD₀' hfund.ne_zero ≠ 1 := by
    rw [Ne, kroneckerChar_eq_one_iff_isSquare]
    exact fun h ↦ hsq ((IsSquare.sq (f : ℤ)).mul h)
  have hN : 0 < D₀.natAbs := Int.natAbs_pos.mpr hfund.ne_zero
  have hM : ((f : ℤ) ^ 2 * D₀).natAbs = f ^ 2 * D₀.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  refine (norm_sum_Icc_changeLevel_le _ hprim hne _ K).trans ?_
  rw [hM, Nat.mul_div_cancel _ hN, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
    Nat.primeFactors_pow f two_ne_zero,
    ← ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  -- `2 ^ ω f ≤ f`, `log |D₀| ≤ log |D|` and `f √|D₀| = √|D|`.
  have : 0 ≤ 1 + Real.log D₀.natAbs := by
    have hNr : (1 : ℝ) ≤ D₀.natAbs := by exact_mod_cast hN
    linarith [Real.log_nonneg hNr]
  calc (2 : ℝ) ^ ω f * (Real.sqrt D₀.natAbs * (1 + Real.log D₀.natAbs))
      ≤ f * (Real.sqrt D₀.natAbs * (1 + Real.log ((f ^ 2 * D₀.natAbs : ℕ) : ℝ))) := by
        gcongr
        · exact_mod_cast ArithmeticFunction.two_pow_cardDistinctFactors_le (by exact_mod_cast hf)
        · exact Nat.cast_le.mpr
            (Nat.le_mul_of_pos_left _ (pow_pos (Nat.pos_of_ne_zero (by exact_mod_cast hf)) 2))
    _ = _ := by
        push_cast
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        ring

/-- **Truncating `L(1, χ_D)`.** For a nonsquare discriminant `D ≡ 0, 1 (mod 4)`, the partial sum
`∑ n ∈ Icc 1 K, χ_D n / n` of the Dirichlet series of the Kronecker character `χ_D = (D / ·)` is
within `2 √|D| (1 + log |D|) / (K + 1)` of `L(1, χ_D)`. -/
theorem norm_LFunction_kroneckerChar_one_sub_sum_Icc_le [NeZero D.natAbs]
    (hD : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD₀ : D ≠ 0) (hsq : ¬ IsSquare D) (K : ℕ) :
    ‖LFunction (kroneckerChar ℂ D hD hD₀) 1 -
        ∑ n ∈ Icc 1 K, kroneckerChar ℂ D hD hD₀ n / (n : ℂ)‖ ≤
      2 * (Real.sqrt D.natAbs * (1 + Real.log D.natAbs)) / (K + 1) := by
  refine norm_LFunction_one_sub_sum_Icc_div_le _ ?_ (norm_sum_Icc_kroneckerChar_le hD hD₀ hsq) K
  rwa [Ne, kroneckerChar_eq_one_iff_isSquare]

end TauCeti
