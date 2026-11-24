/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

import TauCeti.NumberTheory.LSeries.ThreeFourOne

/-!
# Logarithmic derivatives of presented Hecke L-series

On `Re s > 1`, the negative logarithmic derivative of the Hecke L-series of a ray class
character has coefficients `χ(A) Λ_K(A)`. The character is extended by zero at ideals meeting
the finite part of the presentation modulus. In particular, the principal character contributes
only the von Mangoldt terms prime to that modulus.

The logarithmic derivatives of the principal character, `χ`, and `χ ^ 2`, all presented at the
same modulus, satisfy the `3-4-1` inequality. At each good ideal the three terms share a
nonnegative factor `Λ_K(A) / N(A)^σ`, leaving `3 + 4 Re z + Re (z ^ 2)` for
`z = χ(A) / N(A)^(it)`. At the remaining ideals all three terms vanish.

## References

* H. Davenport, *Multiplicative Number Theory*, §14, for the logarithmic derivative argument.
-/

public section

open Complex NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

private theorem threeFourOne_idealTerm_vonMangoldtTransform_nonneg (χ : RayClassCharacter 𝔪)
    (A : (Ideal (𝓞 K))⁰) (σ t : ℝ) :
    0 ≤ 3 * (idealTerm K
        (IdealArithmeticFunction.vonMangoldtTransform
          (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight.toIdealArithmeticFunction) σ A).re +
      4 * (idealTerm K χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform
        ((σ : ℂ) + I * t) A).re +
      (idealTerm K (χ ^ 2).toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform
        ((σ : ℂ) + 2 * (I * t)) A).re := by
  simp only [idealTerm_def, IdealArithmeticFunction.vonMangoldtTransform_apply,
    UnitaryIdealWeight.toIdealArithmeticFunction_apply, val_toUnitaryIdealWeight]
  by_cases hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) 𝔪.support
  · rw [RayClassCharacter.toMultiplicativeIdealWeight_one,
      MultiplicativeIdealWeight.ofBadPrimes_apply, ite_eq_left hA, one_mul, pow_two,
      toMultiplicativeIdealWeight_mul, MultiplicativeIdealWeight.mul_apply, ← pow_two]
    let N := Ideal.absNorm (A : Ideal (𝓞 K))
    have hN : 0 < N := Ideal.absNorm_pos_of_nonZeroDivisors A
    have hN₀ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    let w := (IdealArithmeticFunction.vonMangoldt (K := K) A).re
    let a := w / (N : ℝ) ^ σ
    set z := χ.toMultiplicativeIdealWeight A / (N : ℂ) ^ (I * t) with hz
    have hw : IdealArithmeticFunction.vonMangoldt A = (w : ℂ) :=
      Complex.ext (by simp [w]) (by simp [IdealArithmeticFunction.vonMangoldt_im])
    have hbase : (N : ℂ) ^ (σ : ℂ) = ((N : ℝ) ^ σ : ℝ) := by
      simpa using (Complex.ofReal_cpow (Nat.cast_nonneg N) σ).symm
    have hnorm : ‖z‖ ≤ 1 := by
      rw [hz, norm_div, Complex.norm_natCast_cpow_of_pos hN]
      simpa using χ.toUnitaryIdealWeight.norm_le_one A
    have e₀ : (w : ℂ) / (N : ℂ) ^ (σ : ℂ) = a := by
      rw [hbase, ← Complex.ofReal_div]
    have e₁ : χ.toMultiplicativeIdealWeight A * (w : ℂ) / (N : ℂ) ^ ((σ : ℂ) + I * t) =
        (a : ℂ) * z := by
      rw [cpow_add _ _ hN₀, hz, ← e₀, div_mul_div_comm, mul_comm (w : ℂ)]
    have e₂ : χ.toMultiplicativeIdealWeight A ^ 2 * (w : ℂ) /
        (N : ℂ) ^ ((σ : ℂ) + 2 * (I * t)) = (a : ℂ) * z ^ 2 := by
      rw [cpow_add _ _ hN₀, cpow_ofNat_mul, hz, ← e₀, div_pow, div_mul_div_comm,
        mul_comm (w : ℂ)]
    rw [hw, e₀, e₁, e₂]
    have ha : 0 ≤ a := div_nonneg IdealArithmeticFunction.vonMangoldt_re_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg N) σ)
    calc
      0 ≤ a * LSeries.threeFourOneCombination z :=
        mul_nonneg ha (LSeries.threeFourOneCombination_nonneg hnorm)
      _ = _ := by
        simp only [LSeries.threeFourOneCombination_def, ofReal_re, mul_re, ofReal_im,
          zero_mul, sub_zero]
        ring
  · simp [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo, hA]

/-- **The logarithmic derivative `3-4-1` inequality.** For `σ > 1`, the real parts of the
negative logarithmic derivatives of `L(1, σ)`, `L(χ, σ + it)` and `L(χ², σ + 2it)` have
nonnegative weighted sum with weights `3`, `4` and `1`. All three series use the same modulus. -/
theorem threeFourOne_neg_logDeriv_LSeries_nonneg (χ : RayClassCharacter 𝔪) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-logDeriv (LSeries (normCoeff K
        (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight.toIdealArithmeticFunction)) σ).re +
      4 * (-logDeriv (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
        ((σ : ℂ) + I * t)).re +
      (-logDeriv (LSeries (normCoeff K (χ ^ 2).toUnitaryIdealWeight.toIdealArithmeticFunction))
        ((σ : ℂ) + 2 * (I * t))).re := by
  have habs (ψ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
      idealAbscissaOfAbsConv K ψ.toUnitaryIdealWeight.val.toIdealArithmeticFunction < s.re :=
    idealAbscissaOfAbsConv_lt_re_of_bounded (C := 1) (fun A ↦ by
      rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]
      exact ψ.toUnitaryIdealWeight.norm_le_one A) hs
  have h₀ := habs 1 (s := (σ : ℂ)) (by simpa using hσ)
  have h₁ := habs χ (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have h₂ := habs (χ ^ 2) (s := (σ : ℂ) + 2 * (I * t)) (by simpa [mul_re] using hσ)
  simp only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform _ h₀,
    MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform _ h₁,
    MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform _ h₂, neg_neg]
  have hsumRe {f : IdealArithmeticFunction K} {s : ℂ} (hs : idealAbscissaOfAbsConv K f < s.re) :=
    Complex.hasSum_re (IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform hs).hasSum
  have hsum := (((hsumRe h₀).mul_left (3 : ℝ)).add
    ((hsumRe h₁).mul_left (4 : ℝ))).add (hsumRe h₂)
  refine hsum.nonneg fun A ↦ ?_
  simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
    threeFourOne_idealTerm_vonMangoldtTransform_nonneg χ A σ t

end TauCeti.GlobalNumberFields.RayClassCharacter
