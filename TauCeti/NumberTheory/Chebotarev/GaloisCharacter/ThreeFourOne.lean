/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Weight
public import TauCeti.NumberTheory.LSeries.ThreeFourOne
public import Mathlib.NumberTheory.LSeries.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# The 3-4-1 bound for Galois character series

The Euler products of a Galois character, its square, and the trivial character satisfy the
classical 3-4-1 positivity inequality on `Re s > 1`. All three products omit exactly the primes
ramified in the extension. This lower bound is the positivity input for proving nonvanishing of
the continued character series on the line `Re s = 1`.

The argument uses the local 3-4-1 inequality from `TauCeti.LSeries.ThreeFourOne` and the
exponential Euler product for ideal weights. See Davenport, *Multiplicative Number Theory*,
Chapter 4. The global proof follows the analogous Dirichlet-character argument in Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`,
`DirichletCharacter.norm_LSeries_product_ge_one`, with ideal weights replacing characters on
natural numbers and with ramified Euler factors omitted.
-/

public section

namespace NumberField.Chebotarev

open Complex IsDedekindDomain TauCeti
open scoped NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- A ramified prime contributes zero to each of the three logarithmic Euler factors.
private theorem local_threeFourOne_nonneg (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (P : HeightOneSpectrum (𝓞 K)) {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (-log (1 - (1 : (L ≃ₐ[K] L) →* ℂˣ).galoisCharacterWeight P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ))).re +
      4 * (-log (1 - χ.galoisCharacterWeight P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + I * t))).re +
      (-log (1 - (χ ^ 2).galoisCharacterWeight P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * I * t))).re := by
  classical
  by_cases hP : P ∈ ramifiedPrimes K L
  · simp only [(MonoidHom.galoisCharacterWeight_apply_eq_zero_iff _ P).mpr hP,
      zero_div, sub_zero, log_one, neg_zero, zero_re, mul_zero, zero_add,
      le_refl]
  · have hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q := by
      exact not_not.mp (mt (mem_ramifiedPrimes_iff (L := L) P).mpr hP)
    let a : ℝ := (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ)
    let z : ℂ := (χ.galoisCharacterWeight P.asIdeal : ℂ) /
      (Ideal.absNorm P.asIdeal : ℂ) ^ (I * t)
    have hN : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℝ) := by
      exact_mod_cast Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    have hNc : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
      exact_mod_cast hN.ne'
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a < 1 := by
      dsimp [a]
      rw [Real.rpow_neg (Nat.cast_nonneg _), inv_lt_one_iff₀]
      exact .inr (Real.one_lt_rpow (by exact_mod_cast
        (NumberField.HeightOneSpectrum.one_lt_absNorm P)) (by linarith))
    have hz : ‖z‖ ≤ 1 := by
      dsimp [z]
      rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.cast_pos.mp hN)]
      simpa using (MonoidHom.galoisCharacterUnitaryWeight χ).norm_le_one P.asIdeal
    have hbase : (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ) =
        (↑((Ideal.absNorm P.asIdeal : ℝ) ^ σ) : ℂ) := by
      simpa using (Complex.ofReal_cpow (Nat.cast_nonneg (Ideal.absNorm P.asIdeal)) σ).symm
    have h0 : (1 : (L ≃ₐ[K] L) →* ℂˣ).galoisCharacterWeight P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ) = a := by
      rw [MonoidHom.galoisCharacterWeight_apply_of_unramified _ P hur, MonoidHom.one_apply,
        Units.val_one, one_div, hbase, ← Complex.ofReal_inv]
      congr 1
      exact (Real.rpow_neg hN.le σ).symm
    have h1 : χ.galoisCharacterWeight P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + I * t) = a * z := by
      rw [cpow_add _ _ hNc, hbase]
      simp only [a, z, Real.rpow_neg hN.le, Complex.ofReal_inv, div_eq_mul_inv]
      rw [mul_inv_rev]
      ac_rfl
    have h2 : (χ ^ 2).galoisCharacterWeight P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * I * t) = a * z ^ 2 := by
      rw [MonoidHom.galoisCharacterWeight_apply_of_unramified _ P hur,
        MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        ← MonoidHom.galoisCharacterWeight_apply_of_unramified χ P hur]
      rw [mul_assoc, cpow_add _ _ hNc, cpow_ofNat_mul, hbase]
      simp only [a, z, Real.rpow_neg hN.le, Complex.ofReal_inv, div_eq_mul_inv,
        mul_pow]
      rw [mul_inv_rev, inv_pow]
      ac_rfl
    rw [h0, h1, h2]
    exact TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_nonneg ha0 ha1 hz

/-- **The 3-4-1 bound for Galois character Euler products.** For `σ > 1`, the product of the
trivial-character series to the third power, the `χ`-series at `σ + it` to the fourth power, and
the `χ²`-series at `σ + 2it` has norm at least one. The Euler factors at ramified primes are
omitted in all three series. -/
theorem norm_galoisCharacterLSeries_threeFourOne_ge_one
    (χ : (L ≃ₐ[K] L) →* ℂˣ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖LSeries (normCoeff K
        (1 : (L ≃ₐ[K] L) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction) σ ^ 3 *
      LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction)
        ((σ : ℂ) + I * t) ^ 4 *
      LSeries (normCoeff K (χ ^ 2).galoisCharacterWeight.toIdealArithmeticFunction)
        ((σ : ℂ) + 2 * I * t)‖ := by
  let w₀ := (1 : (L ≃ₐ[K] L) →* ℂˣ).galoisCharacterWeight
  let w₁ := χ.galoisCharacterWeight
  let w₂ := (χ ^ 2).galoisCharacterWeight
  let s₀ : ℂ := σ
  let s₁ : ℂ := (σ : ℂ) + I * t
  let s₂ : ℂ := (σ : ℂ) + 2 * I * t
  have hs₀ : 1 < s₀.re := by simpa [s₀] using hσ
  have hs₁ : 1 < s₁.re := by simpa [s₁] using hσ
  have hs₂ : 1 < s₂.re := by simpa [s₂] using hσ
  have hsum₀ : Summable (idealTerm K w₀.toIdealArithmeticFunction s₀) := by
    simpa only [w₀, MonoidHom.val_galoisCharacterUnitaryWeight,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
      summable_idealTerm_of_unitary_of_one_lt_re
        (MonoidHom.galoisCharacterUnitaryWeight (K := K) (L := L) 1) hs₀
  have hsum₁ : Summable (idealTerm K w₁.toIdealArithmeticFunction s₁) := by
    simpa only [w₁, MonoidHom.val_galoisCharacterUnitaryWeight,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
      summable_idealTerm_of_unitary_of_one_lt_re
        (MonoidHom.galoisCharacterUnitaryWeight (K := K) (L := L) χ) hs₁
  have hsum₂ : Summable (idealTerm K w₂.toIdealArithmeticFunction s₂) := by
    simpa only [w₂, MonoidHom.val_galoisCharacterUnitaryWeight,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
      summable_idealTerm_of_unitary_of_one_lt_re
        (MonoidHom.galoisCharacterUnitaryWeight (K := K) (L := L) (χ ^ 2)) hs₂
  let e (w : MultiplicativeIdealWeight K) (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
    -log (1 - w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)
  have he₀ : Summable (e w₀ s₀) :=
    (Summable.clog_one_sub (w₀.summable_div_of_summable_idealTerm hsum₀)).neg
  have he₁ : Summable (e w₁ s₁) :=
    (Summable.clog_one_sub (w₁.summable_div_of_summable_idealTerm hsum₁)).neg
  have he₂ : Summable (e w₂ s₂) :=
    (Summable.clog_one_sub (w₂.summable_div_of_summable_idealTerm hsum₂)).neg
  have hE₀ := w₀.exp_tsum_neg_log_one_sub_eq_LSeries hsum₀
  have hE₁ := w₁.exp_tsum_neg_log_one_sub_eq_LSeries hsum₁
  have hE₂ := w₂.exp_tsum_neg_log_one_sub_eq_LSeries hsum₂
  -- The Euler-product equalities use local names for the three weights and spectral parameters.
  change 1 ≤ ‖LSeries (normCoeff K w₀.toIdealArithmeticFunction) s₀ ^ 3 *
    LSeries (normCoeff K w₁.toIdealArithmeticFunction) s₁ ^ 4 *
    LSeries (normCoeff K w₂.toIdealArithmeticFunction) s₂‖
  rw [← hE₀, ← hE₁, ← hE₂]
  rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add, norm_exp]
  rw [Real.one_le_exp_iff]
  simp only [add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
  rw [re_tsum he₀, re_tsum he₁, re_tsum he₂]
  have hsum₀ : Summable (fun P ↦ 3 * (e w₀ s₀ P).re) :=
    (hasSum_re he₀.hasSum).summable.mul_left 3
  have hsum₁ : Summable (fun P ↦ 4 * (e w₁ s₁ P).re) :=
    (hasSum_re he₁.hasSum).summable.mul_left 4
  have hsum₂ : Summable (fun P ↦ (e w₂ s₂ P).re) :=
    (hasSum_re he₂.hasSum).summable
  have hmain : 0 ≤ ∑' P, (3 * (e w₀ s₀ P).re +
      4 * (e w₁ s₁ P).re + (e w₂ s₂ P).re) := by
    apply tsum_nonneg
    intro P
    simpa only [w₀, w₁, w₂, s₀, s₁, s₂, e] using
      local_threeFourOne_nonneg χ P hσ (t := t)
  convert hmain using 1
  rw [(hsum₀.add hsum₁).tsum_add hsum₂, hsum₀.tsum_add hsum₁,
    tsum_mul_left, tsum_mul_left]
  norm_num

end NumberField.Chebotarev
