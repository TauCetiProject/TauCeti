/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
public import TauCeti.NumberTheory.LSeries.ThreeFourOne
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff
import TauCeti.NumberTheory.LSeries.Nonvanishing

/-!
# The 3-4-1 bound for the Euler products of unitary ideal weights

Let `χ` be a unitary ideal weight of a number field `K`, and let `χ₀` be a weight that is trivial
on its good ideals and whose bad primes are among those of `χ` — for instance the trivial weight,
whose `L`-series is the Dedekind zeta function `ζ_K`. For real `σ > 1` and real `t`, this file
proves the classical `3-4-1` inequality

```text
1 ≤ ‖L(χ₀, σ) ^ 3 * L(χ, σ + it) ^ 4 * L(χ², σ + 2it)‖,
```

where each `L`-series is the `LSeries` of the norm coefficients of the weight. It is the
positivity input for nonvanishing on the line `Re s = 1`, and is exactly the bound hypothesis of
the analytic criterion `TauCeti.LSeries.ne_zero_of_threeFourOne`: a continuation of `L(χ, ·)`
that is differentiable at `1 + it` does not vanish there, provided `L(χ₀, σ) = O((σ - 1)⁻¹)` as
`σ → 1⁺` and `L(χ², ·)` continues continuously to `1 + 2it`.

The same weights satisfy the `3-4-1` inequality for the real parts of the negative logarithmic
derivatives `-L'/L`, whose coefficients are `χ(A) Λ_K(A)`. At each ideal good for `χ₀` the three
terms share the nonnegative factor `Λ_K(A) / N(A) ^ σ`, leaving `3 + 4 Re z + Re (z ^ 2)` for
`z = χ(A) / N(A) ^ (it)`; at every other ideal all three terms vanish.

## Main results

* `TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one`: the `3-4-1` bound for a unitary
  weight `χ` against a weight `χ₀` trivial on its good ideals, with bad primes among those of `χ`.
* `TauCeti.UnitaryIdealWeight.norm_dedekindZeta_threeFourOne_ge_one`: the case `χ₀ = 1`, where the
  first factor is the Dedekind zeta function.
* `TauCeti.UnitaryIdealWeight.threeFourOne_re_neg_logDeriv_LSeries_nonneg`: the `3-4-1`
  inequality for the negative logarithmic derivatives, with the same hypotheses on `χ₀`.
* `TauCeti.UnitaryIdealWeight.ne_zero_of_eqOn_LSeries`: the resulting nonvanishing criterion on
  the line `Re s = 1`, for continuations of the `L`-series of `χ` and of `χ²`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4, and §14 for the logarithmic
  derivative argument.
* The global argument is that of Mathlib's `DirichletCharacter.norm_LSeries_product_ge_one` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler, with
  unitary ideal weights of a number field in place of Dirichlet characters.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace UnitaryIdealWeight

variable {χ₀ : MultiplicativeIdealWeight K}

/-- The local `3-4-1` inequality at a single prime. It needs only `σ > 0`, which puts
`N(𝔭) ^ (-σ)` in the open unit interval. -/
private theorem threeFourOne_local_nonneg {χ : UnitaryIdealWeight K}
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.val.badPrimes)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    0 ≤ 3 * (-log (1 - χ₀ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ))).re +
      4 * (-log (1 - χ.val P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + I * t))).re +
      (-log (1 - (χ ^ 2).val P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * I * t))).re := by
  rw [val_pow, MultiplicativeIdealWeight.pow_apply _ two_ne_zero]
  by_cases hP : χ₀ P.asIdeal = 0
  · -- a bad prime of `χ₀` is a bad prime of `χ`, so every Euler factor is `1`
    have hχ : χ.val P.asIdeal = 0 :=
      MultiplicativeIdealWeight.mem_badPrimes.mp
        (hbad (MultiplicativeIdealWeight.mem_badPrimes.mpr hP))
    simp [hP, hχ]
  · have h1 : χ₀ P.asIdeal = 1 := h₀.apply_eq_one ((χ₀.apply_ne_zero_iff_isGood _).mp hP)
    have hN1 : 1 < Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hN : (0 : ℝ) < Ideal.absNorm P.asIdeal := by positivity
    have hNc : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    set a : ℝ := (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) with ha
    set z : ℂ := χ.val P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (I * t) with hz
    have ha1 : a < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN1) (neg_lt_zero.2 hσ)
    have hnz : ‖z‖ ≤ 1 := by
      rw [hz, norm_div, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hN)]
      simpa using χ.norm_le_one P.asIdeal
    have hbase : (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ) =
        (((Ideal.absNorm P.asIdeal : ℝ) ^ σ : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow (Nat.cast_nonneg (Ideal.absNorm P.asIdeal)) σ).symm
    have hainv : (a : ℂ) = ((((Ideal.absNorm P.asIdeal : ℝ) ^ σ : ℝ) : ℂ))⁻¹ := by
      rw [ha, Real.rpow_neg hN.le, Complex.ofReal_inv]
    have e₀ : χ₀ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ) = a := by
      rw [h1, hbase, hainv, one_div]
    have e₁ : χ.val P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + I * t) = a * z := by
      rw [cpow_add _ _ hNc, hbase, hainv, hz]
      field_simp
    have e₂ : χ.val P.asIdeal ^ 2 / (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * I * t) =
        a * z ^ 2 := by
      rw [mul_assoc, cpow_add _ _ hNc, cpow_ofNat_mul, hbase, hainv, hz]
      field_simp
    rw [e₀, e₁, e₂]
    exact LSeries.threeFourOne_re_neg_log_one_sub_nonneg (by positivity) ha1 hnz

/-- **The `3-4-1` bound for unitary ideal weights.** Let `χ` be a unitary weight and `χ₀` a
weight that is trivial on its good ideals, with every bad prime of `χ₀` a bad prime of `χ`. For
real `σ > 1` and real `t`, the `L`-series of `χ₀` at `σ` cubed, times that of `χ` at `σ + it` to
the fourth power, times that of `χ²` at `σ + 2it`, has norm at least one. -/
theorem norm_LSeries_threeFourOne_ge_one (χ : UnitaryIdealWeight K)
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.val.badPrimes) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    1 ≤ ‖LSeries (normCoeff K χ₀.toIdealArithmeticFunction) σ ^ 3 *
      LSeries (normCoeff K χ.toIdealArithmeticFunction) ((σ : ℂ) + I * t) ^ 4 *
      LSeries (normCoeff K (χ ^ 2).toIdealArithmeticFunction) ((σ : ℂ) + 2 * I * t)‖ := by
  -- Express each factor as an exponential of a prime logarithm sum. At a bad prime of `χ₀`
  -- all three local terms vanish; at every other prime the scalar 3-4-1 bound applies.
  have hS₀ := summable_idealTerm_of_bounded_of_one_lt_re
    (f := χ₀.toIdealArithmeticFunction) (C := 1) (s := (σ : ℂ))
    (fun I ↦ (χ₀.toIdealArithmeticFunction_apply I).symm ▸ h₀.norm_apply_le_one) (by simpa using hσ)
  have hS₁ : Summable (idealTerm K χ.val.toIdealArithmeticFunction ((σ : ℂ) + I * t)) := by
    simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
      summable_idealTerm_of_unitary_of_one_lt_re χ (s := (σ : ℂ) + I * t)
        (by simpa using hσ)
  have hS₂ : Summable (idealTerm K (χ ^ 2).val.toIdealArithmeticFunction
      ((σ : ℂ) + 2 * I * t)) := by
    rw [← (χ ^ 2).toIdealArithmeticFunction_eq_val]
    exact summable_idealTerm_of_unitary_of_one_lt_re (χ ^ 2)
      (s := (σ : ℂ) + 2 * I * t) (by simpa using hσ)
  have hs₀ := χ₀.summable_neg_log_one_sub hS₀
  have hs₁ := χ.val.summable_neg_log_one_sub hS₁
  have hs₂ := (χ ^ 2).val.summable_neg_log_one_sub hS₂
  have hE₀ := χ₀.exp_tsum_neg_log_one_sub_eq_LSeries hS₀
  have hE₁ := χ.val.exp_tsum_neg_log_one_sub_eq_LSeries hS₁
  have hE₂ := (χ ^ 2).val.exp_tsum_neg_log_one_sub_eq_LSeries hS₂
  simp only [toIdealArithmeticFunction_eq_val]
  rw [← hE₀, ← hE₁, ← hE₂, ← exp_natCast_mul, ← exp_natCast_mul, ← exp_add, ← exp_add, norm_exp,
    Real.one_le_exp_iff]
  have hsum := Complex.hasSum_re
    (((hs₀.hasSum.mul_left 3).add (hs₁.hasSum.mul_left 4)).add hs₂.hasSum)
  push_cast
  refine hsum.nonneg fun P ↦ ?_
  simpa [mul_re] using threeFourOne_local_nonneg h₀ hbad P (zero_lt_one.trans hσ) t

/-- **The `3-4-1` bound against the Dedekind zeta function.** For every unitary weight `χ`, real
`σ > 1` and real `t`, `1 ≤ ‖ζ_K(σ) ^ 3 * L(χ, σ + it) ^ 4 * L(χ², σ + 2it)‖`. -/
theorem norm_dedekindZeta_threeFourOne_ge_one (χ : UnitaryIdealWeight K) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    1 ≤ ‖dedekindZeta K σ ^ 3 *
      LSeries (normCoeff K χ.toIdealArithmeticFunction) ((σ : ℂ) + I * t) ^ 4 *
      LSeries (normCoeff K (χ ^ 2).toIdealArithmeticFunction) ((σ : ℂ) + 2 * I * t)‖ := by
  simpa [dedekindZeta_eq_LSeries_normCoeff_one] using
    χ.norm_LSeries_threeFourOne_ge_one MultiplicativeIdealWeight.isTrivialOnGood_one (by simp)
      hσ t

open scoped nonZeroDivisors in
/-- The `3-4-1` combination of the von Mangoldt weighted ideal terms at a single ideal is
nonnegative. -/
private theorem threeFourOne_idealTerm_vonMangoldtTransform_nonneg {χ : UnitaryIdealWeight K}
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.val.badPrimes)
    (A : (Ideal (𝓞 K))⁰) (σ t : ℝ) :
    0 ≤ 3 * (idealTerm K χ₀.toIdealArithmeticFunction.vonMangoldtTransform σ A).re +
      4 * (idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform
        ((σ : ℂ) + I * t) A).re +
      (idealTerm K (χ ^ 2).toIdealArithmeticFunction.vonMangoldtTransform
        ((σ : ℂ) + 2 * I * t) A).re := by
  simp only [idealTerm_def, IdealArithmeticFunction.vonMangoldtTransform_apply,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_apply, toIdealArithmeticFunction_apply,
    val_pow, MultiplicativeIdealWeight.pow_apply _ two_ne_zero]
  by_cases hA : χ₀.IsGood (A : Ideal (𝓞 K))
  · rw [h₀.apply_eq_one hA, one_mul]
    let N := Ideal.absNorm (A : Ideal (𝓞 K))
    have hN : 0 < N := Ideal.absNorm_pos_of_nonZeroDivisors A
    have hN₀ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    let w := (IdealArithmeticFunction.vonMangoldt (K := K) A).re
    let a := w / (N : ℝ) ^ σ
    set z := χ.val A / (N : ℂ) ^ (I * t) with hz
    have hw : IdealArithmeticFunction.vonMangoldt A = (w : ℂ) :=
      Complex.ext (by simp [w]) (by simp [IdealArithmeticFunction.vonMangoldt_im])
    have hbase : (N : ℂ) ^ (σ : ℂ) = ((N : ℝ) ^ σ : ℝ) := by
      simpa using (Complex.ofReal_cpow (Nat.cast_nonneg N) σ).symm
    have hnorm : ‖z‖ ≤ 1 := by
      rw [hz, norm_div, Complex.norm_natCast_cpow_of_pos hN]
      simpa using χ.norm_le_one A
    have e₀ : (w : ℂ) / (N : ℂ) ^ (σ : ℂ) = a := by
      rw [hbase, ← Complex.ofReal_div]
    have e₁ : χ.val A * (w : ℂ) / (N : ℂ) ^ ((σ : ℂ) + I * t) = (a : ℂ) * z := by
      rw [cpow_add _ _ hN₀, hz, ← e₀, div_mul_div_comm, mul_comm (w : ℂ)]
    have e₂ : χ.val A ^ 2 * (w : ℂ) / (N : ℂ) ^ ((σ : ℂ) + 2 * I * t) = (a : ℂ) * z ^ 2 := by
      rw [mul_assoc (2 : ℂ), cpow_add _ _ hN₀, cpow_ofNat_mul, hz, ← e₀, div_pow,
        div_mul_div_comm, mul_comm (w : ℂ)]
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
  · -- an ideal that is bad for `χ₀` is bad for `χ`, so all three terms vanish
    have hχ : χ.val A = 0 :=
      (χ.val.apply_eq_zero_iff_not_isGood _).mpr fun h ↦ hA (h.mono hbad)
    simp [(χ₀.apply_eq_zero_iff_not_isGood _).mpr hA, hχ]

/-- **The logarithmic derivative `3-4-1` inequality for unitary ideal weights.** Let `χ` be a
unitary weight and `χ₀` a weight that is trivial on its good ideals, with every bad prime of `χ₀`
a bad prime of `χ`. For real `σ > 1` and real `t`, the real parts of the negative logarithmic
derivatives of the `L`-series of `χ₀` at `σ`, of `χ` at `σ + it` and of `χ²` at `σ + 2it` have
nonnegative weighted sum with weights `3`, `4` and `1`. -/
theorem threeFourOne_re_neg_logDeriv_LSeries_nonneg (χ : UnitaryIdealWeight K)
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.val.badPrimes) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    0 ≤ 3 * (-logDeriv (LSeries (normCoeff K χ₀.toIdealArithmeticFunction)) σ).re +
      4 * (-logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) ((σ : ℂ) + I * t)).re +
      (-logDeriv (LSeries (normCoeff K (χ ^ 2).toIdealArithmeticFunction))
        ((σ : ℂ) + 2 * I * t)).re := by
  have habs (ψ : UnitaryIdealWeight K) {s : ℂ} (hs : 1 < s.re) :
      idealAbscissaOfAbsConv K ψ.val.toIdealArithmeticFunction < s.re :=
    idealAbscissaOfAbsConv_lt_re_of_bounded (C := 1) (fun A ↦ by
      rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]
      exact ψ.norm_le_one A) hs
  have h₀' : idealAbscissaOfAbsConv K χ₀.toIdealArithmeticFunction < (σ : ℂ).re :=
    idealAbscissaOfAbsConv_lt_re_of_bounded (C := 1)
      (fun A ↦ (χ₀.toIdealArithmeticFunction_apply A).symm ▸ h₀.norm_apply_le_one)
      (by simpa using hσ)
  have h₁ := habs χ (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have h₂ := habs (χ ^ 2) (s := (σ : ℂ) + 2 * I * t) (by simpa using hσ)
  simp only [toIdealArithmeticFunction_eq_val,
    MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform _ h₀',
    MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform _ h₁,
    MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform _ h₂, neg_neg]
  have hsumRe {f : IdealArithmeticFunction K} {s : ℂ} (hs : idealAbscissaOfAbsConv K f < s.re) :=
    Complex.hasSum_re (IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform hs).hasSum
  have hsum := (((hsumRe h₀').mul_left (3 : ℝ)).add
    ((hsumRe h₁).mul_left (4 : ℝ))).add (hsumRe h₂)
  refine hsum.nonneg fun A ↦ ?_
  simpa only [toIdealArithmeticFunction_eq_val] using
    threeFourOne_idealTerm_vonMangoldtTransform_nonneg h₀ hbad A σ t

/-- **The `3-4-1` nonvanishing criterion for a unitary weight.** Let `χ` be a unitary weight and
`s` a point with `Re s = 1`. If `f` is complex differentiable at `s` and `f₂` is continuous at
`2s - 1`, and they agree on `Re z > 1` with the `L`-series of `χ` and of its pointwise square
`χ²` respectively, then `f s ≠ 0`. -/
theorem ne_zero_of_eqOn_LSeries (χ : UnitaryIdealWeight K) {s : ℂ} (hs : s.re = 1)
    {f f₂ : ℂ → ℂ} (hf : DifferentiableAt ℂ f s)
    (hfL : Set.EqOn f (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re})
    (hf₂ : ContinuousAt f₂ (2 * s - 1))
    (hf₂L : Set.EqOn f₂ (LSeries (normCoeff K (χ ^ 2).toIdealArithmeticFunction))
      {z | 1 < z.re}) :
    f s ≠ 0 := by
  -- Write `s = 1 + it`, so that `2s - 1 = 1 + 2it`. The bound
  -- `norm_dedekindZeta_threeFourOne_ge_one` and the simple pole of `ζ_K` at `s = 1` are the
  -- inputs of the analytic criterion `LSeries.ne_zero_of_threeFourOne`.
  have hs' : s = 1 + I * s.im := by
    conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
  have hs₂ : 2 * s - 1 = 1 + 2 * I * s.im := by
    conv_lhs => rw [hs']
    ring
  rw [hs'] at hf ⊢
  rw [hs₂] at hf₂
  refine LSeries.ne_zero_of_threeFourOne (f₀ := dedekindZeta K) ?_ ?_ (hf.restrictScalars ℝ) hf₂
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [hfL (by simpa using hσ), hf₂L (by simpa using hσ)]
    exact χ.norm_dedekindZeta_threeFourOne_ge_one hσ s.im
  · exact Asymptotics.isBigO_inv_sub_of_sub_smul_isBigO_one norm_smul_le
      (eventually_nhdsWithin_of_forall fun _ ↦ ne_of_gt) <| Filter.Tendsto.isBigO_one ℝ <| by
        simpa using tendsto_sub_one_mul_dedekindZeta_nhdsGT K

end UnitaryIdealWeight

end TauCeti
