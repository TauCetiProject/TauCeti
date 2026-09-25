/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
public import TauCeti.NumberTheory.LSeries.ThreeFourOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import Mathlib.NumberTheory.EulerProduct.ExpLog

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

Each `L`-series is the exponential of a sum of principal logarithms over the primes
(`TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`), so the norm of the
product is the exponential of the sum over the primes `𝔭` of the real part of

```text
3 (-log (1 - χ₀(𝔭) N(𝔭)^{-σ})) + 4 (-log (1 - χ(𝔭) N(𝔭)^{-σ-it}))
  + (-log (1 - χ(𝔭)² N(𝔭)^{-σ-2it})).
```

At a prime where `χ₀` vanishes all three terms vanish; at every other prime `χ₀(𝔭) = 1` and the
term is nonnegative by the local inequality
`TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_nonneg`.

## Main results

* `TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one`: the `3-4-1` bound for a unitary
  weight `χ` against a weight `χ₀` trivial on its good ideals, with bad primes among those of `χ`.
* `TauCeti.UnitaryIdealWeight.norm_dedekindZeta_threeFourOne_ge_one`: the case `χ₀ = 1`, where the
  first factor is the Dedekind zeta function.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
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
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.1.badPrimes)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    0 ≤ 3 * (-log (1 - χ₀ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ))).re +
      4 * (-log (1 - χ.1 P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + I * t))).re +
      (-log (1 - (χ ^ 2).1 P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * I * t))).re := by
  rw [val_pow, MultiplicativeIdealWeight.pow_apply _ two_ne_zero]
  by_cases hP : χ₀ P.asIdeal = 0
  · -- a bad prime of `χ₀` is a bad prime of `χ`, so every Euler factor is `1`
    have hχ : χ.1 P.asIdeal = 0 :=
      MultiplicativeIdealWeight.mem_badPrimes.mp
        (hbad (MultiplicativeIdealWeight.mem_badPrimes.mpr hP))
    simp [hP, hχ]
  · have h1 : χ₀ P.asIdeal = 1 := h₀.apply_eq_one ((χ₀.apply_ne_zero_iff_isGood _).mp hP)
    have hN1 : 1 < Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hN : (0 : ℝ) < Ideal.absNorm P.asIdeal := by positivity
    have hNc : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    set a : ℝ := (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) with ha
    set z : ℂ := χ.1 P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (I * t) with hz
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
    have e₁ : χ.1 P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + I * t) = a * z := by
      rw [cpow_add _ _ hNc, hbase, hainv, hz]
      field_simp
    have e₂ : χ.1 P.asIdeal ^ 2 / (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * I * t) =
        a * z ^ 2 := by
      rw [mul_assoc, cpow_add _ _ hNc, cpow_ofNat_mul, hbase, hainv, hz]
      field_simp
    rw [e₀, e₁, e₂]
    exact LSeries.threeFourOne_re_neg_log_one_sub_nonneg (by positivity) ha1 hnz

/-- The Euler product of a weight bounded by one, in exponential form on `Re s > 1`: the
prime-indexed sum of principal logarithms converges, and its exponential is the `L`-series. -/
private theorem summable_and_exp_tsum_eq_LSeries (ψ : MultiplicativeIdealWeight K)
    (hψ : ∀ I, ‖ψ I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
        -log (1 - ψ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) ∧
      exp (∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - ψ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) =
        LSeries (normCoeff K ψ.toIdealArithmeticFunction) s := by
  have h := summable_idealTerm_of_bounded_of_one_lt_re (f := ψ.toIdealArithmeticFunction)
    (C := 1) (fun I ↦ (ψ.toIdealArithmeticFunction_apply I).symm ▸ hψ I) hs
  exact ⟨(Summable.clog_one_sub (ψ.summable_div_of_summable_idealTerm h)).neg,
    ψ.exp_tsum_neg_log_one_sub_eq_LSeries h⟩

/-- **The `3-4-1` bound for unitary ideal weights.** Let `χ` be a unitary weight and `χ₀` a
weight that is trivial on its good ideals, with every bad prime of `χ₀` a bad prime of `χ`. For
real `σ > 1` and real `t`, the `L`-series of `χ₀` at `σ` cubed, times that of `χ` at `σ + it` to
the fourth power, times that of `χ²` at `σ + 2it`, has norm at least one. -/
theorem norm_LSeries_threeFourOne_ge_one (χ : UnitaryIdealWeight K)
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.1.badPrimes) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    1 ≤ ‖LSeries (normCoeff K χ₀.toIdealArithmeticFunction) σ ^ 3 *
      LSeries (normCoeff K χ.toIdealArithmeticFunction) ((σ : ℂ) + I * t) ^ 4 *
      LSeries (normCoeff K (χ ^ 2).toIdealArithmeticFunction) ((σ : ℂ) + 2 * I * t)‖ := by
  obtain ⟨hs₀, hE₀⟩ := summable_and_exp_tsum_eq_LSeries χ₀ (fun _ ↦ h₀.norm_apply_le_one)
    (s := σ) (by simpa using hσ)
  obtain ⟨hs₁, hE₁⟩ := summable_and_exp_tsum_eq_LSeries χ.1 χ.norm_le_one
    (s := (σ : ℂ) + I * t) (by simpa using hσ)
  obtain ⟨hs₂, hE₂⟩ := summable_and_exp_tsum_eq_LSeries (χ ^ 2).1 (χ ^ 2).norm_le_one
    (s := (σ : ℂ) + 2 * I * t) (by simpa using hσ)
  simp only [toIdealArithmeticFunction_eq_val]
  rw [← hE₀, ← hE₁, ← hE₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add, norm_exp,
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

end UnitaryIdealWeight

end TauCeti
