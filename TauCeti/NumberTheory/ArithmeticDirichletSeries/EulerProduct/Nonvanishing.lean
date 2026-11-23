/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# `3-4-1` nonvanishing for norm-twisted-square ideal weights

Let `K` be a number field and `χ : TauCeti.MultiplicativeIdealWeight K` a completely multiplicative
ideal weight whose pointwise square `χ ^ 2` is a purely imaginary norm twist
`I ↦ N(I) ^ (u * I)` on its good ideals (`(χ ^ 2).IsNormTwistOnGood u`). Then `χ` is
automatically unitary (`TauCeti.MultiplicativeIdealWeight.unitaryOfIsNormTwistOnGoodSq`), and
`L(χ ^ 2, ·)` agrees on `Re s > 1` with the `u * I`-translate of a Dedekind zeta function with
finitely many Euler factors removed. By
`TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub`, that translate continues
continuously to every point of `Re s = 1` except `1 + u * I`, so the `3-4-1` inequality rules out
zeros of any continuation `L` of `L(χ, ·)` everywhere on the line `Re s = 1` except possibly at
`s = 1 + (u / 2) * I`.

## Main results

* `TauCeti.MultiplicativeIdealWeight.ne_zero_of_eqOn_LSeries_of_isNormTwistOnGood_sq`: `3-4-1`
  nonvanishing on `Re s = 1` away from `1 + (u / 2) * I` when `(χ ^ 2).IsNormTwistOnGood u`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4, for the `3-4-1` argument.
* The global argument follows Mathlib's `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao).
-/

public section

namespace TauCeti.MultiplicativeIdealWeight

open Complex IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The `3-4-1` nonvanishing criterion on `Re s = 1` away from `1 + (u / 2) * I`** for a
completely multiplicative ideal weight `χ` whose square is a purely imaginary norm twist
`I ↦ N(I) ^ (u * I)` on its good ideals. -/
theorem ne_zero_of_eqOn_LSeries_of_isNormTwistOnGood_sq
    (χ : MultiplicativeIdealWeight K) {u : ℝ} (hχ₂ : (χ ^ 2).IsNormTwistOnGood u)
    {L : ℂ → ℂ} {s : ℂ} (hs : s.re = 1) (hsu : s ≠ 1 + (u : ℂ) / 2 * Complex.I)
    (hLs : DifferentiableAt ℂ L s)
    (hLL : Set.EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    L s ≠ 0 := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (χ ^ 2).badPrimes = (S : Set (HeightOneSpectrum (𝓞 K))) :=
    ⟨(χ ^ 2).finite_badPrimes.toFinset, (χ ^ 2).finite_badPrimes.coe_toFinset.symm⟩
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K S
  set ρ : ℂ := dedekindZeta_residue K * ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ))
  set w₀ : ℂ := 2 * s - 1 - (u : ℂ) * Complex.I
  have hw₀re : w₀.re = 1 := by norm_num [w₀, hs]
  have hw₀ : w₀ - 1 ≠ 0 := fun h ↦ hsu (by linear_combination h / 2)
  have hcont : ContinuousAt
      (fun z : ℂ ↦ G (z - (u : ℂ) * Complex.I) + ρ / (z - (u : ℂ) * Complex.I - 1))
      (2 * s - 1) := by
    have hG₀ : ContinuousAt G w₀ :=
      (hG.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hw₀re.ge))).continuousAt
    have hsub : ContinuousAt (fun z : ℂ ↦ z - (u : ℂ) * Complex.I) (2 * s - 1) :=
      continuousAt_id.sub continuousAt_const
    exact (hG₀.comp_of_eq hsub rfl).add
      (continuousAt_const.div (hsub.sub continuousAt_const) hw₀)
  have hLL' : Set.EqOn L
      (LSeries (normCoeff K (unitaryOfIsNormTwistOnGoodSq hχ₂).toIdealArithmeticFunction))
      {z | 1 < z.re} := by
    rw [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, val_unitaryOfIsNormTwistOnGoodSq]
    exact hLL
  refine (unitaryOfIsNormTwistOnGoodSq hχ₂).ne_zero_of_eqOn_LSeries hs hLs hLL' hcont fun z hz ↦ ?_
  have hz' : 1 < (z - (u : ℂ) * Complex.I).re := by simpa using hz
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_pow,
    val_unitaryOfIsNormTwistOnGoodSq, hχ₂.LSeries_normCoeff hS, hGL _ hz', sub_add_cancel]

end TauCeti.MultiplicativeIdealWeight
