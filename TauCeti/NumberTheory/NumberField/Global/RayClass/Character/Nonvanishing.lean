/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation

/-!
# Nonvanishing on `Re s ≥ 1` for ray class L-functions

For a nontrivial ray class character `χ` of a modulus `𝔪` of a number field `K`, the unitary
ideal weight `χ.toUnitaryIdealWeight` has cancellation
(`TauCeti.GlobalNumberFields.RayClassCharacter.hasCancellation_toUnitaryIdealWeight`), so its
continued L-function `TauCeti.continuedLFunctionOfWeight χ.toUnitaryIdealWeight` is holomorphic
on `Re s > 1 - 1 / [K : ℚ]`.

When `[K : ℚ] = 1`, that half-plane is `Re s > 0`, and combining `3-4-1` with Landau's theorem
(`TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one` when
`χ ^ 2 = 1`, and `TauCeti.continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq` when
`χ ^ 2 ≠ 1`) yields unconditional nonvanishing on `Re s ≥ 1`.

For an arbitrary number field `K` and a quadratic character (`χ ^ 2 = 1`),
`ne_zero_of_one_le_re_of_sq_eq_one` and `meromorphicOrderAt_eq_zero_of_one_le_re_of_sq_eq_one`
give the Landau nonvanishing criteria on `Re s ≥ 1` for any continuation `L : ℂ → ℂ` given only on
the half-plane `Re s > 1 / 2`.

## Main results

* `ne_zero_of_one_le_re_of_sq_eq_one` and `meromorphicOrderAt_eq_zero_of_one_le_re_of_sq_eq_one`
  (in `TauCeti.GlobalNumberFields.RayClassCharacter`): half-plane Landau nonvanishing and
  meromorphic-order-zero criteria on `Re s ≥ 1` for an arbitrary continuation `L` when `χ ^ 2 = 1`.
* `continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re_of_finrank_eq_one`
  (in `TauCeti.GlobalNumberFields.RayClassCharacter`): nonvanishing on `Re s ≥ 1` when `[K : ℚ] = 1`
  and `χ ≠ 1`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section

open Filter NumberField Set TauCeti
open scoped NumberField Topology

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Half-plane Landau nonvanishing criterion on `Re s ≥ 1` for quadratic ray class characters.**
For any continuation `L : ℂ → ℂ` holomorphic on `{s | 1 / 2 < s.re}` agreeing with the `L`-series
of `χ` on `{s | 1 < s.re}`, together with a continuation `Z` of `dedekindZeta K` on
`{s | 1 / 2 < s.re} \ {1}` satisfying the sharp boundary condition at `(1 / 2)⁺`, `L s ≠ 0` for
all `s` with `1 ≤ s.re`. Only half-plane data on `Re s > 1 / 2` is required. -/
theorem ne_zero_of_one_le_re_of_sq_eq_one {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1)
    {Z L : ℂ → ℂ} (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) : L s ≠ 0 := by
  have hLL' : EqOn L
      (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
      {s | 1 < s.re} := by
    simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      val_toUnitaryIdealWeight] using hLL
  exact MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_isTrivialOnGood_sq
    (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ) hZ hZζ hL hLL' hnot hs

/-- **Half-plane meromorphic order zero on `Re s ≥ 1` for quadratic ray class characters.** Under
the half-plane continuation and boundary hypotheses of `ne_zero_of_one_le_re_of_sq_eq_one`,
`meromorphicOrderAt L s = 0` for every `s` with `1 ≤ s.re`. -/
theorem meromorphicOrderAt_eq_zero_of_one_le_re_of_sq_eq_one {χ : RayClassCharacter 𝔪}
    (hχ : χ ^ 2 = 1) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) : meromorphicOrderAt L s = 0 := by
  have hLL' : EqOn L
      (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
      {s | 1 < s.re} := by
    simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      val_toUnitaryIdealWeight] using hLL
  exact MultiplicativeIdealWeight.meromorphicOrderAt_eq_zero_of_one_le_re_of_isNormTwistOnGood_sq
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr
      (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ))
    hZ hZζ hL hLL' (by simpa using hnot) hs

/-- **Unconditional nonvanishing on `Re s ≥ 1` of the cancellation-continued ray class L-function
when `[K : ℚ] = 1`.** For any nontrivial ray class character `χ ≠ 1` of any modulus `𝔪`,
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` does not vanish on `Re s ≥ 1`: when
`χ ^ 2 = 1` this follows from Landau's theorem (`[K : ℚ] = 1`), and when `χ ^ 2 ≠ 1` it follows
from `3-4-1` and cancellation for `χ ^ 2`. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 := by
  by_cases hsq : χ ^ 2 = 1
  · refine continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one hK
      (hasCancellation_toUnitaryIdealWeight hχ) ?_ hs
    rw [UnitaryIdealWeight.val_pow, val_toUnitaryIdealWeight]
    exact χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hsq
  · have hpow : χ.toUnitaryIdealWeight ^ 2 = (χ ^ 2).toUnitaryIdealWeight := by
      rw [sq, sq, toUnitaryIdealWeight_mul]
    exact continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq
      (hasCancellation_toUnitaryIdealWeight hχ)
      (hpow ▸ hasCancellation_toUnitaryIdealWeight hsq) hs

end TauCeti.GlobalNumberFields.RayClassCharacter
