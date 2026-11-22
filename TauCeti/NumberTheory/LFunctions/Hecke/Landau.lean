/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau

/-!
# Landau nonvanishing criteria for presented Hecke L-functions

For a quadratic ray class character `χ` of a modulus `𝔪` of a number field `K` (`χ ^ 2 = 1`),
`TauCeti.GlobalNumberFields.RayClassCharacter.isTrivialOnGood_sq_iff_sq_eq_one` shows that the
squared ideal weight `χ.toMultiplicativeIdealWeight ^ 2` is trivial on its good ideals. Combining
this bridge with the abstract Landau theorem for ideal weights
(`TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau`) gives conditional continuation criteria
for `TauCeti.LFunctions.heckeLFunctionC χ` on `Re s ≥ 1` over an arbitrary number field `K`.

Given a holomorphic continuation `Z` of `ζ_K` to `{s | 1 / 2 < s.re} \ {1}`, a holomorphic
continuation of `heckeLFunctionC χ` to `{s | 1 / 2 < s.re}` agreeing with its `L`-series on
`Re s > 1`, and the sharp boundary condition that `(Z σ * heckeLFunctionC χ σ).re` does not tend
to `+∞` as real `σ → (1 / 2)⁺` (in particular whenever `Z` and `heckeLFunctionC χ` are continuous
at `1 / 2`), `heckeLFunctionC χ s ≠ 0` and `meromorphicOrderAt (heckeLFunctionC χ) s = 0` for all
`s` with `1 ≤ s.re`.

For unconditional cases without supplying a continuation of `heckeLFunctionC`, see
`TauCeti.NumberTheory.LFunctions.Hecke.Rat` (which identifies `heckeLFunctionC χ` over `ℚ` with
Mathlib's `DirichletCharacter.LFunction`) and
`TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Nonvanishing` (which proves `Re s ≥ 1`
nonvanishing for `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` when `[K : ℚ] = 1`).

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one`: conditional nonvanishing
  on `Re s ≥ 1` for `heckeLFunctionC χ` when `χ ^ 2 = 1`.
* `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_of_sq_eq_one`:
  conditional meromorphic order zero on `Re s ≥ 1` for `heckeLFunctionC χ` when `χ ^ 2 = 1`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* The Dirichlet-character prototype is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao).
-/

public section

open Filter IsDedekindDomain NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Landau nonvanishing criterion on `Re s ≥ 1` for presented quadratic Hecke L-functions.**
Let `χ` be a quadratic ray class character (`χ ^ 2 = 1`) of a modulus `𝔪` of a number field `K`.
Suppose `Z` continues `dedekindZeta K` holomorphically to `{s | 1 / 2 < s.re} \ {1}`,
`heckeLFunctionC χ` is holomorphic on `{s | 1 / 2 < s.re}` and agrees with its defining
`L`-series on `{s | 1 < s.re}`, and `(Z σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as
real `σ → (1 / 2)⁺` (for example, when `Z` and `heckeLFunctionC χ` are both continuous at
`1 / 2`). Then `heckeLFunctionC χ s ≠ 0` for all `s` with `1 ≤ s.re`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one
    {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1) {Z : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * heckeLFunctionC χ σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) : heckeLFunctionC χ s ≠ 0 := by
  have hLL' : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
      {s | 1 < s.re} := by
    simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      RayClassCharacter.val_toUnitaryIdealWeight] using hLL
  exact MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_isTrivialOnGood_sq
    (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ) hZ hZζ hL hLL' hnot hs

/-- **Meromorphic order zero on `Re s ≥ 1` for presented quadratic Hecke L-functions.** Under the
continuation and boundary hypotheses of `heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one`,
`meromorphicOrderAt (heckeLFunctionC χ) s = 0` for every `s` with `1 ≤ s.re`. -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_of_sq_eq_one
    {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1) {Z : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * heckeLFunctionC χ σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) : meromorphicOrderAt (heckeLFunctionC χ) s = 0 := by
  have hLL' : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
      {s | 1 < s.re} := by
    simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      RayClassCharacter.val_toUnitaryIdealWeight] using hLL
  exact MultiplicativeIdealWeight.meromorphicOrderAt_eq_zero_of_one_le_re_of_isNormTwistOnGood_sq
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr
      (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ))
    hZ hZζ hL hLL' (by simpa using hnot) hs

end TauCeti.LFunctions
