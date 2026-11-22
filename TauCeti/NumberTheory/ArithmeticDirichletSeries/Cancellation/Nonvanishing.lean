/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# The continued L-function of a cancelling weight does not vanish on `Re s ≥ 1`

Let `χ` be a unitary ideal weight of a number field `K` with cancellation
(`TauCeti.HasCancellation χ`), so that its continued L-function
`TauCeti.continuedLFunctionOfWeight χ` is holomorphic on `Re s > 1 - 1 / [K : ℚ]`. On `Re s > 1`
it is the `L`-series of `χ`, which does not vanish there because of its Euler product. This file
proves that it has no zeros on the line `Re s = 1` either, under a hypothesis on the pointwise
square `χ ^ 2`.

The classical `3-4-1` argument compares `χ` with `χ ^ 2`: for `σ > 1`,
`1 ≤ ‖ζ_K(σ) ^ 3 L(χ, σ + it) ^ 4 L(χ ^ 2, σ + 2it)‖`. A zero of `L(χ, ·)` at `1 + it`
outweighs the simple pole of `ζ_K` at `1`, provided the `L`-series of `χ ^ 2` continues
continuously to `1 + 2it` (`TauCeti.UnitaryIdealWeight.ne_zero_of_eqOn_LSeries`). The square is
handled in two ways:

* if `χ ^ 2` also has cancellation, its own continued L-function supplies the continuation, and
  the continued L-function of `χ` has no zero on `Re s ≥ 1`;
* if `χ ^ 2` is a norm twist `I ↦ N(I) ^ (u * I)` on its good ideals (as for a quadratic
  character, where `u = 0`), its `L`-series is a translate of a Dedekind zeta function with
  finitely many Euler factors deleted. That translate is continuous away from its pole at
  `1 + u * I`, which leaves only the point `s = 1 + (u / 2) * I` uncovered.

When `[K : ℚ] = 1`, `continuedLFunctionOfWeight χ` continues to `Re s > 0`, so Landau's theorem
(`TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau`) closes the remaining point
`1 + (u / 2) * I` unconditionally.

## Main results

* `TauCeti.continuedLFunctionOfWeight_ne_zero_of_one_lt_re`: nonvanishing on `Re s > 1`, for
  every unitary weight.
* `TauCeti.continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq`: if both `χ` and `χ ^ 2`
  have cancellation, the continued L-function of `χ` has no zeros on `Re s ≥ 1`.
* `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq`: if `χ` has cancellation
  and `χ ^ 2` is a norm twist with parameter `u` on its good ideals, there are no zeros on
  `Re s ≥ 1` other than possibly `1 + (u / 2) * I`.
* `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq`: the case `u = 0`, for
  weights whose square is trivial on its good ideals.
* `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one` and
  `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one`: full
  `Re s ≥ 1` nonvanishing for `[K : ℚ] = 1`, closing the exceptional point via Landau's theorem.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The case analysis on the square follows Mathlib's
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao), where `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` proves the analogous
  statement for Dirichlet `L`-functions.
-/

public section

namespace TauCeti

open Complex Filter IsDedekindDomain NumberField
open scoped Topology

variable {K : Type*} [Field K] [NumberField K]

/-- **No zeros to the right of `1`.** For every unitary weight `χ`, with or without cancellation,
the continued L-function of `χ` does not vanish on `Re s > 1`: there it is the `L`-series of `χ`,
an absolutely convergent Euler product. -/
theorem continuedLFunctionOfWeight_ne_zero_of_one_lt_re (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 1 < s.re) : continuedLFunctionOfWeight χ s ≠ 0 := by
  rw [continuedLFunctionOfWeight_eq_LSeries χ hs,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val]
  refine χ.1.LSeries_ne_zero_of_summable_idealTerm ?_
  rw [← UnitaryIdealWeight.toIdealArithmeticFunction_eq_val]
  exact summable_idealTerm_of_unitary_of_one_lt_re χ hs

/-- **Nonvanishing when the square also cancels.** If a unitary weight `χ` and its pointwise
square `χ ^ 2` both have cancellation, the continued L-function of `χ` has no zeros on the closed
half-plane `Re s ≥ 1`. -/
theorem continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) (hχ₂ : HasCancellation (χ ^ 2)) {s : ℂ} (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re χ hs
  -- the continued L-function of `χ ^ 2` is holomorphic, hence continuous, at `2s - 1`
  exact χ.ne_zero_of_eqOn_LSeries hs.symm (differentiableAt_continuedLFunctionOfWeight hχ hs.le)
    (fun z hz ↦ continuedLFunctionOfWeight_eq_LSeries χ hz)
    (differentiableAt_continuedLFunctionOfWeight hχ₂ (by norm_num [← hs])).continuousAt
    fun z hz ↦ continuedLFunctionOfWeight_eq_LSeries _ hz

/-- **Nonvanishing when the square is a norm twist on its good ideals.** Let `χ` be a unitary
weight with cancellation whose pointwise square agrees with `I ↦ N(I) ^ (u * I)` on its good
ideals. Then the continued L-function of `χ` has no zeros on `Re s ≥ 1` except possibly at
`s = 1 + (u / 2) * I`, where the `L`-series of `χ ^ 2` has its pole at `2s - 1 = 1 + u * I`. -/
theorem continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) {u : ℝ} (hχ₂ : (χ ^ 2).1.IsNormTwistOnGood u) {s : ℂ}
    (hs : 1 ≤ s.re) (hsu : s ≠ 1 + (u : ℂ) / 2 * I) :
    continuedLFunctionOfWeight χ s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re χ hs
  exact χ.ne_zero_of_eqOn_LSeries_of_isNormTwistOnGood_sq hχ₂ hs.symm hsu
    (differentiableAt_continuedLFunctionOfWeight hχ hs.le)
    fun z hz ↦ continuedLFunctionOfWeight_eq_LSeries χ hz

/-- **Nonvanishing when the square is trivial on its good ideals**, as for a quadratic character.
If a unitary weight `χ` has cancellation and `χ ^ 2` takes the value `1` on its good ideals, the
continued L-function of `χ` has no zeros on `Re s ≥ 1` except possibly at `s = 1`. -/
theorem continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) (hχ₂ : (χ ^ 2).1.IsTrivialOnGood) {s : ℂ} (hs : 1 ≤ s.re)
    (hs1 : s ≠ 1) : continuedLFunctionOfWeight χ s ≠ 0 :=
  continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq hχ
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr hχ₂) hs (by simpa using hs1)

/-- **Unconditional nonvanishing of `continuedLFunctionOfWeight` on `Re s ≥ 1` when
`[K : ℚ] = 1`.** For a degree-`1` field, cancellation continues `L(χ, ·)` holomorphically to
`Re s > 0`, discharging both continuation hypotheses of Landau's theorem unconditionally. -/
theorem continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ)
    {u : ℝ} (hχ₂ : (χ ^ 2).1.IsNormTwistOnGood u) {s : ℂ} (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ s ≠ 0 := by
  have hdiff : DifferentiableOn ℂ (continuedLFunctionOfWeight χ) {z | (0 : ℝ) < z.re} := by
    simpa [hK] using differentiableOn_continuedLFunctionOfWeight hχ
  have hopen : IsOpen {z : ℂ | (0 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_finrank_eq_one hK hχ₂
    (hdiff.mono fun _ hz ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz)
    (fun z hz ↦ by
      rw [continuedLFunctionOfWeight_eq_LSeries χ hz,
        UnitaryIdealWeight.toIdealArithmeticFunction_eq_val])
    (hdiff.differentiableAt (hopen.mem_nhds (by norm_num))).continuousAt hs

/-- **Unconditional nonvanishing of `continuedLFunctionOfWeight` on `Re s ≥ 1` when
`[K : ℚ] = 1` and `(χ ^ 2).1.IsTrivialOnGood`.** -/
theorem continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ)
    (hχ₂ : (χ ^ 2).1.IsTrivialOnGood) {s : ℂ} (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ s ≠ 0 :=
  continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one hK hχ
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr hχ₂) hs

end TauCeti
