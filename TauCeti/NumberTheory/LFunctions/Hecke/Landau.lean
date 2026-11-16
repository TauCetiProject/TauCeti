/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Quadratic

/-!
# Landau nonvanishing for quadratic ray class L-functions

For a quadratic ray class character `χ` of a modulus `𝔪` of a number field `K` (satisfying
`χ ^ 2 = 1`), the squared ideal weight `χ.toMultiplicativeIdealWeight ^ 2` is trivial on its good
ideals (`RayClassCharacter.isTrivialOnGood_sq_iff_sq_eq_one`). Applying Landau's nonvanishing
theorem for ideal weights (`TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau`) to the
canonical presented Hecke L-function `TauCeti.LFunctions.heckeLFunctionC χ` and the continued
Dedekind zeta function `TauCeti.LFunctions.dedekindZetaC K` rules out zeros on the entire closed
half-plane `Re s ≥ 1`, including the exceptional point `s = 1` where the `3-4-1` inequality fails.

The general statements take analytic continuation hypotheses on `dedekindZetaC K` and
`heckeLFunctionC χ` down to `Re s = 1 / 2` (or on `{1}ᶜ` and `ℂ` respectively). For fields of
degree `1` or `2` over `ℚ`, the continuation of `ζ_K` is already available unconditionally via
`TauCeti.exists_differentiableOn_eq_dedekindZeta_sub` and
`TauCeti.LFunctions.analyticOnNhd_dedekindZetaC_compl_singleton`, discharging the `dedekindZetaC`
hypotheses completely.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.isTrivialOnGood_sq_iff_sq_eq_one`: a ray class
  character has squared ideal weight trivial on good ideals iff `χ ^ 2 = 1`.
* `TauCeti.LFunctions.heckeLFunctionC_one_ne_zero_of_sq_eq_one`: Landau nonvanishing at `s = 1`
  for `heckeLFunctionC χ` when `χ ^ 2 = 1`.
* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one`,
  `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one_of_continuousAt`, and
  `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one_of_analyticOnNhd`:
  nonvanishing of `heckeLFunctionC χ` throughout `Re s ≥ 1` when `χ ^ 2 = 1`.
* `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_of_sq_eq_one`:
  meromorphic order zero on `Re s ≥ 1`.
* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_of_finrank_eq_one` and
  `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_of_finrank_eq_two`: degree-`1` and
  degree-`2` specializations discharging the `dedekindZetaC` hypotheses.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section

open Filter NumberField Set
open scoped NumberField Topology

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- A ray class character has squared ideal weight trivial on its good ideals if and only if
`χ ^ 2 = 1` in the character group. -/
theorem isTrivialOnGood_sq_iff_sq_eq_one (χ : RayClassCharacter 𝔪) :
    (χ.toMultiplicativeIdealWeight ^ 2).IsTrivialOnGood ↔ χ ^ 2 = 1 := by
  have hsq : χ.toMultiplicativeIdealWeight ^ 2 = (χ ^ 2).toMultiplicativeIdealWeight := by
    rw [sq, sq, toMultiplicativeIdealWeight_mul]
  constructor
  · intro h
    apply toMultiplicativeIdealWeight_injective
    ext I
    rw [← hsq]
    by_cases hI : Ideal.IsPrimeTo I 𝔪.support
    · have hval : χ.toMultiplicativeIdealWeight I ≠ 0 := by
        rw [toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hI]
        exact Units.ne_zero _
      have hgood : (χ.toMultiplicativeIdealWeight ^ 2).IsGood I := by
        rw [← MultiplicativeIdealWeight.apply_ne_zero_iff_isGood, sq,
          MultiplicativeIdealWeight.mul_apply]
        exact mul_ne_zero hval hval
      rw [h.apply_eq_one hgood, toMultiplicativeIdealWeight_one,
        MultiplicativeIdealWeight.ofBadPrimes_apply]
      simp [hI]
    · rw [sq, MultiplicativeIdealWeight.mul_apply,
        toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hI, mul_zero,
        toMultiplicativeIdealWeight_apply_of_not_isPrimeTo 1 hI]
  · intro hχ
    rw [hsq, hχ, toMultiplicativeIdealWeight_one]
    exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes 𝔪.support.finite_toSet

end TauCeti.GlobalNumberFields.RayClassCharacter

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

private theorem eqOn_toMultiplicativeIdealWeight {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
      {s | 1 < s.re}) :
    EqOn L (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
      {s | 1 < s.re} := by
  simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    RayClassCharacter.val_toUnitaryIdealWeight] using hLL

/-- **Landau's nonvanishing theorem at `s = 1` for quadratic ray class L-functions.** If
`χ ^ 2 = 1`, `dedekindZetaC K` and `heckeLFunctionC χ` continue `ζ_K` and `L(χ, ·)` holomorphically
to `Re s > 1 / 2` (with `1` punctured from `dedekindZetaC K`), and the real part of their product
does not tend to `+∞` as real `σ → (1 / 2)⁺`, then `heckeLFunctionC χ 1 ≠ 0`. -/
theorem heckeLFunctionC_one_ne_zero_of_sq_eq_one {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1)
    (hZ : DifferentiableOn ℂ (dedekindZetaC K) ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn (dedekindZetaC K) (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * heckeLFunctionC χ σ).re)
      (𝓝[>] (1 / 2 : ℝ)) atTop) :
    heckeLFunctionC χ 1 ≠ 0 :=
  MultiplicativeIdealWeight.ne_zero_one_of_eqOn_LSeries
    (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ) hZ hZζ hL
    (eqOn_toMultiplicativeIdealWeight hLL) hnot

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing for quadratic ray class L-functions**, sharp
boundary form. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one {χ : RayClassCharacter 𝔪}
    (hχ : χ ^ 2 = 1)
    (hZ : DifferentiableOn ℂ (dedekindZetaC K) ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn (dedekindZetaC K) (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * heckeLFunctionC χ σ).re)
      (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) :
    heckeLFunctionC χ s ≠ 0 :=
  MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_isTrivialOnGood_sq
    (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ) hZ hZζ hL
    (eqOn_toMultiplicativeIdealWeight hLL) hnot hs

/-- **Meromorphic order zero on `Re s ≥ 1` for quadratic ray class L-functions**, sharp boundary
form. -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_of_sq_eq_one
    {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1)
    (hZ : DifferentiableOn ℂ (dedekindZetaC K) ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn (dedekindZetaC K) (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * heckeLFunctionC χ σ).re)
      (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  MultiplicativeIdealWeight.meromorphicOrderAt_eq_zero_of_one_le_re_of_isNormTwistOnGood_sq
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr
      (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ))
    hZ hZζ hL (eqOn_toMultiplicativeIdealWeight hLL) (by simpa using hnot) hs

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing for quadratic ray class L-functions**,
continuous-at-`1 / 2` form. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one_of_continuousAt
    {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1)
    (hZ : DifferentiableOn ℂ (dedekindZetaC K) ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn (dedekindZetaC K) (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hZhalf : ContinuousAt (dedekindZetaC K) (1 / 2 : ℂ))
    (hLhalf : ContinuousAt (heckeLFunctionC χ) (1 / 2 : ℂ))
    {s : ℂ} (hs : 1 ≤ s.re) :
    heckeLFunctionC χ s ≠ 0 :=
  MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr
      (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ))
    hZ hZζ hL (eqOn_toMultiplicativeIdealWeight hLL) hZhalf (by simpa using hLhalf) hs

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing for quadratic ray class L-functions**,
whole-plane analytic form: if `dedekindZetaC K` is analytic away from `1` and `heckeLFunctionC χ`
is entire, both agreeing with their Dirichlet series on `Re s > 1`, then `heckeLFunctionC χ s ≠ 0`
for all `1 ≤ s.re`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one_of_analyticOnNhd
    {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1)
    (hZ : AnalyticOnNhd ℂ (dedekindZetaC K) {1}ᶜ)
    (hZζ : EqOn (dedekindZetaC K) (dedekindZeta K) {s | 1 < s.re})
    (hL : AnalyticOnNhd ℂ (heckeLFunctionC χ) univ)
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    {s : ℂ} (hs : 1 ≤ s.re) :
    heckeLFunctionC χ s ≠ 0 :=
  heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one_of_continuousAt hχ
    (hZ.differentiableOn.mono fun _ h ↦ h.2) hZζ
    (hL.differentiableOn.mono (subset_univ _)) hLL
    (hZ (1 / 2 : ℂ) (by norm_num)).continuousAt
    (hL (1 / 2 : ℂ) (mem_univ _)).continuousAt hs

/-- **Nonvanishing on `Re s ≥ 1` for quadratic ray class L-functions when `[K : ℚ] = 1`**,
discharging the Dedekind zeta continuation hypotheses unconditionally. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_of_finrank_eq_one (hK : Module.finrank ℚ K = 1)
    {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1)
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hLhalf : ContinuousAt (heckeLFunctionC χ) (1 / 2 : ℂ))
    {s : ℂ} (hs : 1 ≤ s.re) :
    heckeLFunctionC χ s ≠ 0 :=
  MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_finrank_eq_one hK
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr
      (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hχ))
    hL (eqOn_toMultiplicativeIdealWeight hLL) (by simpa using hLhalf) hs

/-- **Nonvanishing on `Re s ≥ 1` for quadratic ray class L-functions over quadratic fields**,
discharging the Dedekind zeta continuation hypotheses via the quadratic factorization
`ζ_K(s) = ζ(s) L(s, χ_D)`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_of_finrank_eq_two (hK : Module.finrank ℚ K = 2)
    {χ : RayClassCharacter 𝔪} (hχ : χ ^ 2 = 1)
    (hL : DifferentiableOn ℂ (heckeLFunctionC χ) {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hLhalf : ContinuousAt (heckeLFunctionC χ) (1 / 2 : ℂ))
    {s : ℂ} (hs : 1 ≤ s.re) :
    heckeLFunctionC χ s ≠ 0 :=
  heckeLFunctionC_ne_zero_of_one_le_re_of_sq_eq_one_of_continuousAt hχ
    ((analyticOnNhd_dedekindZetaC_compl_singleton hK).differentiableOn.mono fun _ h ↦ h.2)
    (fun _ hs ↦ dedekindZetaC_eq_dedekindZeta hK hs) hL hLL
    (analyticOnNhd_dedekindZetaC_compl_singleton hK (1 / 2 : ℂ) (by norm_num)).continuousAt
    hLhalf hs

end TauCeti.LFunctions
