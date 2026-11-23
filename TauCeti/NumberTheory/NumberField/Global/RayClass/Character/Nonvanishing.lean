/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation

/-!
# Nonvanishing on `Re s ≥ 1` for ray class L-functions

For a nontrivial ray class character `χ` of a modulus `𝔪` of a number field `K`, the unitary
ideal weight `χ.toUnitaryIdealWeight` has cancellation
(`TauCeti.GlobalNumberFields.RayClassCharacter.hasCancellation_toUnitaryIdealWeight`), so its
continued L-function `TauCeti.continuedLFunctionOfWeight χ.toUnitaryIdealWeight` is holomorphic
on `Re s > 1 - 1 / [K : ℚ]`.

On `Re s ≥ 1`, `continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re` proves
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0` for any `χ ≠ 1`: on `Re s > 1` by the
Euler product, when `χ ^ 2 ≠ 1` by `3-4-1` and cancellation for `χ ^ 2`, when `χ ^ 2 = 1` and
`s ≠ 1` by `3-4-1` (`TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq`), and in
the remaining case `χ ^ 2 = 1 ∧ s = 1` when `[K : ℚ] = 1` by Landau's theorem
(`TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one`).

For an arbitrary number field `K` and any continuation `L : ℂ → ℂ` agreeing with the `L`-series
of `χ` on `Re z > 1`, `ne_zero_of_one_le_re` and `meromorphicOrderAt_eq_zero_of_one_le_re` give
pointwise nonvanishing and meromorphic-order-zero criteria on `Re s ≥ 1`: on `Re s > 1` only series
agreement is needed; on `Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`, `3-4-1` requires only
differentiability of `L` at `s` (together with a continuous continuation of `L(χ ^ 2, ·)` at
`2 * s - 1` when `χ ^ 2 ≠ 1`); and only at `χ ^ 2 = 1 ∧ s = 1` do they ask for a holomorphic
continuation `Z` of `ζ_K` on `{z | 1 / 2 < z.re} \ {1}`, holomorphy of `L` on
`{z | 1 / 2 < z.re}`, and the sharp boundary condition that `(Z σ * L σ).re` does not tend to
`+∞` as real `σ → (1 / 2)⁺`.

## Main results

* `ne_zero_of_one_le_re` and `meromorphicOrderAt_eq_zero_of_one_le_re` (in
  `TauCeti.GlobalNumberFields.RayClassCharacter`): nonvanishing and meromorphic-order-zero
  criteria on `Re s ≥ 1` for an arbitrary continuation `L`, reserving Landau half-plane data on
  `L`, `Z`, and `(Z σ * L σ).re` for the exceptional case `χ ^ 2 = 1 ∧ s = 1`.
* `continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re` (in
  `TauCeti.GlobalNumberFields.RayClassCharacter`): nonvanishing on `Re s ≥ 1` for `χ ≠ 1`,
  requiring `[K : ℚ] = 1` only when `χ ^ 2 = 1 ∧ s = 1`.

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

open Filter NumberField Set TauCeti
open scoped NumberField Topology

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Pointwise nonvanishing criterion on `Re s ≥ 1` for ray class L-functions.**
For any `L : ℂ → ℂ` agreeing with the `L`-series of `χ` on `{z | 1 < z.re}` and any `s` with
`1 ≤ s.re`, `L s ≠ 0` under branch-minimal hypotheses:
* on `1 < s.re`, series agreement alone suffices by the Euler product;
* on `s.re = 1` with `χ ^ 2 = 1` and `s ≠ 1`, complex differentiability of `L` at `s` suffices by
  `3-4-1`;
* on `s.re = 1` with `χ ^ 2 ≠ 1`, complex differentiability of `L` at `s` and a continuation of
  `L(χ ^ 2, ·)` continuous at `2 * s - 1` suffice by `3-4-1`;
* at `χ ^ 2 = 1 ∧ s = 1`, Landau's theorem applies given a continuation `Z` of `dedekindZeta K`
  holomorphic on `{z | 1 / 2 < z.re} \ {1}`, holomorphy of `L` on `{z | 1 / 2 < z.re}`, and the
  sharp boundary condition that `(Z σ * L σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`.
-/
theorem ne_zero_of_one_le_re {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re) (hLs : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → DifferentiableAt ℂ L s)
    (hsq_ne : s.re = 1 → χ ^ 2 ≠ 1 → ∃ L₂ : ℂ → ℂ, ContinuousAt L₂ (2 * s - 1) ∧
      EqOn L₂
        (LSeries (normCoeff K (χ ^ 2).toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    L s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · rw [hLL hsgt, UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, val_toUnitaryIdealWeight]
    refine χ.toMultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm ?_
    simpa [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, val_toUnitaryIdealWeight] using
      summable_idealTerm_of_unitary_of_one_lt_re χ.toUnitaryIdealWeight hsgt
  · by_cases hsq : χ ^ 2 = 1
    · have hLL' : EqOn L
          (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
          {z | 1 < z.re} := by
        simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
          val_toUnitaryIdealWeight] using hLL
      exact MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_isTrivialOnGood_sq
        (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hsq) hLL' hs
        (fun hre hs1 ↦ hLs hre (.inr hs1)) (hlandau hsq)
    · obtain ⟨L₂, hL₂cont, hL₂eq⟩ := hsq_ne hseq.symm hsq
      have hpow : χ.toUnitaryIdealWeight ^ 2 = (χ ^ 2).toUnitaryIdealWeight := by
        rw [sq, sq, toUnitaryIdealWeight_mul]
      exact χ.toUnitaryIdealWeight.ne_zero_of_eqOn_LSeries hseq.symm
        (hLs hseq.symm (.inl hsq)) hLL hL₂cont fun z hz ↦ by rw [hpow]; exact hL₂eq hz

/-- **Pointwise meromorphic order zero on `Re s ≥ 1` for ray class L-functions.** Under the
branch-minimal hypotheses of `ne_zero_of_one_le_re` together with meromorphic normal form at `s`
when `s.re = 1` and `χ ^ 2 ≠ 1 ∨ s ≠ 1`, `meromorphicOrderAt L s = 0`. -/
theorem meromorphicOrderAt_eq_zero_of_one_le_re {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re) (hLM : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → MeromorphicNFAt L s)
    (hLs : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → DifferentiableAt ℂ L s)
    (hsq_ne : s.re = 1 → χ ^ 2 ≠ 1 → ∃ L₂ : ℂ → ℂ, ContinuousAt L₂ (2 * s - 1) ∧
      EqOn L₂
        (LSeries (normCoeff K (χ ^ 2).toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt L s = 0 := by
  have hne : L s ≠ 0 := ne_zero_of_one_le_re hLL hs hLs hsq_ne hlandau
  have hnf : MeromorphicNFAt L s := by
    rcases hs.lt_or_eq with hsgt | hseq
    · have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hana :
          AnalyticAt ℂ
            (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) s :=
        analyticOnNhd_LSeries_of_unitary χ.toUnitaryIdealWeight s hsgt
      exact (hana.congr
        ((Filter.eventuallyEq_of_mem (hopen.mem_nhds hsgt) hLL).symm)).meromorphicNFAt
    · by_cases hboth : χ ^ 2 = 1 ∧ s = 1
      · obtain ⟨_, _, _, hL, _⟩ := hlandau hboth.1 hboth.2
        have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
          isOpen_lt continuous_const Complex.continuous_re
        exact (hL.analyticAt
          (hopen.mem_nhds (by simp only [Set.mem_ofPred_eq]; linarith))).meromorphicNFAt
      · exact hLM hseq.symm (not_and_or.mp hboth)
  exact hnf.meromorphicOrderAt_eq_zero_iff.mpr hne

/-- **Nonvanishing on `Re s ≥ 1` of the cancellation-continued ray class L-function.**
For any ray class character `χ` of any modulus `𝔪`,
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0` for every `s` with `1 ≤ s.re` provided
`χ ≠ 1` on `Re s = 1`, requiring `[K : ℚ] = 1` only in the exceptional case `χ ^ 2 = 1 ∧ s = 1`
(via Landau's theorem). On `Re s > 1`, nonvanishing holds for every `χ` (including `χ = 1`) via
the Euler product. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re
    {χ : RayClassCharacter 𝔪} {s : ℂ} (hχ : s.re = 1 → χ ≠ 1)
    (hK : χ ^ 2 = 1 → s = 1 → Module.finrank ℚ K = 1) (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re _ hsgt
  · have hχne : χ ≠ 1 := hχ hseq.symm
    by_cases hsq : χ ^ 2 = 1
    · have htriv : (χ.toUnitaryIdealWeight ^ 2).val.IsTrivialOnGood := by
        rw [UnitaryIdealWeight.val_pow, val_toUnitaryIdealWeight]
        exact χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hsq
      rcases eq_or_ne s 1 with rfl | hs1
      · exact continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one
          (hK hsq rfl) (hasCancellation_toUnitaryIdealWeight hχne) htriv hs
      · exact continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq
          (hasCancellation_toUnitaryIdealWeight hχne) htriv hs hs1
    · have hpow : χ.toUnitaryIdealWeight ^ 2 = (χ ^ 2).toUnitaryIdealWeight := by
        rw [sq, sq, toUnitaryIdealWeight_mul]
      exact continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq
        (hasCancellation_toUnitaryIdealWeight hχne)
        (hpow ▸ hasCancellation_toUnitaryIdealWeight hsq) hs

end TauCeti.GlobalNumberFields.RayClassCharacter
