/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing.Basic
import TauCeti.Analysis.Meromorphic.Identity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Nonvanishing
import TauCeti.NumberTheory.LFunctions.Hecke.EulerCorrection
import TauCeti.NumberTheory.NumberField.DedekindZeta.Basic

/-!
# Arbitrary-continuation boundary nonvanishing for ray class L-functions

For an arbitrary number field `K`, modulus `𝔪 : Modulus K`, ray class character
`χ : RayClassCharacter 𝔪`, and continuation `L : ℂ → ℂ` agreeing with the `L`-series of `χ` on
`Re z > 1`, `RayClassCharacter.ne_zero_of_one_le_re` and
`RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re` give pointwise nonvanishing and
meromorphic-order-zero criteria on `Re s ≥ 1`:

* on `Re s > 1`, series agreement alone suffices by the Euler product;
* on `Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`, comparison with the analytic nonvanishing model
  (`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` when `χ ≠ 1`, or `dedekindZetaC K` times the
  trivial-modulus Euler correction when `χ = 1`) requires only `ContinuousAt L s` for
  nonvanishing and `MeromorphicAt L s` (via punctured-germ identity) for meromorphic order zero;
* only at `χ ^ 2 = 1 ∧ s = 1` do they ask for holomorphy of `L` on `{z | 1 / 2 < z.re}` and the
  sharp boundary condition that `(dedekindZetaC K σ * L σ).re` does not tend to `+∞` as real
  `σ → (1 / 2)⁺` (supplying `dedekindZetaC K` internally).

## Main results

* `RayClassCharacter.ne_zero_of_one_le_re` and
  `RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re`: nonvanishing and
  meromorphic-order-zero criteria on `Re s ≥ 1` for an arbitrary continuation `L`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
-/

public section

open Complex Filter NumberField Set TauCeti TauCeti.LFunctions
open scoped NumberField Topology

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- Shared analytic nonvanishing model and right-half-plane series agreement on `Re s = 1` away
from `χ ^ 2 = 1 ∧ s = 1`:
* `dedekindZetaC K * (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔪` when `χ = 1`,
* `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` when `χ ≠ 1`. -/
private theorem exists_analyticAt_ne_zero_eqOn_of_eqOn_LSeries
    {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : s.re = 1) (hcase : χ ^ 2 ≠ 1 ∨ s ≠ 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F s ∧ F s ≠ 0 ∧ EqOn L F {z | 1 < z.re} := by
  by_cases hχ : χ = 1
  · subst hχ
    have hs1 : s ≠ 1 := hcase.resolve_left (not_not.mpr (by ext; simp))
    set F : ℂ → ℂ := fun z ↦
      dedekindZetaC K z * (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔪 z
    have hζ : AnalyticAt ℂ (dedekindZetaC K) s := analyticAt_dedekindZetaC K hs1
    have hF : AnalyticAt ℂ F s :=
      hζ.mul (((1 : RayClassCharacter (Modulus.one K)).differentiable_eulerCorrection
        𝔪).analyticAt s)
    have hFne : F s ≠ 0 := mul_ne_zero
      (dedekindZetaC_ne_zero_of_one_le_re K hs.ge hs1)
      ((1 : RayClassCharacter (Modulus.one K)).eulerCorrection_ne_zero 𝔪 (by norm_num [hs]))
    have hLF : EqOn L F {z | 1 < z.re} := fun z hz ↦ by
      dsimp only [F]
      rw [hLL hz]
      conv_lhs => rw [← map_one (induced (Modulus.one_dvd 𝔪))]
      rw [RayClassCharacter.LSeries_induced (Modulus.one_dvd 𝔪) 1 hz,
        RayClassCharacter.toUnitaryIdealWeight_one,
        UnitaryIdealWeight.toIdealArithmeticFunction_one,
        ← dedekindZeta_eq_LSeries_normCoeff_one, dedekindZetaC_eq_dedekindZeta K hz]
    exact ⟨F, hF, hFne, hLF⟩
  · set F : ℂ → ℂ := continuedLFunctionOfWeight χ.toUnitaryIdealWeight
    have hUopen : IsOpen {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hF : AnalyticAt ℂ F s :=
      ((differentiableOn_continuedLFunctionOfWeight
        (hasCancellation_toUnitaryIdealWeight hχ)).analyticOnNhd hUopen) s
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge)
    have hFne : F s ≠ 0 := continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero hχ hs.ge hcase
    have hLF : EqOn L F {z | 1 < z.re} := fun z hz ↦ by
      dsimp only [F]
      rw [hLL hz, continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hz]
    exact ⟨F, hF, hFne, hLF⟩

/-- **Pointwise nonvanishing criterion on `Re s ≥ 1` for ray class L-functions.**
For any `L : ℂ → ℂ` agreeing with the `L`-series of `χ` on `{z | 1 < z.re}` and any `s` with
`1 ≤ s.re`, `L s ≠ 0` under branch-minimal hypotheses:
* on `1 < s.re`, series agreement alone suffices by the Euler product;
* on `s.re = 1` away from `χ ^ 2 = 1 ∧ s = 1`, continuity of `L` at `s` suffices by right-half-plane
  limit comparison against the analytic nonvanishing model;
* at `χ ^ 2 = 1 ∧ s = 1`, Landau's theorem applies (supplying `dedekindZetaC K` internally) given
  holomorphy of `L` on `{z | 1 / 2 < z.re}` and the sharp boundary condition that
  `(dedekindZetaC K σ * L σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`. -/
theorem ne_zero_of_one_le_re {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re) (hLs : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → ContinuousAt L s)
    (hlandau : χ ^ 2 = 1 → s = 1 →
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    L s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · rw [hLL hsgt, ← continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hsgt]
    exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re χ.toUnitaryIdealWeight hsgt
  · by_cases hboth : χ ^ 2 = 1 ∧ s = 1
    · have hLL' : EqOn L
          (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
          {z | 1 < z.re} := by
        simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
          val_toUnitaryIdealWeight] using hLL
      exact MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_isTrivialOnGood_sq
        (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hboth.1) hLL' hs
        (fun _ hs1 ↦ absurd hboth.2 hs1) fun _ ↦ by
          obtain ⟨hL, hnot⟩ := hlandau hboth.1 hboth.2
          exact ⟨dedekindZetaC K,
            fun _ hz ↦ (analyticAt_dedekindZetaC K hz.2).differentiableWithinAt,
            fun _ hz ↦ dedekindZetaC_eq_dedekindZeta K hz, hL, hnot⟩
    · have hcase : χ ^ 2 ≠ 1 ∨ s ≠ 1 := not_and_or.mp hboth
      obtain ⟨F, hF, hFne, hLF⟩ :=
        exists_analyticAt_ne_zero_eqOn_of_eqOn_LSeries hLL hseq.symm hcase
      have hnebot : (𝓝[{z : ℂ | 1 < z.re}] s).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
        intro ε hε
        refine ⟨s + (ε / 2 : ℝ), ?_, ?_⟩
        · simp [← hseq]; linarith
        · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (half_pos hε)]
          linarith
      have hL_eq_F : L s = F s := tendsto_nhds_unique_of_eventuallyEq
        ((hLs hseq.symm hcase).tendsto.mono_left nhdsWithin_le_nhds)
        (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun _ hz ↦ hLF hz)
      rwa [hL_eq_F]

/-- **Pointwise meromorphic order zero on `Re s ≥ 1` for ray class L-functions.** Under series
agreement on `Re z > 1`, `MeromorphicAt L s` away from `χ ^ 2 = 1 ∧ s = 1`, and the Landau
conditions (with `dedekindZetaC K` supplied internally) at `χ ^ 2 = 1 ∧ s = 1`,
`meromorphicOrderAt L s = 0`. -/
theorem meromorphicOrderAt_eq_zero_of_one_le_re {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re) (hLM : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → MeromorphicAt L s)
    (hlandau : χ ^ 2 = 1 → s = 1 →
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt L s = 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · exact (χ.toUnitaryIdealWeight.analyticAt_of_eqOn_LSeries hLL hsgt
      ).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr <|
      ne_zero_of_one_le_re hLL hs (fun hre _ ↦ absurd hre hsgt.ne')
        (fun _ hs1 ↦ absurd hsgt.ne' (by simp [hs1]))
  · by_cases hboth : χ ^ 2 = 1 ∧ s = 1
    · obtain ⟨hL, _⟩ := hlandau hboth.1 hboth.2
      have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have hne : L s ≠ 0 := ne_zero_of_one_le_re hLL hs
        (fun _ hcase ↦ hcase.elim (absurd hboth.1) (absurd hboth.2))
        hlandau
      exact (hL.analyticAt
        (hopen.mem_nhds (by simp only [mem_ofPred_eq]; linarith))).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hne
    · have hcase : χ ^ 2 ≠ 1 ∨ s ≠ 1 := not_and_or.mp hboth
      obtain ⟨F, hF, hFne, hLF⟩ :=
        exists_analyticAt_ne_zero_eqOn_of_eqOn_LSeries hLL hseq.symm hcase
      have hgerm : L =ᶠ[𝓝[≠] s] F :=
        (hLM hseq.symm hcase).eventuallyEq_nhdsNE_of_eventuallyEq_re_gt hF.meromorphicAt
          (eventually_nhdsWithin_of_forall fun _ hz ↦ hLF (hseq.symm ▸ hz))
      rw [meromorphicOrderAt_congr hgerm]
      exact hF.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hFne

end TauCeti.GlobalNumberFields.RayClassCharacter
