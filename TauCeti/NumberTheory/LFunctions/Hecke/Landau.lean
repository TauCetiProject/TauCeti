/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.NumberTheory.LFunctions.Hecke.ChangeModulus
import TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Nonvanishing and Landau criteria for presented Hecke L-functions

The canonical function `TauCeti.LFunctions.heckeLFunctionC χ` is defined via
`TauCeti.meromorphicContinuation 1`, so it agrees with the `L`-series of `χ` on `Re s > 1` only
once a **whole-plane** meromorphic normal-form continuation `g` exists
(`TauCeti.meromorphicContinuation_eqOn`). Given that explicit whole-plane prerequisite, this file
lifts `TauCeti.GlobalNumberFields.RayClassCharacter.ne_zero_of_one_le_re` to `heckeLFunctionC χ` on
`Re s ≥ 1`, deriving boundary differentiability away from `χ ^ 2 = 1 ∧ s = 1` automatically:

* on `Re s > 1`, series agreement alone suffices via the Euler product;
* on `Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`, `heckeLFunctionC χ` agrees with
  `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` throughout `Re z > 1 - 1 / [K : ℚ]`
  (when `χ ≠ 1`, via `heckeLFunctionC_eqOn_continuedLFunctionOfWeight`) or agrees as a punctured
  germ with `dedekindZetaC K * (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔪` (when
  `χ = 1` and `s ≠ 1`, via `heckeLFunctionC_induced_eventuallyEq` and
  `heckeLFunctionC_one_modulus_one`), supplying local differentiability at `s` so `3-4-1` gives
  nonvanishing;
* only at `χ ^ 2 = 1 ∧ s = 1` does Landau's theorem require holomorphy of `heckeLFunctionC χ` on
  `{z | 1 / 2 < z.re}` together with the sharp boundary condition that
  `(dedekindZetaC K σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`
  (supplying `dedekindZetaC K` internally).

For unconditional results without supplying a whole-plane continuation of `heckeLFunctionC χ`, see
`TauCeti.NumberTheory.LFunctions.Hecke.Rat` (which identifies `heckeLFunctionC χ` over `ℚ` with the
meromorphic normal form of Mathlib's `DirichletCharacter.LFunction`) and
`TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing` (which proves `Re s ≥ 1` nonvanishing of
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` for nontrivial `χ ≠ 1`, requiring `[K : ℚ] = 1`
only at `χ ^ 2 = 1 ∧ s = 1`).

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_eqOn_continuedLFunctionOfWeight`: for `χ ≠ 1`, series
  agreement on `Re z > 1` extends `heckeLFunctionC χ` to agree with
  `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` on `Re z > 1 - 1 / [K : ℚ]`.
* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re`: nonvanishing on `Re s ≥ 1` for
  `heckeLFunctionC χ` given the whole-plane series-agreement witness, reserving Landau half-plane
  hypotheses on `heckeLFunctionC χ` solely for `χ ^ 2 = 1 ∧ s = 1`.
* `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re`: meromorphic order
  zero on `Re s ≥ 1` for `heckeLFunctionC χ` under the same hypotheses.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* The Dirichlet-character prototype is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao), which also supplies the unconditional nonvanishing over `ℚ` in
  `TauCeti.NumberTheory.LFunctions.Hecke.Rat`.
-/

public section

open Filter IsDedekindDomain NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Comparison with the cancellation continuation for any modulus.** For a nontrivial ray class
character `χ ≠ 1`, if `heckeLFunctionC χ` agrees with the defining `L`-series on `Re z > 1`, then
it agrees with `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` throughout the open half-plane
`Re z > 1 - 1 / [K : ℚ]`. -/
theorem heckeLFunctionC_eqOn_continuedLFunctionOfWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    EqOn (heckeLFunctionC χ) (continuedLFunctionOfWeight χ.toUnitaryIdealWeight)
      {z | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} := by
  set U : Set ℂ := {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight) U :=
    differentiableOn_continuedLFunctionOfWeight
      (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ)
  have hz₀U : (2 : ℂ) ∈ U :=
    setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (by norm_num)
  refine MeromorphicNFOn.eqOn_of_isPreconnected
    (fun z _ ↦ meromorphicNFOn_heckeLFunctionC χ (Set.mem_univ z))
    (hdiff.analyticOnNhd hUopen).meromorphicNFOn (convex_halfSpace_re_gt _).isPreconnected
    hz₀U ?_
  refine nhdsWithin_le_nhds ?_
  have hre_open : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hre_open.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z (hz : 1 < z.re)
  rw [hLL hz, continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hz]

private theorem differentiableAt_heckeLFunctionC_of_eqOn {χ : RayClassCharacter 𝔪}
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : s.re = 1) (hcase : χ ^ 2 ≠ 1 ∨ s ≠ 1) :
    DifferentiableAt ℂ (heckeLFunctionC χ) s := by
  by_cases hχ : χ = 1
  · subst hχ
    have hs1 : s ≠ 1 := hcase.resolve_left (not_not.mpr (by ext; simp))
    have heq : heckeLFunctionC (1 : RayClassCharacter 𝔪) =ᶠ[𝓝[≠] s]
        fun z ↦ dedekindZetaC K z *
          (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔪 z := by
      simpa only [map_one, heckeLFunctionC_one_modulus_one] using
        heckeLFunctionC_induced_eventuallyEq (Modulus.one_dvd 𝔪)
          (1 : RayClassCharacter (Modulus.one K)) s
    have hana : AnalyticAt ℂ
        (fun z ↦ dedekindZetaC K z *
          (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔪 z) s :=
      (analyticAt_dedekindZetaC K hs1).mul
        (((1 : RayClassCharacter (Modulus.one K)).differentiable_eulerCorrection 𝔪).analyticAt s)
    exact hana.differentiableAt.congr_of_eventuallyEq
      (((meromorphicNFOn_heckeLFunctionC (1 : RayClassCharacter 𝔪)
        (Set.mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hana.meromorphicNFAt).mp heq)
  · have hUopen : IsOpen {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hsU : {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} ∈ 𝓝 s :=
      hUopen.mem_nhds (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge)
    exact ((differentiableOn_continuedLFunctionOfWeight
      (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ)).differentiableAt hsU
      ).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hsU (heckeLFunctionC_eqOn_continuedLFunctionOfWeight hχ hLL))

/-- **Nonvanishing criterion on `Re s ≥ 1` for presented Hecke L-functions.**
Suppose the `L`-series of `χ` admits a whole-plane meromorphic normal-form continuation `g` (making
`heckeLFunctionC χ` agree with the `L`-series on `{z | 1 < z.re}`). Then `heckeLFunctionC χ s ≠ 0`
for any `s` with `1 ≤ s.re` unconditionally away from `χ ^ 2 = 1 ∧ s = 1`, and at
`χ ^ 2 = 1 ∧ s = 1` given holomorphy of `heckeLFunctionC χ` on `{z | 1 / 2 < z.re}` together with
the sharp boundary condition that `(dedekindZetaC K σ * heckeLFunctionC χ σ).re` does not tend to
`+∞` as real `σ → (1 / 2)⁺`.

For an arbitrary continuation `L` with branch-specific hypotheses in place of the whole-plane
witness `hcont`, use `TauCeti.GlobalNumberFields.RayClassCharacter.ne_zero_of_one_le_re`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re {χ : RayClassCharacter 𝔪}
    (hcont : ∃ g : ℂ → ℂ, MeromorphicNFOn g univ ∧
      EqOn g (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hlandau : χ ^ 2 = 1 → s = 1 →
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * heckeLFunctionC χ σ).re)
        (𝓝[>] (1 / 2 : ℝ)) atTop) :
    heckeLFunctionC χ s ≠ 0 := by
  have hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re} := by
    rw [heckeLFunctionC_def]
    exact meromorphicContinuation_eqOn hcont
  refine χ.ne_zero_of_one_le_re hLL hs
    (fun hseq hcase ↦ differentiableAt_heckeLFunctionC_of_eqOn hLL hseq hcase)
    fun hsq hs1 ↦ ?_
  obtain ⟨hL, hnot⟩ := hlandau hsq hs1
  exact ⟨dedekindZetaC K, fun z hz ↦ (analyticAt_dedekindZetaC K hz.2).differentiableWithinAt,
    fun z hz ↦ dedekindZetaC_eq_dedekindZeta K hz, hL, hnot⟩

/-- **Meromorphic order zero on `Re s ≥ 1` for presented Hecke L-functions.** Under the
whole-plane series-agreement witness and Landau hypothesis of
`heckeLFunctionC_ne_zero_of_one_le_re`, `meromorphicOrderAt (heckeLFunctionC χ) s = 0`.

For an arbitrary continuation `L` with branch-specific hypotheses in place of `hcont`, see
`TauCeti.GlobalNumberFields.RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re`. -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re {χ : RayClassCharacter 𝔪}
    (hcont : ∃ g : ℂ → ℂ, MeromorphicNFOn g univ ∧
      EqOn g (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hlandau : χ ^ 2 = 1 → s = 1 →
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (dedekindZetaC K σ * heckeLFunctionC χ σ).re)
        (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  ((meromorphicNFOn_heckeLFunctionC χ) (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr
    (heckeLFunctionC_ne_zero_of_one_le_re hcont hs hlandau)

end TauCeti.LFunctions
