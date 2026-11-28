/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.NumberField.DedekindZeta
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Nonvanishing

/-!
# Nonvanishing and Landau criteria for presented Hecke L-functions

The canonical function `TauCeti.LFunctions.heckeLFunctionC χ` is defined via
`TauCeti.meromorphicContinuation 1`, so it agrees with the `L`-series of `χ` on `Re s > 1` only
once a **whole-plane** meromorphic normal-form continuation `g` exists
(`TauCeti.meromorphicContinuation_eqOn`). Given that explicit whole-plane prerequisite, this file
lifts `TauCeti.GlobalNumberFields.RayClassCharacter.ne_zero_of_one_le_re` to `heckeLFunctionC χ` on
`Re s ≥ 1`, deriving boundary differentiability away from `χ ^ 2 = 1 ∧ s = 1` automatically:

* on `Re s > 1`, series agreement alone suffices via the Euler product;
* on `Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`, `heckeLFunctionC χ` agrees on `Re z > 1` with
  `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` (when `χ ≠ 1`) or the finite-Euler-factor
  Dedekind zeta continuation (when `χ = 1` and `s ≠ 1`), so identity propagation supplies local
  differentiability at `s` and `3-4-1` gives nonvanishing;
* only at `χ ^ 2 = 1 ∧ s = 1` does Landau's theorem require half-plane continuations of **both**
  `heckeLFunctionC χ` (holomorphic on `{z | 1 / 2 < z.re}`) and `ζ_K` (`Z` holomorphic on
  `{z | 1 / 2 < z.re} \ {1}`), together with the sharp boundary condition that
  `(Z σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`.

For unconditional results without supplying a whole-plane continuation of `heckeLFunctionC χ`, see
`TauCeti.NumberTheory.LFunctions.Hecke.Rat` (which identifies `heckeLFunctionC χ` over `ℚ` with
Mathlib's `DirichletCharacter.LFunction`) and
`TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Nonvanishing` (which proves `Re s ≥ 1`
nonvanishing of `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` for nontrivial `χ ≠ 1`,
requiring `[K : ℚ] = 1` only at `χ ^ 2 = 1 ∧ s = 1`).

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re`: nonvanishing on `Re s ≥ 1` for
  `heckeLFunctionC χ` given the whole-plane series-agreement witness, reserving Landau half-plane
  hypotheses on `heckeLFunctionC χ` and `ζ_K` solely for `χ ^ 2 = 1 ∧ s = 1`.
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

private theorem differentiableAt_heckeLFunctionC_of_eqOn {χ : RayClassCharacter 𝔪}
    (hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : s.re = 1) (hcase : χ ^ 2 ≠ 1 ∨ s ≠ 1) :
    DifferentiableAt ℂ (heckeLFunctionC χ) s := by
  by_cases hχ : χ = 1
  · subst hχ
    have hs1 : s ≠ 1 := hcase.resolve_left (not_not.mpr (by ext; simp))
    have him : s.im ≠ 0 := fun h ↦ hs1 (Complex.ext hs h)
    set U : Set ℂ := {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re}
    set W : Set ℂ := U ∩ {z : ℂ | 0 < s.im * z.im}
    have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hWopen : IsOpen W :=
      hUopen.inter (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im))
    have hWconv : Convex ℝ W :=
      (convex_halfSpace_re_gt _).inter fun x hx y hy a b ha hb hab ↦ by
        simp only [mem_ofPred_eq, Complex.add_im, Complex.smul_im, smul_eq_mul, mul_add]
        rw [mul_left_comm s.im a x.im, mul_left_comm s.im b y.im]
        rcases ha.eq_or_lt with rfl | ha'
        · rw [zero_mul, zero_add]
          exact mul_pos (by linarith) hy
        · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb (le_of_lt hy))
    have hsW : s ∈ W :=
      ⟨setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge, mul_self_pos.mpr him⟩
    set z₀ : ℂ := 2 + s.im * Complex.I
    have hz₀re : 1 < z₀.re := by simp [z₀]
    have hz₀W : z₀ ∈ W :=
      ⟨setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hz₀re.le, by
        simp [z₀, mul_self_pos.mpr him]⟩
    obtain ⟨G, hG, hGeq⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K 𝔪.support
    set ρ : ℂ := dedekindZeta_residue K *
      ∏ P ∈ 𝔪.support, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ))
    set T : ℂ → ℂ := fun z ↦ G z + ρ / (z - 1)
    have hTdiff : DifferentiableOn ℂ T W :=
      (hG.mono inter_subset_left).add
        ((differentiableOn_const ρ).div (differentiableOn_id.sub_const 1) fun z hz ↦
          sub_ne_zero.mpr fun h ↦ by have := congrArg Complex.im h; simp_all [W])
    have hEq : EqOn (heckeLFunctionC (1 : RayClassCharacter 𝔪)) T W := by
      refine MeromorphicNFOn.eqOn_of_isPreconnected
        (fun z _ ↦ meromorphicNFOn_heckeLFunctionC 1 (Set.mem_univ z))
        (hTdiff.analyticOnNhd hWopen).meromorphicNFOn hWconv.isPreconnected hz₀W ?_
      refine nhdsWithin_le_nhds ?_
      have hre_open : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hre_open.mem_nhds hz₀re] with z (hz : 1 < z.re)
      dsimp only [T]
      rw [hLL hz, hGeq z hz, UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
        RayClassCharacter.val_toUnitaryIdealWeight,
        RayClassCharacter.toMultiplicativeIdealWeight_one, sub_add_cancel]
    exact (hTdiff.differentiableAt (hWopen.mem_nhds hsW)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hWopen.mem_nhds hsW) hEq)
  · set U : Set ℂ := {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re}
    have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight) U :=
      differentiableOn_continuedLFunctionOfWeight
        (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ)
    have hz₀re : (1 : ℝ) < (2 : ℂ).re := by norm_num
    have hz₀U : (2 : ℂ) ∈ U := setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hz₀re.le
    have hEq : EqOn (heckeLFunctionC χ) (continuedLFunctionOfWeight χ.toUnitaryIdealWeight) U := by
      refine MeromorphicNFOn.eqOn_of_isPreconnected
        (fun z _ ↦ meromorphicNFOn_heckeLFunctionC χ (Set.mem_univ z))
        (hdiff.analyticOnNhd hUopen).meromorphicNFOn (convex_halfSpace_re_gt _).isPreconnected
        hz₀U ?_
      refine nhdsWithin_le_nhds ?_
      have hre_open : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hre_open.mem_nhds hz₀re] with z (hz : 1 < z.re)
      rw [hLL hz, continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hz]
    exact (hdiff.differentiableAt
      (hUopen.mem_nhds (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge))
      ).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
      (hUopen.mem_nhds (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge)) hEq)

/-- **Nonvanishing criterion on `Re s ≥ 1` for presented Hecke L-functions.**
Suppose the `L`-series of `χ` admits a whole-plane meromorphic normal-form continuation `g` (making
`heckeLFunctionC χ` agree with the `L`-series on `{z | 1 < z.re}`). Then `heckeLFunctionC χ s ≠ 0`
for any `s` with `1 ≤ s.re` unconditionally away from `χ ^ 2 = 1 ∧ s = 1`, and at
`χ ^ 2 = 1 ∧ s = 1` given Landau half-plane continuations of both `ζ_K` (`Z` holomorphic on
`{z | 1 / 2 < z.re} \ {1}`) and `heckeLFunctionC χ` (holomorphic on `{z | 1 / 2 < z.re}`) such
that `(Z σ * heckeLFunctionC χ σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`.

For an arbitrary continuation `L` with branch-specific hypotheses in place of the whole-plane
witness `hcont`, use `TauCeti.GlobalNumberFields.RayClassCharacter.ne_zero_of_one_le_re`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re {χ : RayClassCharacter 𝔪}
    (hcont : ∃ g : ℂ → ℂ, MeromorphicNFOn g univ ∧
      EqOn g (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
        {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * heckeLFunctionC χ σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    heckeLFunctionC χ s ≠ 0 := by
  have hLL : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re} := by
    rw [heckeLFunctionC_def]
    exact meromorphicContinuation_eqOn hcont
  exact χ.ne_zero_of_one_le_re hLL hs
    (fun hseq hcase ↦ differentiableAt_heckeLFunctionC_of_eqOn hLL hseq hcase) hlandau

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
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ (heckeLFunctionC χ) {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * heckeLFunctionC χ σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  ((meromorphicNFOn_heckeLFunctionC χ) (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr
    (heckeLFunctionC_ne_zero_of_one_le_re hcont hs hlandau)

end TauCeti.LFunctions
