/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.ModularForms.LevelOne.Eigenbasis
public import TauCeti.NumberTheory.ModularForms.LFunction.Basic

import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.NumberTheory.ArithmeticFunction.Sigma.LSeries
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.LFunction.Abscissa
import TauCeti.NumberTheory.ModularForms.LFunction.EulerProduct

/-!
# L-functions of level-one modular forms

At level one (`𝒮ℒ`, where `ModularGroup.S ∈ 𝒮ℒ` and the cusp at `∞` has strict width `1`), two
complementary phenomena govern `ModularForm.L`:

* For each `f : Newform 1 k`, the canonical Hecke eigenbasis vector
  `TauCeti.levelOneNewformBasis k f` of `CuspForm 𝒮ℒ k` transports `f.toCuspForm` along
  `(Gamma1 1).map (mapGL ℝ) = 𝒮ℒ` without changing the underlying function on `ℍ`. On the
  Euler-product half-plane `Re s > k / 2 + 1`, `ModularForm.L` coincides with the `q`-expansion
  `LSeries` and does not vanish (`TauCeti.L_levelOneNewformBasis_ne_zero`).
* Because `ModularGroup.S` fixes every level-one modular form under the slash action, the possible
  simple pole of `ModularForm.L hk f` at the weight `k` is controlled directly by the constant
  `q`-expansion coefficient `(qExpansion 1 f).coeff 0`
  (`TauCeti.meromorphicOrderAt_L_levelOne_k`, `TauCeti.analyticAt_L_levelOne_iff`,
  `TauCeti.differentiable_L_levelOne_iff`). In particular, the Eisenstein series `E₄` has L-series
  `240 ζ(s) ζ(s - 3)` on `Re s > 4` (`TauCeti.LSeries_qExpansion_coeff_E₄`, `TauCeti.L_E₄_eq`),
  exact abscissa of absolute convergence `4` (`TauCeti.abscissaOfAbsConv_qExpansion_coeff_E₄`), and
  a simple pole at `s = 4` (`TauCeti.meromorphicOrderAt_L_E₄_four`), witnessing both the sharpness
  of the congruence abscissa bound `k` and the obstruction to entire continuation for non-cuspidal
  forms.

## Main results

* `TauCeti.L_levelOneNewformBasis_ne_zero`: for `0 < k`, `f : Newform 1 k`, and
  `(k : ℝ) / 2 + 1 < s.re`, `ModularForm.L hk (levelOneNewformBasis k f) s ≠ 0`.
* `TauCeti.meromorphicOrderAt_L_levelOne_k`, `TauCeti.analyticAt_L_levelOne_iff`,
  `TauCeti.differentiable_L_levelOne_iff`: at level one, `ModularForm.L hk f` is entire if and only
  if `(qExpansion 1 f).coeff 0 = 0`, and otherwise has a simple pole at `s = k`.
* `TauCeti.LSeries_qExpansion_coeff_E₄`, `TauCeti.L_E₄_eq`: on `Re s > 4`, both the coefficient
  `LSeries` of `E₄` and `ModularForm.L hk E₄ s` equal `240 * riemannZeta s * riemannZeta (s - 3)`.
* `TauCeti.abscissaOfAbsConv_qExpansion_coeff_E₄`: the coefficient `LSeries` of `E₄` has abscissa
  of absolute convergence `4`.
* `TauCeti.meromorphicOrderAt_L_E₄_four`, `TauCeti.not_analyticAt_L_E₄_four`,
  `TauCeti.not_differentiable_L_E₄`: `ModularForm.L hk E₄` has a simple pole at `4` and is not
  entire.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Propositions 5.8.5 and 5.9.1, and §5.9.
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup UpperHalfPlane
open scoped ArithmeticFunction.sigma LSeries.notation MatrixGroups

namespace TauCeti

/-- On the Euler-product half-plane `Re s > k / 2 + 1`, `ModularForm.L` of the level-one newform
basis vector `levelOneNewformBasis k f` does not vanish. -/
theorem L_levelOneNewformBasis_ne_zero {k : ℤ} (hk : 0 < k) (f : Newform 1 k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    ModularForm.L hk (levelOneNewformBasis k f) s ≠ 0 := by
  have hwidth : Subgroup.strictWidthInfty 𝒮ℒ = 1 := by
    rw [← Gamma1_one_map_eq_SL, strictWidthInfty_Gamma1]
  have hL := CuspForm.LSeries_qExpansion_coeff_eq hk (levelOneNewformBasis k f) hs
  rw [hwidth, Complex.ofReal_one, Complex.one_cpow, one_mul, coe_levelOneNewformBasis_apply] at hL
  rw [← hL]
  exact f.LSeries_ne_zero_of_lt_re (by linarith)

/-- At level one, `ModularGroup.S ∈ 𝒮ℒ` fixes `f` under the slash action, so
`valueAtInfty (ModularForm.translate f ModularGroup.S)` is the constant `q`-expansion coefficient
`(qExpansion 1 f).coeff 0`. -/
private lemma valueAtInfty_translate_S_levelOne {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F 𝒮ℒ k] (f : F) :
    valueAtInfty (ModularForm.translate f ModularGroup.S) = (qExpansion 1 f).coeff 0 := by
  have hS : (ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩
  have hcoe : (ModularForm.translate f ModularGroup.S : ℍ → ℂ) = f :=
    (ModularForm.coe_translate f ModularGroup.S).trans
      (SlashInvariantForm.slash_action_eqn f _ hS)
  rw [hcoe]
  exact (qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)).symm

/-- A positive-weight level-one modular form with nonzero constant `q`-expansion coefficient has a
simple pole of `ModularForm.L hk f` at `s = k`. -/
theorem meromorphicOrderAt_L_levelOne_k {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F 𝒮ℒ k] (f : F) (h0 : (qExpansion 1 f).coeff 0 ≠ 0) :
    meromorphicOrderAt (ModularForm.L hk f) k = (-1 : ℤ) := by
  refine ModularForm.meromorphicOrderAt_L_k hk f ?_
  rwa [valueAtInfty_translate_S_levelOne]

/-- At level one, `ModularForm.L hk f` is analytic at `s` if and only if `s ≠ k` or the constant
`q`-expansion coefficient `(qExpansion 1 f).coeff 0` vanishes. -/
theorem analyticAt_L_levelOne_iff {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F 𝒮ℒ k] (f : F) (s : ℂ) :
    AnalyticAt ℂ (ModularForm.L hk f) s ↔ s ≠ k ∨ (qExpansion 1 f).coeff 0 = 0 := by
  rw [ModularForm.analyticAt_L_iff, valueAtInfty_translate_S_levelOne]

/-- At level one, `ModularForm.L hk f` is entire if and only if `(qExpansion 1 f).coeff 0 = 0`. -/
theorem differentiable_L_levelOne_iff {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F 𝒮ℒ k] (f : F) :
    Differentiable ℂ (ModularForm.L hk f) ↔ (qExpansion 1 f).coeff 0 = 0 := by
  rw [ModularForm.differentiable_L_iff, valueAtInfty_translate_S_levelOne]

/-- **The `q`-expansion L-series of `E₄`**: on `Re s > 4`,
`L(E₄, s) = 240 ζ(s) ζ(s - 3)`. -/
theorem LSeries_qExpansion_coeff_E₄ {s : ℂ} (hs : 4 < s.re) :
    LSeries (fun n ↦ (qExpansion 1 _root_.ModularForm.E₄).coeff n) s =
      240 * riemannZeta s * riemannZeta (s - 3) := by
  have hcongr : LSeries (fun n ↦ (qExpansion 1 _root_.ModularForm.E₄).coeff n) s =
      LSeries ((240 : ℂ) • (↗(σ 3) : ℕ → ℂ)) s :=
    LSeries_congr (fun {n} hn ↦ by
      simpa [Pi.smul_apply, smul_eq_mul] using ModularForm.E₄_qExpansion_coeff_of_ne_zero hn) s
  have hs3 : ((3 : ℕ) : ℝ) + 1 < s.re := by norm_num; exact hs
  rw [hcongr, LSeries_smul, ArithmeticFunction.LSeries_sigma hs3, Nat.cast_ofNat, ← mul_assoc]

/-- On `Re s > 4`, Mathlib's `ModularForm.L` of `E₄` equals `240 ζ(s) ζ(s - 3)`. -/
theorem L_E₄_eq (hk : (0 : ℤ) < 4 := by decide) {s : ℂ} (hs : 4 < s.re) :
    _root_.ModularForm.L hk _root_.ModularForm.E₄ s =
      240 * riemannZeta s * riemannZeta (s - 3) := by
  have hs' : ((4 : ℤ) : ℝ) < s.re := by simpa using hs
  rw [← ModularFormClass.LSeries_qExpansion_coeff_eq_of_Gamma1_le Gamma1_one_map_eq_SL.le hk
    _root_.ModularForm.E₄ hs']
  exact LSeries_qExpansion_coeff_E₄ hs

/-- **Sharpness of the congruence abscissa bound for `E₄`**: the `q`-expansion coefficient L-series
of `E₄` has abscissa of absolute convergence equal to its weight `4`. -/
theorem abscissaOfAbsConv_qExpansion_coeff_E₄ :
    LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 _root_.ModularForm.E₄).coeff n) = 4 := by
  have hcongr :
      LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 _root_.ModularForm.E₄).coeff n) =
        LSeries.abscissaOfAbsConv ((240 : ℂ) • (↗(σ 3) : ℕ → ℂ)) :=
    LSeries.abscissaOfAbsConv_congr fun {n} hn ↦ by
      simpa [Pi.smul_apply, smul_eq_mul] using ModularForm.E₄_qExpansion_coeff_of_ne_zero hn
  have hsmul : LSeries.abscissaOfAbsConv ((240 : ℂ) • (↗(σ 3) : ℕ → ℂ)) =
      LSeries.abscissaOfAbsConv (↗(σ 3) : ℕ → ℂ) :=
    congrArg sInf (congrArg _ (Set.ext fun _ ↦ LSeriesSummable.smul_iff (by norm_num)))
  have h3 : (((3 : ℕ) : ℝ) + 1 : ℝ) = 4 := by norm_num
  rw [hcongr, hsmul, ArithmeticFunction.abscissaOfAbsConv_sigma, h3]
  rfl

/-- `ModularForm.L` of `E₄` has a simple pole at `s = 4`. -/
theorem meromorphicOrderAt_L_E₄_four (hk : (0 : ℤ) < 4 := by decide) :
    meromorphicOrderAt (_root_.ModularForm.L hk _root_.ModularForm.E₄) 4 = (-1 : ℤ) := by
  have h := meromorphicOrderAt_L_levelOne_k hk _root_.ModularForm.E₄
    (by rw [EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩]; exact one_ne_zero)
  simpa using h

/-- `ModularForm.L` of `E₄` is not analytic at `s = 4`. -/
theorem not_analyticAt_L_E₄_four (hk : (0 : ℤ) < 4 := by decide) :
    ¬ AnalyticAt ℂ (_root_.ModularForm.L hk _root_.ModularForm.E₄) 4 := by
  have h := (analyticAt_L_levelOne_iff hk _root_.ModularForm.E₄ 4).not
  simpa [EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩] using h

/-- `ModularForm.L` of `E₄` is not entire. -/
theorem not_differentiable_L_E₄ (hk : (0 : ℤ) < 4 := by decide) :
    ¬ Differentiable ℂ (_root_.ModularForm.L hk _root_.ModularForm.E₄) := by
  rw [differentiable_L_levelOne_iff, EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩]
  exact one_ne_zero

end TauCeti
