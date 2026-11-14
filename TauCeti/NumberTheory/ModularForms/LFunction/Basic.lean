/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
public import Mathlib.NumberTheory.ModularForms.LFunction
public import TauCeti.NumberTheory.LSeries.AbstractFuncEq
public import TauCeti.NumberTheory.LSeries.Continuation
import TauCeti.Geometry.Manifold.Connected
import TauCeti.NumberTheory.ModularForms.FiniteDimensional
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import TauCeti.NumberTheory.LSeries.MeanSquare

/-!
# Dirichlet series of modular forms

Mathlib's `Mathlib/NumberTheory/ModularForms/LFunction.lean` defines the completed
L-function `ModularForm.Λ` and the L-function `ModularForm.L` of a modular form for an
arithmetic level, with the Dirichlet-series identities `ModularForm.hasSum_L` and
`CuspForm.hasSum_L` on their convergence half-planes, and — for cusp forms — entire
continuation (`CuspForm.differentiable_L`). This file supplies the interface between that
API and Mathlib's `LSeries` of the `q`-expansion coefficients:

* abscissa-of-absolute-convergence bounds for the coefficient series,
* meromorphic continuation, exact pole at the weight, and regular-point characterization of
  `ModularForm.L`, and
* the identification of `LSeries` of the coefficients with `ModularForm.L` across the full
  convergence half-plane, in both the modular and the cuspidal ranges.

## Main results

* `ModularForm.abscissaOfAbsConv_qExpansion_coeff_le`: for a modular form of weight
  `k`, the abscissa of absolute convergence of the coefficient series is at most
  `k + 1` (from `aₙ = O(nᵏ)`), with `ModularForm.LSeriesSummable_qExpansion_coeff` giving
  absolute convergence on `Re s > k + 1`.
* `ModularForm.abscissaOfAbsConv_qExpansion_coeff_eq_bot_of_weight_nonpos`: in weight `k ≤ 0`,
  all positive `q`-expansion coefficients vanish
  (`ModularForm.qExpansion_coeff_eq_zero_of_weight_nonpos`), so the abscissa of absolute
  convergence is `⊥`.
* `ModularForm.weakFEPair_congr`, `ModularForm.Λ_congr`, `ModularForm.L_congr`: `weakFEPair`,
  `Λ`, and `L` depend only on the underlying function on `ℍ` and the weight, not on the ambient
  arithmetic subgroup.
* `ModularForm.meromorphic_L`, `ModularForm.meromorphicOrderAt_L_k`,
  `ModularForm.analyticAt_L_iff`, `ModularForm.differentiable_L_iff`: `L hk f` is meromorphic on
  `ℂ` with removable singularity at `0` and at most a simple pole at `k`, present if and only if
  `valueAtInfty (translate f ModularGroup.S) ≠ 0`.
* `ModularForm.LSeries_qExpansion_coeff_eq`, `CuspForm.LSeries_qExpansion_coeff_eq`, and
  `ModularForm.LSeries_qExpansion_coeff_eq_of_abscissaOfAbsConv_lt_re`:
  on the convergence half-plane (away from the possible pole at `k`), `LSeries` of the
  coefficients is `(Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s` for Mathlib's `ModularForm.L`,
  giving an analytic continuation on `{k}ᶜ`
  (`ModularForm.isContinuationOn_strictWidthInfty_cpow_mul_L`).
* `CuspForm.abscissaOfAbsConv_qExpansion_coeff_le`: for a cusp form, at most `(k+1)/2`
  (from Mathlib's mean-square coefficient bound and Cauchy–Schwarz). In weight one this
  gives the bound `1`, which the pointwise estimate `aₙ = O(n^{k/2})` does not give.
  `CuspForm.LSeriesSummable_qExpansion_coeff` is the resulting absolute convergence on
  `Re s > (k+1)/2`.
* `ModularForm.Λ_natCast_add_one`: `Λ(f, n + 1) = n! / (2π)ⁿ⁺¹ · L(f, n + 1)` at the positive
  integers, so that there `Λ` and `L` vanish together (`ModularForm.Λ_natCast_add_one_eq_zero_iff`).
* `CuspForm.hasEntireExtension_qExpansion_coeff`: the coefficient series of a cusp form
  has an entire extension.
* `CuspForm.L_ne_zero_of_qExpansion_coeff_ne_zero`: a nonzero coefficient makes
  the entire L-function nonzero.
* `CuspForm.eq_strictWidthInfty_cpow_mul_L`: uniqueness of the width-normalized entire
  continuation.

The non-cuspidal abscissa bound `k + 1` is weaker than Diamond–Shurman Prop. 5.9.1
(which gives convergence for `Re s > k`). On any level containing `Γ₁(N)`,
`TauCeti.ModularFormClass.abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le` sharpens it to `k`
in all weights, via `aₙ = O(n^{k-1})` in weight `k ≥ 3`, `aₙ = O(n^{1+ε})` in weight two, and the
weight-one cusp–Eisenstein decomposition combined with the cuspidal mean-square bound in weight one.
The entire continuation of the cusp-form series is `CuspForm.hasEntireExtension_qExpansion_coeff`
below.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/LFunction.lean`), rebuilt to consume Mathlib's
`ModularForm.L` rather than defining a parallel Dirichlet series.
The sharper cuspidal abscissa uses Mathlib's
`CuspFormClass.sum_range_norm_sq_qExpansion_coeff_isBigO`, followed by Cauchy–Schwarz
and Abel summation through `TauCeti.LSeries.abscissaOfAbsConv_le_of_sum_norm_sq_bigO`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/LFunction.lean`)
-/

public section

noncomputable section

open Filter LSeries Topology UpperHalfPlane

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
variable {F : Type*} [FunLike F ℍ ℂ] {s : ℂ}

/-- The `HasSum`-to-`LSeries` boundary shared by the identification theorems below:
plain Dirichlet sums at `s ≠ 0` converging to `v` identify `LSeries a s` with `v`. -/
private lemma LSeries_eq_of_hasSum {a : ℕ → ℂ} {v : ℂ} (hs0 : s ≠ 0)
    (h : HasSum (fun n : ℕ ↦ a n / (n : ℂ) ^ s) v) : LSeries a s = v := by
  rw [← funext (LSeries.term_of_ne_zero' hs0 a)] at h
  exact LSeriesHasSum.LSeries_eq h

namespace ModularForm

/-- In nonpositive weight `k ≤ 0`, every positive `q`-expansion coefficient of a modular form
vanishes (for negative weight the form is zero; in weight zero it is constant). -/
theorem qExpansion_coeff_eq_zero_of_weight_nonpos (hk : k ≤ 0) {h : ℝ}
    [ModularFormClass F Γ k] (f : F) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion h f).coeff n = 0 := by
  rcases hk.lt_or_eq with hk | rfl
  · simp [qExpansion_eq_zero_of_neg_weight hk f]
  · obtain ⟨c, hc⟩ := eq_const_of_weight_zero (ModularFormClass.modularForm f)
    have hf : (f : ℍ → ℂ) = c • (1 : ℍ → ℂ) := by
      ext z
      simpa [ModularFormClass.coe_modularForm] using congrFun hc z
    have han : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 :=
      (TauCeti.UpperHalfPlane.cuspFunction_one h).symm ▸ analyticAt_const
    rw [hf, UpperHalfPlane.qExpansion_smul han, UpperHalfPlane.qExpansion_one,
      PowerSeries.coeff_smul, PowerSeries.coeff_one, ite_eq_right hn, smul_zero]

/-- In nonpositive weight `k ≤ 0`, the `q`-expansion coefficient L-series has abscissa of
absolute convergence `⊥`, for any width `h`. -/
theorem abscissaOfAbsConv_qExpansion_coeff_eq_bot_of_weight_nonpos (hk : k ≤ 0) {h : ℝ}
    [ModularFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (fun n ↦ (qExpansion h f).coeff n) = ⊥ := by
  rw [LSeries.abscissaOfAbsConv_congr (g := 0) fun hn ↦
    qExpansion_coeff_eq_zero_of_weight_nonpos hk f hn]
  exact eq_bot_iff.mpr (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun _ _ ↦
    LSeriesSummable_zero)

/-- **Hecke's abscissa bound for modular forms**: the Dirichlet series of the `q`-expansion
coefficients converges absolutely for `Re s > k + 1` (from `aₙ = O(nᵏ)` for `k ≥ 0`; in negative
weight the form is zero). -/
theorem abscissaOfAbsConv_qExpansion_coeff_le [ModularFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) ≤
      ((k : ℝ) : EReal) + 1 := by
  by_cases hk : 0 ≤ k
  · refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow ?_
    refine (ModularFormClass.qExpansion_isBigO hk f).congr' EventuallyEq.rfl
      (Eventually.of_forall fun n ↦ ?_)
    simp only [Real.rpow_intCast]
  · rw [abscissaOfAbsConv_qExpansion_coeff_eq_bot_of_weight_nonpos (le_of_not_ge hk) f]
    exact bot_le

/-- The Dirichlet series of the `q`-expansion coefficients of a modular form converges absolutely
on the half-plane `Re s > k + 1`. -/
theorem LSeriesSummable_qExpansion_coeff [ModularFormClass F Γ k] (f : F)
    (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((abscissaOfAbsConv_qExpansion_coeff_le f).trans_lt (mod_cast hs))

section LevelIndependence

variable {Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ'.IsArithmetic]
variable {G : Type*} [FunLike G ℍ ℂ]

/-- The `WeakFEPair` of a modular form depends only on its underlying function on `ℍ` and its
weight, not on the ambient arithmetic subgroup. -/
theorem weakFEPair_congr (hk : 0 < k) [ModularFormClass F Γ k] [ModularFormClass G Γ' k]
    {f : F} {g : G} (hfg : (f : ℍ → ℂ) = g) :
    weakFEPair hk f = weakFEPair hk g := by
  simp only [weakFEPair, coe_translate, hfg]

/-- The completed `L`-function `Λ` depends only on the underlying function on `ℍ` and the weight,
not on the ambient arithmetic subgroup. -/
theorem Λ_congr (hk : 0 < k) [ModularFormClass F Γ k] [ModularFormClass G Γ' k]
    {f : F} {g : G} (hfg : (f : ℍ → ℂ) = g) :
    Λ hk f = Λ hk g := by
  simp only [Λ, weakFEPair_congr hk hfg]

/-- The `L`-function `ModularForm.L` depends only on the underlying function on `ℍ` and the
weight, not on the ambient arithmetic subgroup. -/
theorem L_congr (hk : 0 < k) [ModularFormClass F Γ k] [ModularFormClass G Γ' k]
    {f : F} {g : G} (hfg : (f : ℍ → ℂ) = g) :
    L hk f = L hk g := by
  simp only [L, Λ_congr hk hfg, hfg]

end LevelIndependence

/-- On `{0}ᶜ`, `L hk f` agrees locally near `s ≠ 0` with `z ↦ Λ hk f z * (2 * (Gammaℂ z)⁻¹)`. -/
private lemma L_eventuallyEq_of_ne_zero (hk : 0 < k) [ModularFormClass F Γ k] (f : F)
    (hs : s ≠ 0) :
    L hk f =ᶠ[𝓝 s] fun z ↦ Λ hk f z * (2 * (Complex.Gammaℂ z)⁻¹) := by
  filter_upwards [eventually_ne_nhds hs] with z hz
  simpa only [div_eq_mul_inv] using L_apply_of_ne_zero hk f hz

/-- At a nonzero regular point (`s ≠ k` or `valueAtInfty (translate f ModularGroup.S) = 0`),
`L hk f` is analytic. -/
private lemma analyticAt_L_of_ne_zero (hk : 0 < k) [ModularFormClass F Γ k] (f : F)
    (hs0 : s ≠ 0) (hs : s ≠ k ∨ valueAtInfty (translate f ModularGroup.S) = 0) :
    AnalyticAt ℂ (L hk f) s := by
  have hΛ : AnalyticAt ℂ (Λ hk f) s :=
    ((weakFEPair hk f).analyticAt_Λ_iff s).mpr ⟨Or.inl hs0, by simpa using hs⟩
  exact (hΛ.mul ((Complex.differentiable_Gammaℂ_inv.const_mul 2).analyticAt s)).congr
    (L_eventuallyEq_of_ne_zero hk f hs0).symm

/-- `L hk f` is analytic at `0`: the zero of `(Gammaℂ s)⁻¹` cancels the possible simple pole of
`Λ hk f` at `0`, and `L hk f 0 = -valueAtInfty f` fills the removable singularity. -/
theorem analyticAt_L_zero (hk : 0 < k) [ModularFormClass F Γ k] (f : F) :
    AnalyticAt ℂ (L hk f) 0 := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    (continuousAt_L_zero hk f)
  filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds (by exact_mod_cast hk.ne : (0 : ℂ) ≠ k)),
    self_mem_nhdsWithin] with z hzk hz0
  exact (analyticAt_L_of_ne_zero hk f hz0 (Or.inl hzk)).differentiableAt

/-- The `L`-function of a positive-weight modular form is meromorphic on `ℂ`. -/
theorem meromorphic_L (hk : 0 < k) [ModularFormClass F Γ k] (f : F) : Meromorphic (L hk f) := by
  intro s
  rcases eq_or_ne s 0 with rfl | hs0
  · exact (analyticAt_L_zero hk f).meromorphicAt
  · exact (((weakFEPair hk f).meromorphic_Λ s).mul
      ((Complex.differentiable_Gammaℂ_inv.const_mul 2).analyticAt s).meromorphicAt).congr
      ((L_eventuallyEq_of_ne_zero hk f hs0).symm.filter_mono nhdsWithin_le_nhds)

/-- When `valueAtInfty (translate f ModularGroup.S) ≠ 0`, `ModularForm.L hk f` has an exact simple
pole at the weight `k`. -/
theorem meromorphicOrderAt_L_k (hk : 0 < k) [ModularFormClass F Γ k] (f : F)
    (hg : valueAtInfty (translate f ModularGroup.S) ≠ 0) :
    meromorphicOrderAt (L hk f) k = (-1 : ℤ) := by
  have hk_re : 0 < ((k : ℂ)).re := by exact_mod_cast hk
  have hk0 : (k : ℂ) ≠ 0 := Complex.ne_zero_of_re_pos hk_re
  have hgamma : Complex.Gammaℂ k ≠ 0 := by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hk_re)
      (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using add_pos hk_re zero_lt_one))
  have hfactor : AnalyticAt ℂ (fun z ↦ 2 * (Complex.Gammaℂ z)⁻¹) k :=
    (Complex.differentiable_Gammaℂ_inv.const_mul 2).analyticAt k
  have hfactor_ord : meromorphicOrderAt (fun z ↦ 2 * (Complex.Gammaℂ z)⁻¹) k = 0 := by
    rw [hfactor.meromorphicOrderAt_eq,
      hfactor.analyticOrderAt_eq_zero.mpr (mul_ne_zero two_ne_zero (inv_ne_zero hgamma))]
    rfl
  have hΛ_ord : meromorphicOrderAt (Λ hk f) k = (-1 : ℤ) := by
    simpa [Λ] using (weakFEPair hk f).meromorphicOrderAt_Λ_k (by simpa using hg)
  have hΛ_mero : MeromorphicAt (Λ hk f) k := (weakFEPair hk f).meromorphic_Λ k
  have heq : L hk f =ᶠ[𝓝[≠] (k : ℂ)] (Λ hk f * fun z ↦ 2 * (Complex.Gammaℂ z)⁻¹) :=
    (L_eventuallyEq_of_ne_zero hk f hk0).filter_mono nhdsWithin_le_nhds
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul hΛ_mero hfactor.meromorphicAt,
    hΛ_ord, hfactor_ord, add_zero]

/-- **Regular points of `ModularForm.L`**: the only possible singularity of `L hk f` on `ℂ` is a
simple pole at the weight `k`, which occurs if and only if
`valueAtInfty (translate f ModularGroup.S) ≠ 0`. -/
@[simp]
theorem analyticAt_L_iff (hk : 0 < k) [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    AnalyticAt ℂ (L hk f) s ↔ s ≠ k ∨ valueAtInfty (translate f ModularGroup.S) = 0 := by
  constructor
  · intro h
    by_cases hs : s = k
    · right
      by_contra hg
      have hn := (hs ▸ h).meromorphicOrderAt_nonneg
      rw [meromorphicOrderAt_L_k hk f hg] at hn
      have : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hn
      omega
    · exact Or.inl hs
  · intro hs
    rcases eq_or_ne s 0 with rfl | hs0
    · exact analyticAt_L_zero hk f
    · exact analyticAt_L_of_ne_zero hk f hs0 hs

/-- At any point away from `k` (or everywhere when `translate f ModularGroup.S` vanishes at `∞`),
`L hk f` is complex differentiable. -/
theorem differentiableAt_L (hk : 0 < k) [ModularFormClass F Γ k] (f : F)
    (hs : s ≠ k ∨ valueAtInfty (translate f ModularGroup.S) = 0) :
    DifferentiableAt ℂ (L hk f) s :=
  ((analyticAt_L_iff hk f s).mpr hs).differentiableAt

/-- `ModularForm.L hk f` is entire if and only if `translate f ModularGroup.S` vanishes at `∞`. -/
@[simp]
theorem differentiable_L_iff (hk : 0 < k) [ModularFormClass F Γ k] (f : F) :
    Differentiable ℂ (L hk f) ↔ valueAtInfty (translate f ModularGroup.S) = 0 :=
  ⟨fun h ↦ by simpa using (analyticAt_L_iff hk f k).mp (h.analyticAt k),
    fun h z ↦ differentiableAt_L hk f (Or.inr h)⟩

/-- On the half-plane `Re s > k + 1`, the Dirichlet series of the `q`-expansion
coefficients is Mathlib's `ModularForm.L`, up to the width factor. Not `@[simp]`: the
positivity witness `hk` occurs in the right-hand side `L hk f s`, so the rewrite cannot
fire from the left-hand side alone (simpNF rejects it). -/
theorem LSeries_qExpansion_coeff_eq (hk : 0 < k) [ModularFormClass F Γ k] (f : F)
    (hs : k + 1 < s.re) :
    LSeries (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) s =
      (Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [Complex.zero_re] at hs
    have hk' : (0 : ℝ) ≤ (k : ℝ) := mod_cast hk.le
    linarith
  exact LSeries_eq_of_hasSum hs0 (hasSum_L hk f hs)

/-- **Dirichlet-series identity on the full convergence half-plane**: at any regular point `s` of
`ModularForm.L` inside the open half-plane of absolute convergence of the `q`-expansion
coefficient L-series, `LSeries` of the coefficients equals
`(Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s`. -/
theorem LSeries_qExpansion_coeff_eq_of_abscissaOfAbsConv_lt_re (hk : 0 < k)
    [ModularFormClass F Γ k] (f : F)
    (hs : s ≠ k ∨ valueAtInfty (translate f ModularGroup.S) = 0)
    (habs : abscissaOfAbsConv (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) < s.re) :
    LSeries (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) s =
      (Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s := by
  obtain ⟨σ, hσ_abs, hσ_s⟩ := EReal.exists_between_coe_real habs
  have hcpow : Differentiable ℂ (fun z : ℂ ↦ (Γ.strictWidthInfty : ℂ) ^ (-z)) :=
    Differentiable.const_cpow differentiable_neg
      (Or.inl (Complex.ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne'))
  set z₀ : ℂ := ((max σ ((k : ℝ) + 1) + 1 : ℝ) : ℂ)
  have hz₀_σ : σ < z₀.re := by
    simp only [z₀, Complex.ofReal_re]
    linarith [le_max_left σ ((k : ℝ) + 1)]
  have hev : (LSeries fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) =ᶠ[𝓝 z₀]
      fun z ↦ (Γ.strictWidthInfty : ℂ) ^ (-z) * L hk f z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      simp only [z₀, Complex.ofReal_re]
      linarith [le_max_right σ ((k : ℝ) + 1)] : (k : ℝ) + 1 < z₀.re)] with z hz
    exact LSeries_qExpansion_coeff_eq hk f hz
  rcases hs with hsk | h0
  · set W : Set ℂ := {z : ℂ | σ < z.re} \ {(k : ℂ)}
    have hL : AnalyticOnNhd ℂ (LSeries (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n)) W :=
      (LSeries_analyticOnNhd _).mono fun z hz ↦ hσ_abs.trans_le (by exact_mod_cast hz.1.le)
    have hF : AnalyticOnNhd ℂ (fun z ↦ (Γ.strictWidthInfty : ℂ) ^ (-z) * L hk f z) W :=
      fun z hz ↦ (hcpow.analyticAt z).mul ((analyticAt_L_iff hk f z).mpr (Or.inl hz.2))
    have hz₀k : z₀ ≠ k := by
      intro h
      have hre := congrArg Complex.re h
      simp only [z₀, Complex.ofReal_re, Complex.intCast_re] at hre
      linarith [le_max_right σ ((k : ℝ) + 1)]
    exact hL.eqOn_of_preconnected_of_eventuallyEq hF
      (TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank (E := ℂ)
        (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)
        (isOpen_lt continuous_const Complex.continuous_re)
        (convex_halfSpace_re_gt σ).isPreconnected
        isClosed_singleton (Set.finite_singleton _).isDiscrete)
      ⟨hz₀_σ, hz₀k⟩ hev ⟨by exact_mod_cast hσ_s, hsk⟩
  · set W : Set ℂ := {z : ℂ | σ < z.re}
    have hL : AnalyticOnNhd ℂ (LSeries (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n)) W :=
      (LSeries_analyticOnNhd _).mono fun z (hz : σ < z.re) ↦
        hσ_abs.trans_le (by exact_mod_cast hz.le)
    have hF : AnalyticOnNhd ℂ (fun z ↦ (Γ.strictWidthInfty : ℂ) ^ (-z) * L hk f z) W :=
      fun z _ ↦ (hcpow.analyticAt z).mul ((analyticAt_L_iff hk f z).mpr (Or.inr h0))
    exact hL.eqOn_of_preconnected_of_eventuallyEq hF
      (convex_halfSpace_re_gt σ).isPreconnected hz₀_σ hev (by exact_mod_cast hσ_s)

/-- At any nonzero regular point `s` of `ModularForm.L` inside the open half-plane of absolute
convergence of the `q`-expansion coefficient L-series, the plain Dirichlet series
`∑ aₙ / n ^ s` converges to `(Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s`. -/
theorem hasSum_L_of_abscissaOfAbsConv_lt_re (hk : 0 < k) [ModularFormClass F Γ k] (f : F)
    (hs0 : s ≠ 0) (hs : s ≠ k ∨ valueAtInfty (translate f ModularGroup.S) = 0)
    (habs : abscissaOfAbsConv (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) < s.re) :
    HasSum (fun n : ℕ ↦ (qExpansion Γ.strictWidthInfty f).coeff n / (n : ℂ) ^ s)
      ((Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s) := by
  have hsum := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  rw [LSeries_qExpansion_coeff_eq_of_abscissaOfAbsConv_lt_re hk f hs habs] at hsum
  rwa [LSeriesHasSum, funext (LSeries.term_of_ne_zero' hs0 _)] at hsum

/-- **Meromorphic L-series continuation away from the weight**: on `{k}ᶜ`, the width-normalized
`ModularForm.L` is an analytic continuation (`LSeries.IsContinuationOn`) of the `q`-expansion
coefficient L-series. -/
theorem isContinuationOn_strictWidthInfty_cpow_mul_L (hk : 0 < k) [ModularFormClass F Γ k]
    (f : F) :
    LSeries.IsContinuationOn (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n)
      (fun s ↦ (Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s) {(k : ℂ)}ᶜ := by
  have hcpow : Differentiable ℂ (fun z : ℂ ↦ (Γ.strictWidthInfty : ℂ) ^ (-z)) :=
    Differentiable.const_cpow differentiable_neg
      (Or.inl (Complex.ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne'))
  refine ⟨isOpen_compl_singleton,
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (k : ℂ)).isPreconnected,
    fun z hz ↦ (hcpow.analyticAt z).mul ((analyticAt_L_iff hk f z).mpr (Or.inl hz)),
    ⟨((k : ℝ) + 2 : ℂ), ?_, ?_⟩, fun z hz habs ↦
      (LSeries_qExpansion_coeff_eq_of_abscissaOfAbsConv_lt_re hk f (Or.inl hz) habs).symm⟩
  · intro h
    have hre := congrArg Complex.re (Set.mem_singleton_iff.mp h)
    simp at hre
  · refine (abscissaOfAbsConv_qExpansion_coeff_le f).trans_lt ?_
    have : (k : ℝ) + 1 < (((k : ℝ) + 2 : ℂ)).re := by simp
    exact_mod_cast this

/-- At a positive integer `n + 1` the completed `L`-function of a modular form is
`Λ(f, n + 1) = n! / (2π)ⁿ⁺¹ · L(f, n + 1)`: the archimedean factor `Γ_ℂ(s) / 2 = (2π)⁻ˢ Γ(s)`
at `s = n + 1`. -/
theorem Λ_natCast_add_one (hk : 0 < k) [ModularFormClass F Γ k] (f : F) (n : ℕ) :
    Λ hk f (n + 1) = n.factorial / (2 * Real.pi) ^ (n + 1) * L hk f (n + 1) := by
  have h2π : (2 * Real.pi : ℂ) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Real.two_pi_pos.ne')
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [L_apply_of_ne_zero hk f (by exact_mod_cast n.succ_ne_zero), Complex.Gammaℂ_def,
    Complex.Gamma_nat_eq_factorial, Complex.cpow_neg, ← Nat.cast_succ, Complex.cpow_natCast]
  field_simp

/-- At a positive integer the completed `L`-function of a modular form vanishes exactly when its
`L`-function does. -/
theorem Λ_natCast_add_one_eq_zero_iff (hk : 0 < k) [ModularFormClass F Γ k] (f : F) (n : ℕ) :
    Λ hk f (n + 1) = 0 ↔ L hk f (n + 1) = 0 := by
  rw [Λ_natCast_add_one, mul_eq_zero, or_iff_right]
  exact div_ne_zero (by exact_mod_cast n.factorial_ne_zero)
    (pow_ne_zero _ (by exact_mod_cast Real.two_pi_pos.ne'))

end ModularForm

namespace CuspForm

/-- **The mean-square abscissa bound for cusp forms**: the Dirichlet series of the
`q`-expansion coefficients converges absolutely for `Re s > (k+1)/2`. In particular its
abscissa is at most one in weight one. -/
theorem abscissaOfAbsConv_qExpansion_coeff_le [CuspFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) ≤
      ((((k : ℝ) + 1) / 2 : ℝ) : EReal) := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    have hO : (fun n ↦ ∑ j ∈ Finset.Icc 1 n,
        ‖(qExpansion Γ.strictWidthInfty f).coeff j‖ ^ 2) =O[atTop]
        fun n ↦ (n : ℝ) ^ (k : ℝ) :=
      TauCeti.isBigO_sum_Icc_of_sum_range (fun _ ↦ sq_nonneg _)
        (by simpa only [Real.rpow_natCast] using
          CuspFormClass.sum_range_norm_sq_qExpansion_coeff_isBigO f)
    simpa only [Int.cast_natCast] using
      TauCeti.LSeries.abscissaOfAbsConv_le_of_sum_norm_sq_bigO hO
        (le_trans (by norm_num) (Nat.cast_nonneg k))
  · refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y _ ↦ ?_
    rw [qExpansion_eq_zero_of_weight_nonpos (le_of_lt (lt_of_not_ge hk)) f]
    simp only [map_zero]
    exact LSeriesSummable_zero

/-- The Dirichlet series of the `q`-expansion coefficients of a cusp form converges absolutely
on the half-plane `Re s > (k+1)/2`. -/
theorem LSeriesSummable_qExpansion_coeff [CuspFormClass F Γ k] (f : F)
    (hs : ((k : ℝ) + 1) / 2 < s.re) :
    LSeriesSummable (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((abscissaOfAbsConv_qExpansion_coeff_le f).trans_lt (mod_cast hs))

/-- On the half-plane `Re s > k/2 + 1`, the Dirichlet series of the `q`-expansion
coefficients of a cusp form is Mathlib's `ModularForm.L`, up to the width factor.
Not `@[simp]`: as with the modular-form version, `hk` occurs in the right-hand side. -/
theorem LSeries_qExpansion_coeff_eq (hk : 0 < k) [CuspFormClass F Γ k] (f : F)
    (hs : k / 2 + 1 < s.re) :
    LSeries (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) s =
      (Γ.strictWidthInfty : ℂ) ^ (-s) * ModularForm.L hk f s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [Complex.zero_re] at hs
    have hk' : (0 : ℝ) < (k : ℝ) := mod_cast hk
    linarith
  exact LSeries_eq_of_hasSum hs0 (hasSum_L hk f hs)

/-- **Entire continuation of the L-series of a cusp form**: the Dirichlet series of the
`q`-expansion coefficients of a cusp form has an entire extension, namely
`s ↦ (Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s` in positive weight (in nonpositive weight the
form is zero). -/
theorem hasEntireExtension_qExpansion_coeff [CuspFormClass F Γ k] (f : F) :
    LSeries.HasEntireExtension (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) := by
  rcases lt_or_ge 0 k with hk | hk
  · refine LSeries.HasEntireExtension.of_extension_of_eq_on_lt_re (c := (k : ℝ) / 2 + 1)
      ?_ ?_ (fun {s} hs ↦ (LSeries_qExpansion_coeff_eq hk f hs).symm)
    · refine (abscissaOfAbsConv_qExpansion_coeff_le f).trans_lt ?_
      exact EReal.coe_lt_top _
    · exact (Differentiable.const_cpow differentiable_neg
        (Or.inl (Complex.ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne'))).mul
        (differentiable_L hk f)
  · refine LSeries.hasEntireExtension_of_support_finite ?_
    rw [qExpansion_eq_zero_of_weight_nonpos hk f]
    simp

/-- The entire L-function of a positive-weight cusp form is nonzero if one of its
coefficients is nonzero (the constant coefficient is always zero). This ensures that its
analytic order is finite. -/
theorem L_ne_zero_of_qExpansion_coeff_ne_zero [CuspFormClass F Γ k] (f : F) (hk : 0 < k)
    {n : ℕ} (hcoeff : (qExpansion Γ.strictWidthInfty f).coeff n ≠ 0) :
    ModularForm.L hk f ≠ 0 := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hcoeff (CuspFormClass.qExpansion_coeff_zero f Γ.strictWidthInfty_pos
      Γ.strictWidthInfty_mem_strictPeriods)
  intro hL
  have hzero :
      (fun x : ℝ ↦ LSeries (fun m ↦ (qExpansion Γ.strictWidthInfty f).coeff m) x)
        =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop ((k : ℝ) / 2 + 2)] with x hx
    have hs : (k : ℝ) / 2 + 1 < x := by linarith
    simpa [hL] using CuspForm.LSeries_qExpansion_coeff_eq hk f hs
  rcases LSeries_eventually_eq_zero_iff'.mp hzero with hzero | habscissa
  · exact hcoeff (hzero n hn)
  · have hfinite := (CuspForm.hasEntireExtension_qExpansion_coeff f).abscissa_lt_top
    rw [habscissa] at hfinite
    exact (lt_irrefl ⊤ hfinite).elim

/-- A positive-weight cusp form with a nonzero coefficient has finite analytic
order at every point. -/
theorem analyticOrderAt_L_ne_top_of_qExpansion_coeff_ne_zero [CuspFormClass F Γ k] (f : F)
    (hk : 0 < k) (s : ℂ) {n : ℕ}
    (hcoeff : (qExpansion Γ.strictWidthInfty f).coeff n ≠ 0) :
    analyticOrderAt (ModularForm.L hk f) s ≠ ⊤ := by
  intro htop
  apply L_ne_zero_of_qExpansion_coeff_ne_zero f hk hcoeff
  exact (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s fun _ ↦
    (CuspForm.differentiable_L hk f).analyticAt _).mp htop

/-- Any entire function agreeing with the coefficient Dirichlet series of a positive-weight
cusp form on its convergence half-plane is the width-normalized entire L-function. -/
theorem eq_strictWidthInfty_cpow_mul_L [CuspFormClass F Γ k] (f : F) (hk : 0 < k)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hGL : ∀ {s : ℂ}, (k : ℝ) / 2 + 1 < s.re →
      G s = LSeries (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) s) :
    G = fun s ↦ (Γ.strictWidthInfty : ℂ) ^ (-s) * ModularForm.L hk f s := by
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((Differentiable.const_cpow differentiable_neg
        (Or.inl (Complex.ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne'))).mul
        (CuspForm.differentiable_L hk f))) (by
      refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨{s : ℂ | (k : ℝ) / 2 + 1 < s.re}, ?_, ?_⟩
      · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
          simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
          linarith : (((k : ℝ) / 2 + 2 : ℝ) : ℂ) ∈
            {s : ℂ | (k : ℝ) / 2 + 1 < s.re})
      · intro s hs
        exact (hGL hs).trans (CuspForm.LSeries_qExpansion_coeff_eq hk f hs))

end CuspForm
