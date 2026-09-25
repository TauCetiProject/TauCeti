/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Injectivity
public import Mathlib.NumberTheory.ModularForms.LFunction
public import TauCeti.NumberTheory.LSeries.EntireExtension

/-!
# Dirichlet series of modular forms

Mathlib's `Mathlib/NumberTheory/ModularForms/LFunction.lean` defines the completed
L-function `ModularForm.Λ` and the L-function `ModularForm.L` of a modular form for an
arithmetic level, with the Dirichlet-series identities `ModularForm.hasSum_L` and
`CuspForm.hasSum_L` on their convergence half-planes, and — for cusp forms — entire
continuation (`CuspForm.differentiable_L`). This file supplies the interface between that
API and Mathlib's `LSeries` of the `q`-expansion coefficients:

* Hecke's abscissa-of-absolute-convergence bounds for the coefficient series, and
* the identification of `LSeries` of the coefficients with `ModularForm.L` on the
  convergence half-plane, in both the modular and the cuspidal ranges.

## Main results

* `ModularForm.abscissaOfAbsConv_qExpansion_coeff_le`: for a modular form of weight
  `k ≥ 0`, the abscissa of absolute convergence of the coefficient series is at most
  `k + 1` (from `aₙ = O(nᵏ)`).
* `CuspForm.abscissaOfAbsConv_qExpansion_coeff_le`: for a cusp form, at most `k/2 + 1`
  (from Hecke's `aₙ = O(n^{k/2})`).
* `CuspForm.LSeriesSummable_qExpansion_coeff`: absolute convergence of the coefficient
  L-series for `Re s > k/2 + 1`.
* `ModularForm.LSeries_qExpansion_coeff_eq`, `CuspForm.LSeries_qExpansion_coeff_eq`:
  on the respective half-planes, `LSeries` of the coefficients is
  `(Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s` for Mathlib's `ModularForm.L`.
* `CuspForm.hasEntireExtension_qExpansion_coeff`: the coefficient series of a cusp form
  of positive weight has an entire extension (the Layer-7 continuation milestone).
* `CuspForm.L_ne_zero_of_qExpansion_coeff_ne_zero`: a nonzero positive-index coefficient makes
  the entire L-function nonzero.
* `CuspForm.eq_strictWidthInfty_cpow_mul_L`: uniqueness of the width-normalized entire
  continuation.

The non-cuspidal abscissa bound `k + 1` is weaker than Diamond–Shurman Prop. 5.9.1
(which gives convergence for `Re s > k` via `aₙ = O(n^{k-1})`); tightening it is a
separate milestone of the roadmap's Layer 7. The entire continuation of the cusp-form
series is `CuspForm.hasEntireExtension_qExpansion_coeff` below.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/LFunction.lean`), rebuilt to consume Mathlib's
`ModularForm.L` rather than defining a parallel Dirichlet series.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/LFunction.lean`)
-/

public section

noncomputable section

open Filter LSeries UpperHalfPlane

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
variable {F : Type*} [FunLike F ℍ ℂ] {s : ℂ}

/-- The `HasSum`-to-`LSeries` boundary shared by the identification theorems below:
plain Dirichlet sums at `s ≠ 0` converging to `v` identify `LSeries a s` with `v`. -/
private lemma LSeries_eq_of_hasSum {a : ℕ → ℂ} {v : ℂ} (hs0 : s ≠ 0)
    (h : HasSum (fun n : ℕ ↦ a n / (n : ℂ) ^ s) v) : LSeries a s = v := by
  rw [← funext (LSeries.term_of_ne_zero' hs0 a)] at h
  exact LSeriesHasSum.LSeries_eq h

namespace ModularForm

/-- **Hecke's abscissa bound for modular forms**: for weight `k ≥ 0`, the Dirichlet series
of the `q`-expansion coefficients converges absolutely for `Re s > k + 1`
(from `aₙ = O(nᵏ)`). -/
theorem abscissaOfAbsConv_qExpansion_coeff_le (hk : 0 ≤ k) [ModularFormClass F Γ k]
    (f : F) :
    abscissaOfAbsConv (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) ≤
      ((k : ℝ) : EReal) + 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow ?_
  refine (ModularFormClass.qExpansion_isBigO hk f).congr' EventuallyEq.rfl
    (Eventually.of_forall fun n ↦ ?_)
  simp only [Real.rpow_intCast]

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

end ModularForm

namespace CuspForm

/-- **Hecke's abscissa bound for cusp forms**: the Dirichlet series of the `q`-expansion
coefficients converges absolutely for `Re s > k/2 + 1` (from Hecke's
`aₙ = O(n^{k/2})`). -/
theorem abscissaOfAbsConv_qExpansion_coeff_le [CuspFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) ≤
      (((k : ℝ) / 2 : ℝ) : EReal) + 1 :=
  LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (CuspFormClass.qExpansion_isBigO f)

/-- The L-series of a cusp form's Fourier coefficients converges absolutely when
`Re s > k/2 + 1`. -/
theorem LSeriesSummable_qExpansion_coeff [CuspFormClass F Γ k] (f : F)
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) s := by
  refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
  exact (abscissaOfAbsConv_qExpansion_coeff_le f).trans_lt (mod_cast hs)

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

/-- **Entire continuation of the L-series of a cusp form** — the roadmap's Layer-7
continuation milestone: the Dirichlet series of the `q`-expansion coefficients of a cusp
form of positive weight has an entire extension, namely
`s ↦ (Γ.strictWidthInfty : ℂ) ^ (-s) * L hk f s`. -/
theorem hasEntireExtension_qExpansion_coeff (hk : 0 < k) [CuspFormClass F Γ k] (f : F) :
    LSeries.HasEntireExtension (fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n) := by
  refine LSeries.HasEntireExtension.of_extension_of_eq_on_lt_re (c := (k : ℝ) / 2 + 1)
    ?_ ?_ (fun {s} hs ↦ (LSeries_qExpansion_coeff_eq hk f hs).symm)
  · refine (abscissaOfAbsConv_qExpansion_coeff_le f).trans_lt ?_
    have hcast : (((k : ℝ) / 2 : ℝ) : EReal) + 1 = (((k : ℝ) / 2 + 1 : ℝ) : EReal) := by
      norm_cast
    rw [hcast]
    exact EReal.coe_lt_top _
  · exact (Differentiable.const_cpow differentiable_neg
      (Or.inl (Complex.ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne'))).mul
      (differentiable_L hk f)

/-- The entire L-function of a positive-weight cusp form is nonzero if one of its
positive-index coefficients is nonzero. This ensures that its analytic order is finite. -/
theorem L_ne_zero_of_qExpansion_coeff_ne_zero [CuspFormClass F Γ k] (f : F) (hk : 0 < k)
    {n : ℕ} (hn : n ≠ 0) (hcoeff : (qExpansion Γ.strictWidthInfty f).coeff n ≠ 0) :
    ModularForm.L hk f ≠ 0 := by
  intro hL
  have hzero :
      (fun x : ℝ ↦ LSeries (fun m ↦ (qExpansion Γ.strictWidthInfty f).coeff m) x)
        =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop ((k : ℝ) / 2 + 2)] with x hx
    have hs : (k : ℝ) / 2 + 1 < x := by linarith
    simpa [hL] using CuspForm.LSeries_qExpansion_coeff_eq hk f hs
  rcases LSeries_eventually_eq_zero_iff'.mp hzero with hzero | habscissa
  · exact hcoeff (hzero n hn)
  · have hfinite := (CuspForm.hasEntireExtension_qExpansion_coeff hk f).abscissa_lt_top
    rw [habscissa] at hfinite
    exact (lt_irrefl ⊤ hfinite).elim

/-- A positive-weight cusp form with a nonzero positive-index coefficient has finite analytic
order at every point. -/
theorem analyticOrderAt_L_ne_top_of_qExpansion_coeff_ne_zero [CuspFormClass F Γ k] (f : F)
    (hk : 0 < k) (s : ℂ) {n : ℕ} (hn : n ≠ 0)
    (hcoeff : (qExpansion Γ.strictWidthInfty f).coeff n ≠ 0) :
    analyticOrderAt (ModularForm.L hk f) s ≠ ⊤ := by
  intro htop
  apply L_ne_zero_of_qExpansion_coeff_ne_zero f hk hn hcoeff
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
