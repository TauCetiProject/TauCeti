/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt
public import TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.NormCoeff
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Boundary

/-!
# First Riesz sums of nontrivial ray class characters

When the continued L-function of a nontrivial ray class character `χ` is nonzero at `1`,
the first Riesz sum `R(x)` of its twisted ideal von Mangoldt coefficients satisfies
`R(x) / x → −L′(1, χ) / L(1, χ)` as `x → ∞`. For any complex coefficient `c`, there is
a constant `C` such that `‖R(x) + c x‖ ≤ C x` for all `x ≥ 1`.
-/

public section

open Asymptotics Complex Filter NumberField Set
open scoped Topology

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- The normalized first Riesz sum for a nontrivial ray class character converges to
`−L′(1, χ)/L(1, χ)` when its continued L-function does not vanish at `1`. Nonvanishing at
the other points of `Re s = 1` follows from the boundary nonvanishing theorem. -/
theorem tendsto_rieszSum_vonMangoldtTransform_div {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (h₁ : continuedLFunctionOfWeight χ.toUnitaryIdealWeight 1 ≠ 0) :
    Tendsto (fun x : ℝ ↦ rieszSum
      (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform) x /
        (x : ℂ)) atTop (𝓝 (-logDeriv (continuedLFunctionOfWeight χ.toUnitaryIdealWeight) 1)) := by
  let w := χ.toUnitaryIdealWeight
  let L := continuedLFunctionOfWeight w
  refine tendsto_rieszSum_div_of_analyticAt (F := fun s ↦ -logDeriv L s)
    (C := (Module.finrank ℚ K : ℝ) * (Real.log 4 + 4)) (fun x hx ↦ ?_) (fun s hs ↦ ?_)
    (fun s hs ↦ ?_)
  · rw [mul_assoc]
    exact (w.toIdealArithmeticFunction.norm_sum_normCoeff_vonMangoldtTransform_le
      (fun I _ ↦ by simpa using w.norm_le_one I) x).trans
      (mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (by linarith))
        (Nat.cast_nonneg _))
  · have hcancel := hasCancellation_toUnitaryIdealWeight hχ
    have hn : L s ≠ 0 := by
      rcases eq_or_ne s 1 with rfl | h
      · exact h₁
      · exact continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero hχ hs.ge (Or.inr h)
    have ha : AnalyticAt ℂ L s :=
      ((differentiableOn_continuedLFunctionOfWeight hcancel).analyticOnNhd
        (isOpen_lt continuous_const Complex.continuous_re)) s
        ((cancellationExponent_lt_one (K := K)).trans_le hs.ge)
    exact (ha.logDeriv hn).neg
  · have habs : idealAbscissaOfAbsConv K w.toIdealArithmeticFunction < s.re :=
      idealAbscissaOfAbsConv_lt_re_of_bounded (f := w.toIdealArithmeticFunction)
        (C := 1) (fun I ↦ by simpa using w.norm_le_one I) hs
    have hsum := IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform habs
    have heq : L =ᶠ[𝓝 s] LSeries (normCoeff K w.toIdealArithmeticFunction) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
      exact continuedLFunctionOfWeight_eq_LSeries w hz
    have hlog := w.val.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform (s := s) (by
      rwa [← w.toIdealArithmeticFunction_eq_val])
    rw [← w.toIdealArithmeticFunction_eq_val, ← LSeries_normCoeff K hsum] at hlog
    rw [(logDeriv_congr_nhds heq).eq_of_nhds, hlog, neg_neg]
    exact (LSeriesSummable_normCoeff K hsum).LSeriesHasSum

/-- For a nontrivial ray class character whose L-function is nonzero at `1`, the twisted
first Riesz sum remains bounded by `C x` on `[1, ∞)` after any linear correction `c x`. -/
theorem exists_norm_rieszSum_vonMangoldtTransform_add_mul_le {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) (h₁ : continuedLFunctionOfWeight χ.toUnitaryIdealWeight 1 ≠ 0) (c : ℂ) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ‖rieszSum
      (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform) x +
        c * (x : ℂ)‖ ≤ C * x := by
  let a := normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform
  let R := rieszSum a
  have hn : ∀ᶠ x : ℝ in atTop, (x : ℂ) ≠ 0 :=
    (eventually_gt_atTop (0 : ℝ)).mono fun x hx ↦ Complex.ofReal_ne_zero.mpr hx.ne'
  have h : R =O[atTop] (fun x : ℝ ↦ (x : ℂ)) :=
    isBigO_of_div_tendsto_nhds (hn.mono fun _ hn' hzero ↦ (hn' hzero).elim) _
      (tendsto_rieszSum_vonMangoldtTransform_div hχ h₁)
  have hc : (fun x : ℝ ↦ c * (x : ℂ)) =O[atTop] (fun x : ℝ ↦ (x : ℂ)) :=
    (isBigO_refl (fun x : ℝ ↦ (x : ℂ)) atTop).const_mul_left c
  have hcont : Continuous fun x : ℝ ↦ R x + c * (x : ℂ) :=
    (continuous_rieszSum _).add (continuous_const.mul continuous_ofReal)
  have hO := (h.add hc).isBigO_principal_Ici_of_continuousOn (a := (1 : ℝ))
    hcont.continuousOn continuous_ofReal.continuousOn fun x hx ↦ by
      simpa using (zero_lt_one.trans_le (mem_Ici.mp hx)).ne'
  obtain ⟨C, hC⟩ := hO.isBigOWith
  exact ⟨C, fun x hx ↦ by
    simpa [Real.norm_of_nonneg (zero_le_one.trans hx)] using isBigOWith_principal.mp hC x hx⟩

end TauCeti.GlobalNumberFields.RayClassCharacter
