/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Liouville
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Liouville.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.NumberField.DedekindZeta.Basic

/-!
# Local continuation counterexample for the ideal Liouville weight

Let `K` be a number field and `λ_K = TauCeti.MultiplicativeIdealWeight.liouville K` the ideal
Liouville weight taking value `-1` at every height-one prime. On `Re s > 1`,
`L(λ_K, s) = ζ_K(2s) / ζ_K(s)` extends holomorphically across `s = 1` to a function vanishing at
`s = 1` (`TauCeti.MultiplicativeIdealWeight.`
`exists_differentiableOn_eqOn_LSeries_liouville_and_apply_one_eq_zero`), demonstrating that local
analytic continuation across `s = 1` alone does not rule out `L 1 = 0`.

## Main results

* `TauCeti.MultiplicativeIdealWeight.`
  `exists_differentiableOn_eqOn_LSeries_liouville_and_apply_one_eq_zero`:
  local continuation counterexample with `L 1 = 0`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* Mathlib's `zetaMul` positivity argument in `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`
  (Michael Stoll, David Loeffler, and Terence Tao) provides the positivity background for the
  quadratic case.
-/

public section

namespace TauCeti.MultiplicativeIdealWeight

open Complex NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Counterexample to local continuation across `s = 1` alone.** For the ideal Liouville weight
`λ_K = MultiplicativeIdealWeight.liouville K`, which satisfies `(λ_K ^ 2).IsTrivialOnGood`, the
Dirichlet series `L(λ_K, s) = ζ_K(2s) / ζ_K(s)` continues holomorphically across `s = 1` to
`Metric.ball 1 r ∪ {s | 1 < s.re}` and vanishes at `s = 1`. Thus local analytic continuation across
`s = 1` alone cannot rule out `L 1 = 0`. -/
theorem exists_differentiableOn_eqOn_LSeries_liouville_and_apply_one_eq_zero :
    ∃ r > 0, ∃ L : ℂ → ℂ,
      DifferentiableOn ℂ L (Metric.ball (1 : ℂ) r ∪ {s | 1 < s.re}) ∧
      Set.EqOn L (LSeries (normCoeff K (liouville K).toIdealArithmeticFunction)) {s | 1 < s.re} ∧
      L 1 = 0 := by
  obtain ⟨H, hHdiff, hHeq, _, hHne⟩ := exists_differentiableOn_eq_sub_one_mul_dedekindZeta K
  set U : Set ℂ := {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h1U : (1 : ℂ) ∈ U :=
    setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (by simp)
  have hH1 : H 1 ≠ 0 := hHne 1 (by simp)
  have hmem : U ∩ {s : ℂ | (1 / 2 : ℝ) < s.re} ∩ {s : ℂ | H s ≠ 0} ∈ nhds (1 : ℂ) :=
    Filter.inter_mem (Filter.inter_mem (hUopen.mem_nhds h1U)
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)))
      ((hHdiff.differentiableAt (hUopen.mem_nhds h1U)).continuousAt.eventually_ne hH1)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hmem
  set L : ℂ → ℂ := fun s ↦ (s - 1) * dedekindZeta K (2 * s) / H s
  refine ⟨r, hr, L, ?_, ?_, by simp [L]⟩
  · intro s hs
    have hsU : s ∈ U := hs.elim (fun h ↦ (hball h).1.1) fun h ↦
      setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K
        (le_of_lt (by simpa only [Set.mem_ofPred_eq] using h))
    have hs2 : 1 < (2 * s).re := by
      have hhalf : (1 / 2 : ℝ) < s.re :=
        hs.elim (fun h ↦ (hball h).1.2) fun h ↦ by
          simpa only [Set.mem_ofPred_eq] using lt_trans (by norm_num : (1 / 2 : ℝ) < 1) h
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
    have hHs : H s ≠ 0 := hs.elim (fun h ↦ (hball h).2) fun h ↦
      hHne s (le_of_lt (by simpa only [Set.mem_ofPred_eq] using h))
    have hζ2 : DifferentiableAt ℂ (fun z : ℂ ↦ dedekindZeta K (2 * z)) s :=
      (analyticOnNhd_dedekindZeta K (2 * s) hs2).differentiableAt.comp s
        (differentiableAt_id.const_mul 2)
    exact (((differentiableAt_id.sub_const 1).mul hζ2).div
      (hHdiff.differentiableAt (hUopen.mem_nhds hsU)) hHs).differentiableWithinAt
  · intro s hs
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hs
    have hζne : dedekindZeta K s ≠ 0 := dedekindZeta_ne_zero_of_one_lt_re hs
    have hconv : dedekindZeta K (2 * s) = dedekindZeta K s *
        LSeries (normCoeff K (liouville K).toIdealArithmeticFunction) s := by
      rw [← LSeries_normCoeff_convolution_one_liouville,
        LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul hs
          (LSeriesSummable_normCoeff_of_isTrivialOnGood_sq (isTrivialOnGood_liouville_sq K) hs)]
    simp only [L, hHeq s hs, hconv]
    field_simp [hne, hζne]

end TauCeti.MultiplicativeIdealWeight
