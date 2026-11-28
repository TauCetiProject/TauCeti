/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Quadratic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Liouville
public import TauCeti.NumberTheory.ArithmeticFunction.DilateSq
import Mathlib.Algebra.GroupWithZero.Torsion
import TauCeti.Algebra.Group.Submonoid.Operations
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Multiplicative
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.LSeries.Term
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Ideal convolution and continuation of the ideal Liouville weight

Let `K` be a number field and `λ_K = TauCeti.MultiplicativeIdealWeight.liouville K` the ideal
Liouville weight taking value `-1` at every height-one prime. Since `λ_K ^ 2 = 1`, `λ_K` satisfies
`(λ_K ^ 2).IsTrivialOnGood`, so the convolution theory of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Convolution/Quadratic.lean` applies. This file
collects the exact identities and sharpness counterexamples for `1 * λ_K` and `L(λ_K, ·)`:

* at every nonzero integral ideal `A`, `(1 * λ_K)(A) = 1` if `A` is a square ideal `B ^ 2` and `0`
  otherwise (`TauCeti.convolution_one_liouville_apply`);
* regrouping by absolute norm identifies `normCoeff K (1 * λ_K)` with the square dilation
  `(normCoeff K 1).dilateSq` (`TauCeti.normCoeff_convolution_one_liouville_eq_dilateSq`), matching
  `(normCoeff K 1) m` at `m ^ 2` and vanishing off the squares;
* as a totalized `LSeries` identity, `L(1 * λ_K, s) = ζ_K(2s)` holds for **every** `s : ℂ`
  (`TauCeti.LSeries_normCoeff_convolution_one_liouville`), while the series converges (absolutely)
  specifically on `Re s > 1 / 2`
  (`TauCeti.LSeriesSummable_normCoeff_convolution_one_liouville_iff`), showing that the abscissa
  lower bound `1 / 2` in `TauCeti.half_le_abscissaOfAbsConv_normCoeff_convolution_one` is sharp
  (`TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_liouville`);
* on `Re s > 1`, `L(λ_K, s) = ζ_K(2s) / ζ_K(s)` extends holomorphically across `s = 1` to a
  function vanishing at `s = 1` (`TauCeti.MultiplicativeIdealWeight.`
  `exists_differentiableOn_eqOn_LSeries_liouville_and_apply_one_eq_zero`),
  demonstrating that local analytic continuation across `s = 1` alone does not prevent `L 1 = 0`.

## Main results

* `TauCeti.convolution_one_liouville_apply` and
  `TauCeti.normCoeff_convolution_one_liouville_eq_dilateSq`: ideal-level and norm-regrouped
  formulas for `1 * λ_K`.
* `TauCeti.LSeries_normCoeff_convolution_one_liouville`,
  `TauCeti.LSeriesSummable_normCoeff_convolution_one_liouville_iff`,
  `TauCeti.abscissaOfAbsConv_normCoeff_convolution_one_liouville`: totalized `L`-series identity
  and exact abscissa of absolute convergence `1 / 2`.
* `TauCeti.MultiplicativeIdealWeight.`
  `exists_differentiableOn_eqOn_LSeries_liouville_and_apply_one_eq_zero`:
  local continuation counterexample with `L 1 = 0`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* The Dirichlet-character prototype is Mathlib's `zetaMul` positivity and Liouville
  counterexample in `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll,
  David Loeffler, and Terence Tao).
-/

public section

namespace TauCeti

open Complex IsDedekindDomain NumberField
open scoped ComplexOrder nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- **Ideal convolution with the Liouville weight detects square ideals.** For every nonzero
integral ideal `A`, `(1 * λ_K)(A)` equals `1` if `A` is the square of a nonzero ideal and `0`
otherwise. -/
theorem convolution_one_liouville_apply (A : (Ideal (𝓞 K))⁰) :
    IdealArithmeticFunction.convolution 1
        (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction A =
      if ∃ B : (Ideal (𝓞 K))⁰, A = B ^ 2 then 1 else 0 := by
  obtain ⟨S, e, hA⟩ := Ideal.exists_eq_prod_pow (mem_nonZeroDivisors_iff_ne_zero.mp A.property)
  have hmul : (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction).IsMultiplicative :=
    IdealArithmeticFunction.isMultiplicative_one.convolution
      (MultiplicativeIdealWeight.liouville K).isMultiplicative_toIdealArithmeticFunction
  rw [hmul.map_prod_pow S e A hA]
  have hprod :
      ∏ P ∈ S, IdealArithmeticFunction.convolution 1
          (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction
          (P.primeIdealPow (e P)) =
        ∏ P ∈ S, (if Even (e P) then (1 : ℂ) else 0) :=
    Finset.prod_congr rfl fun P _ ↦
      convolution_one_primeIdealPow_of_apply_eq_neg_one
        (MultiplicativeIdealWeight.liouville_prime K P) (e P)
  rw [hprod]
  by_cases hall : ∀ P ∈ S, Even (e P)
  · have hsq : ∃ B : (Ideal (𝓞 K))⁰, A = B ^ 2 := by
      refine ⟨∏ P ∈ S, P.primeIdealPow (e P / 2), Subtype.ext ?_⟩
      rw [hA, SubmonoidClass.coe_pow, Submonoid.coe_finsetProd, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun P hP ↦ ?_
      rw [HeightOneSpectrum.coe_primeIdealPow, ← pow_mul,
        Nat.div_mul_cancel (even_iff_two_dvd.mp (hall P hP))]
    rw [ite_eq_left hsq]
    exact Finset.prod_eq_one fun P hP ↦ ite_eq_left (hall P hP)
  · push Not at hall
    obtain ⟨P, hPS, hPodd⟩ := hall
    have hPne : ¬ Even (e P) := Nat.not_even_iff_odd.mpr hPodd
    have hnsq : ¬ ∃ B : (Ideal (𝓞 K))⁰, A = B ^ 2 := by
      rintro ⟨B, rfl⟩
      exact hPne (even_of_sq_eq_prod_pow
        (by simpa [SubmonoidClass.coe_pow] using hA) hPS)
    rw [ite_eq_right hnsq]
    exact Finset.prod_eq_zero hPS (ite_eq_right hPne)

open Classical in
/-- **Norm coefficients of `1 * λ_K` are the square dilation of `normCoeff K 1`.** At a square
`m ^ 2` the norm coefficient equals `normCoeff K 1 m`, and off the squares it vanishes. -/
theorem normCoeff_convolution_one_liouville_eq_dilateSq :
    normCoeff K (IdealArithmeticFunction.convolution 1
        (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction) =
      ArithmeticFunction.dilateSq (normCoeff K (1 : IdealArithmeticFunction K)) := by
  ext n
  by_cases hn : IsSquare n
  · obtain ⟨m, rfl⟩ := hn
    rw [← sq, ArithmeticFunction.dilateSq_apply_sq,
      normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
    simp_rw [convolution_one_liouville_apply]
    simp only [Finset.sum_boole, Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    symm
    refine Finset.card_bij (fun B _ ↦ B ^ 2) ?_
      (fun _ _ _ _ h ↦ pow_left_injective two_ne_zero h) ?_
    · intro B hB
      exact Finset.mem_filter.mpr ⟨(sq_mem_normFiber_iff K B m).mpr hB, ⟨B, rfl⟩⟩
    · intro A hA
      obtain ⟨hAm, B, rfl⟩ := Finset.mem_filter.mp hA
      exact ⟨B, (sq_mem_normFiber_iff K B m).mp hAm, rfl⟩
  · rw [ArithmeticFunction.dilateSq_apply_of_not_isSquare _ hn, normCoeff_eq_sum_normFiber]
    refine Finset.sum_eq_zero fun A hA ↦ ?_
    rw [convolution_one_liouville_apply, ite_eq_right]
    rintro ⟨B, rfl⟩
    exact hn ⟨Ideal.absNorm (B : Ideal (𝓞 K)), by
      rw [← (mem_normFiber K).mp hA, SubmonoidClass.coe_pow, map_pow, sq]⟩

/-- **Totalized `LSeries` identity for `1 * λ_K`.** For every `s : ℂ`, the `tsum`-defined
`LSeries` of `1 * λ_K` at `s` equals `ζ_K(2s)` (both sides being totalized by `0` outside
their half-plane of convergence `Re s > 1 / 2`, where `LSeries` is the convergent Dirichlet series
by `LSeriesSummable_normCoeff_convolution_one_liouville_iff`). -/
theorem LSeries_normCoeff_convolution_one_liouville (s : ℂ) :
    LSeries (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) s =
      dedekindZeta K (2 * s) := by
  rw [dedekindZeta_eq_LSeries_normCoeff_one, LSeries, LSeries,
    normCoeff_convolution_one_liouville_eq_dilateSq]
  refine (Function.Injective.tsum_eq (Nat.pow_left_injective two_ne_zero) ?_).symm.trans
    (tsum_congr fun m ↦ ?_)
  · intro n hn
    by_contra hnot
    have hnsq : ¬ IsSquare n := by
      rintro ⟨m, rfl⟩
      exact hnot ⟨m, sq m⟩
    simp [LSeries.term, ArithmeticFunction.dilateSq_apply_of_not_isSquare _ hnsq] at hn
  · rw [TauCeti.LSeries.term_sq]
    simp [LSeries.term]

/-- The Dirichlet series of `1 * λ_K` converges absolutely exactly on `Re s > 1 / 2`. -/
theorem LSeriesSummable_normCoeff_convolution_one_liouville_iff {s : ℂ} :
    LSeriesSummable (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) s ↔ 1 / 2 < s.re := by
  rw [LSeriesSummable, normCoeff_convolution_one_liouville_eq_dilateSq,
    ← (Nat.pow_left_injective two_ne_zero).summable_iff fun n hn ↦ by
      have hnsq : ¬ IsSquare n := by
        rintro ⟨m, rfl⟩
        exact hn ⟨m, sq m⟩
      simp [LSeries.term, ArithmeticFunction.dilateSq_apply_of_not_isSquare _ hnsq]]
  have hfun :
      (LSeries.term ⇑(ArithmeticFunction.dilateSq
        (normCoeff K (1 : IdealArithmeticFunction K))) s) ∘ (· ^ 2) =
        LSeries.term (normCoeff K (1 : IdealArithmeticFunction K)) (2 * s) := by
    ext m
    rw [Function.comp_apply, TauCeti.LSeries.term_sq]
    simp [LSeries.term]
  rw [hfun, ← LSeriesSummable, LSeriesSummable_normCoeff_one_iff]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  constructor <;> intro h <;> linarith

/-- **Sharpness of the lower bound `1 / 2`.** The ideal Liouville weight satisfies
`((liouville K) ^ 2).IsTrivialOnGood` and its convolution `1 * λ_K` has exact abscissa of absolute
convergence `1 / 2`. -/
theorem abscissaOfAbsConv_normCoeff_convolution_one_liouville :
    LSeries.abscissaOfAbsConv (normCoeff K (IdealArithmeticFunction.convolution 1
      (MultiplicativeIdealWeight.liouville K).toIdealArithmeticFunction)) =
        ((1 / 2 : ℝ) : EReal) := by
  refine le_antisymm ?_
    (half_le_abscissaOfAbsConv_normCoeff_convolution_one
      (MultiplicativeIdealWeight.isTrivialOnGood_liouville_sq K))
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy ↦
    (LSeriesSummable_normCoeff_convolution_one_liouville_iff (K := K)).mpr (by simpa using hy)

namespace MultiplicativeIdealWeight

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

end MultiplicativeIdealWeight

end TauCeti
