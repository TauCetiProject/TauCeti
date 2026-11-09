/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Density
import TauCeti.Probability.Distributions.Dirichlet.Aggregation
import TauCeti.Probability.Distributions.Dirichlet.StickBreaking
import TauCeti.Probability.Distributions.Beta.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mixed power moments of the Dirichlet distribution

Products of real powers of Dirichlet coordinates have a Gamma-ratio integral whenever adding
each exponent to its concentration parameter leaves it positive. This includes negative
exponents, and in particular gives every natural mixed moment. These integrals also evaluate
the masses obtained by mixing multinomial laws against a Dirichlet law.

When there are at least two coordinates, the shifted-parameter condition is also necessary.
This is proved by splitting off each coordinate in turn: the split coordinate is Beta-distributed
and independent of the normalized remainder, so Fubini reduces each endpoint threshold to the
sharp mixed-power criterion for a Beta law. The one-coordinate law is instead concentrated at
the constant vector `1`, and hence has every real mixed moment.

The moment computation uses `dirichletMeasure_eq_map_withDensity_dirichletChartPDF`:
multiplication by a monomial shifts the exponents in the chart density, and the shifted density
has mass one. On a one-element coordinate type every mixed power is identically one almost
surely, without any restriction on its exponent.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

section

variable [Nonempty ι]

private theorem dirichletChartPDFReal_mul_prod_rpow [DecidableEq ι]
    {a q : ι → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 < a i + q i)
    (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) :
    dirichletChartPDFReal a i₀ x * (∏ i, dirichletChart i₀ x i ^ q i) =
      (Real.Gamma (∑ i, a i) / Real.Gamma (∑ i, (a i + q i)) *
        ∏ i, Real.Gamma (a i + q i) / Real.Gamma (a i)) *
      dirichletChartPDFReal (fun i ↦ a i + q i) i₀ x := by
  by_cases hx : x ∈ dirichletChartRegion i₀
  · have hΓa : (∏ i, Real.Gamma (a i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ (Real.Gamma_pos_of_pos (ha i)).ne'
    have hΓq : (∏ i, Real.Gamma (a i + q i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ (Real.Gamma_pos_of_pos (hq i)).ne'
    have hΓsum : Real.Gamma (∑ i, (a i + q i)) ≠ 0 :=
      (Real.Gamma_pos_of_pos (Finset.sum_pos (fun i _ ↦ hq i)
        Finset.univ_nonempty)).ne'
    have hdensity (b : ι → ℝ) : dirichletChartPDFReal b i₀ x =
        (Real.Gamma (∑ i, b i) / ∏ i, Real.Gamma (b i)) *
          ∏ i, dirichletChart i₀ x i ^ (b i - 1) := by
      have hp := Fintype.prod_eq_mul_prod_subtype_ne
        (fun i ↦ dirichletChart i₀ x i ^ (b i - 1)) i₀
      rw [dirichletChartPDFReal_of_mem b hx, hp]
      simp only [dirichletChart_apply_self, dirichletChart_apply_coe]
      ring
    have hpowers : (∏ i, dirichletChart i₀ x i ^ (a i - 1)) *
        (∏ i, dirichletChart i₀ x i ^ q i) =
        ∏ i, dirichletChart i₀ x i ^ (a i + q i - 1) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.rpow_add (dirichletChart_pos hx i)]
      congr 1
      ring
    rw [hdensity a, hdensity (fun i ↦ a i + q i), mul_assoc, hpowers,
      Finset.prod_div_distrib]
    field_simp
  · simp [dirichletChartPDFReal_of_notMem _ hx]

private theorem dirichletMomentConst_nonneg {a q : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 < a i + q i) :
    0 ≤ Real.Gamma (∑ i, a i) / Real.Gamma (∑ i, (a i + q i)) *
      ∏ i, Real.Gamma (a i + q i) / Real.Gamma (a i) := by
  exact mul_nonneg
    (div_nonneg (Real.Gamma_pos_of_pos
      (Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty)).le
      (Real.Gamma_pos_of_pos
        (Finset.sum_pos (fun i _ ↦ hq i) Finset.univ_nonempty)).le)
    (Finset.prod_nonneg fun i _ ↦ div_nonneg
      (Real.Gamma_pos_of_pos (hq i)).le (Real.Gamma_pos_of_pos (ha i)).le)

/-- The nonnegative extended integral of a mixed real power under a Dirichlet law, when every
shifted concentration parameter is positive. -/
theorem lintegral_prod_rpow_dirichletMeasure {a q : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 < a i + q i) :
    ∫⁻ x, ENNReal.ofReal (∏ i, x i ^ q i) ∂dirichletMeasure a =
      ENNReal.ofReal (Real.Gamma (∑ i, a i) / Real.Gamma (∑ i, (a i + q i)) *
        ∏ i, Real.Gamma (a i + q i) / Real.Gamma (a i)) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  have hm : Measurable fun x : EuclideanSpace ℝ ι ↦ ENNReal.ofReal (∏ i, x i ^ q i) := by
    fun_prop
  rw [dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha i₀,
    lintegral_map hm measurable_dirichletChart,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_dirichletChartPDF a i₀)
      (by fun_prop)]
  have heq (x : {i // i ≠ i₀} → ℝ) :
      dirichletChartPDF a i₀ x * ENNReal.ofReal (∏ i, dirichletChart i₀ x i ^ q i) =
        ENNReal.ofReal (Real.Gamma (∑ i, a i) / Real.Gamma (∑ i, (a i + q i)) *
          ∏ i, Real.Gamma (a i + q i) / Real.Gamma (a i)) *
        dirichletChartPDF (fun i ↦ a i + q i) i₀ x := by
    simp only [dirichletChartPDF_eq_ofReal]
    rw [← ENNReal.ofReal_mul (dirichletChartPDFReal_nonneg ha i₀ x),
      dirichletChartPDFReal_mul_prod_rpow ha hq]
    exact ENNReal.ofReal_mul (dirichletMomentConst_nonneg ha hq)
  simp_rw [Pi.mul_apply, heq]
  rw [lintegral_const_mul _ (measurable_dirichletChartPDF _ i₀),
    lintegral_dirichletChartPDF_eq_one hq i₀, mul_one]

omit [Nonempty ι] in
private theorem ae_nonneg_prod_rpow_dirichletMeasure {a q : ι → ℝ} :
    0 ≤ᵐ[dirichletMeasure a] fun x ↦ ∏ i, x i ^ q i := by
  filter_upwards [ae_pos_dirichletMeasure (a := a)] with x hx
  exact Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hx i).le _

omit [Nonempty ι] in
/-- A mixed real power is integrable under a Dirichlet law if each exponent added to its
concentration parameter is positive. Negative exponents are allowed. For invalid parameters or
an empty coordinate type, the measure is zero. -/
theorem integrable_prod_rpow_dirichletMeasure {a q : ι → ℝ}
    (hq : ∀ i, 0 < a i + q i) :
    Integrable (fun x ↦ ∏ i, x i ^ q i) (dirichletMeasure a) := by
  by_cases h : Nonempty ι ∧ ∀ i, 0 < a i
  · let : Nonempty ι := h.1
    have hm : Measurable fun x : EuclideanSpace ℝ ι ↦ ∏ i, x i ^ q i := by fun_prop
    refine ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal ae_nonneg_prod_rpow_dirichletMeasure).2 ?_⟩
    rw [lintegral_prod_rpow_dirichletMeasure h.2 hq]
    exact ENNReal.ofReal_lt_top
  · rw [dirichletMeasure_eq_zero_of_invalid h]
    simp

omit [Nonempty ι] in
private theorem euclideanFiberSum_equiv_apply {K : Type*} [Fintype K]
    (e : ι ≃ K) (x : EuclideanSpace ℝ ι) (j : K) :
    euclideanFiberSum e x j = x (e.symm j) := by
  classical
  rw [euclideanFiberSum_apply]
  simp only [← e.eq_symm_apply]
  rw [Finset.filter_eq' Finset.univ (e.symm j)]
  simp

omit [Nonempty ι] in
/-- For a Dirichlet law with at least two coordinates, a mixed real power is integrable exactly
when every exponent stays above its coordinate's endpoint singularity threshold. -/
theorem integrable_prod_rpow_dirichletMeasure_iff {a q : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hcard : 2 ≤ Fintype.card ι) :
    Integrable (fun x ↦ ∏ i, x i ^ q i) (dirichletMeasure a) ↔
      ∀ i, 0 < a i + q i := by
  classical
  constructor
  · intro h i
    let κ := {j // j ≠ i}
    let e : Option κ ≃ ι := Equiv.optionSubtypeNe i
    let a' : Option κ → ℝ := fun j ↦ a (e j)
    let q' : Option κ → ℝ := fun j ↦ q (e j)
    have hne : ∃ j, j ≠ i :=
      Fintype.exists_ne_of_one_lt_card (lt_of_lt_of_le one_lt_two hcard) i
    let _ : Nonempty κ := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    have ha' (j : Option κ) : 0 < a' j := ha (e j)
    have hsum_a : 0 < ∑ j : κ, a' (some j) :=
      Finset.sum_pos (fun j _ ↦ ha' (some j)) Finset.univ_nonempty
    let μ := (betaMeasure (a i) (∑ j : κ, a' (some j))).prod
      (dirichletMeasure fun j ↦ a' (some j))
    let insert : ℝ × EuclideanSpace ℝ κ → EuclideanSpace ℝ ι := fun z ↦
      euclideanFiberSum e (dirichletStickInsert z)
    have ha_none : a' none = a i := by rfl
    have hq_none : q' none = q i := by rfl
    have hμ : μ = (betaMeasure (a' none) (∑ j : κ, a' (some j))).prod
        (dirichletMeasure fun j ↦ a' (some j)) := by
      rw [ha_none]
    have hmap : μ.map insert = dirichletMeasure a := by
      rw [hμ]
      change (((betaMeasure (a' none) (∑ j : κ, a' (some j))).prod
        (dirichletMeasure fun j ↦ a' (some j))).map
          (euclideanFiberSum e ∘ dirichletStickInsert) = dirichletMeasure a)
      rw [← Measure.map_map (measurable_euclideanFiberSum e)
        measurable_dirichletStickInsert,
        map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure ha',
        map_euclideanFiberSum_dirichletMeasure e.surjective ha']
      congr 1
      funext j
      simp only [← e.eq_symm_apply]
      rw [Finset.filter_eq' Finset.univ (e.symm j)]
      simp [a', e]
    have hinsert : Integrable (fun z ↦ ∏ j, insert z j ^ q j) μ := by
      have hi : Integrable (fun x ↦ ∏ j, x j ^ q j) (μ.map insert) := hmap.symm ▸ h
      change Integrable ((fun x ↦ ∏ j, x j ^ q j) ∘ insert) μ
      exact (integrable_map_measure hi.aestronglyMeasurable
        (by fun_prop : AEMeasurable insert μ)).1 hi
    let f : ℝ → ℝ := fun v ↦ v ^ q i * (1 - v) ^ (∑ j : κ, q' (some j))
    let g : EuclideanSpace ℝ κ → ℝ := fun y ↦ ∏ j, y j ^ q' (some j)
    have _ : IsProbabilityMeasure (betaMeasure (a i) (∑ j : κ, a' (some j))) :=
      isProbabilityMeasureBeta (ha i) hsum_a
    have _ : IsProbabilityMeasure (dirichletMeasure fun j : κ ↦ a' (some j)) :=
      isProbabilityMeasure_dirichletMeasure (fun j ↦ ha' (some j))
    have hfactor : (∀ᵐ z ∂μ, (∏ j, insert z j ^ q j) = f z.1 * g z.2) := by
      change ∀ᵐ z ∂((betaMeasure (a i) (∑ j : κ, a' (some j))).prod
        (dirichletMeasure fun j ↦ a' (some j))),
          (∏ j, insert z j ^ q j) = f z.1 * g z.2
      apply Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop)) |>.2
      filter_upwards [ae_mem_Ioo_betaMeasure (a i) (∑ j : κ, a' (some j))] with v hv
      filter_upwards [ae_pos_dirichletMeasure (a := fun j : κ ↦ a' (some j))] with y hy
      rw [Fintype.prod_equiv e.symm (fun j ↦ insert (v, y) j ^ q j)
        (fun j ↦ dirichletStickInsert (v, y) j ^ q' j)]
      · simp only [Fintype.prod_option, dirichletStickInsert_none,
          dirichletStickInsert_some]
        simp_rw [Real.mul_rpow (sub_pos.mpr hv.2).le (hy _).le]
        rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (sub_pos.mpr hv.2)]
        simp [f, g, hq_none, mul_assoc]
      · intro j
        change (euclideanFiberSum e (dirichletStickInsert (v, y)) j) ^ q j = _
        rw [euclideanFiberSum_equiv_apply]
        simp [q', e]
    have hsep : Integrable (fun z ↦ f z.1 * g z.2) μ := hinsert.congr hfactor
    have hslice : ∀ᵐ y ∂(dirichletMeasure fun j : κ ↦ a' (some j)),
        Integrable (fun v ↦ f v * g y)
          (betaMeasure (a i) (∑ j : κ, a' (some j))) :=
      (show Integrable (fun z ↦ f z.1 * g z.2)
          ((betaMeasure (a i) (∑ j : κ, a' (some j))).prod
            (dirichletMeasure fun j ↦ a' (some j))) from by simpa [μ] using hsep).prod_left_ae
    have hpositive : ∀ᵐ y ∂(dirichletMeasure fun j : κ ↦ a' (some j)), 0 < g y := by
      filter_upwards [ae_pos_dirichletMeasure (a := fun j : κ ↦ a' (some j))] with y hy
      exact Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hy j) _
    obtain ⟨y, hgy, hy⟩ := (hpositive.and hslice).exists
    have hf : Integrable f (betaMeasure (a i) (∑ j : κ, a' (some j))) :=
      (integrable_mul_const_iff (isUnit_iff_ne_zero.2 hgy.ne') f).1 hy
    exact ((integrable_rpow_mul_one_sub_rpow_betaMeasure_iff (ha i) hsum_a).1
      (by simpa [f, a', e] using hf)).1
  · exact integrable_prod_rpow_dirichletMeasure

/-- The mixed real-power moment of a Dirichlet law is the ratio of the original and shifted
normalizing constants. -/
theorem integral_prod_rpow_dirichletMeasure {a q : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 < a i + q i) :
    ∫ x, (∏ i, x i ^ q i) ∂dirichletMeasure a =
      Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + ∑ i, q i) *
        ∏ i, Real.Gamma (a i + q i) / Real.Gamma (a i) := by
  rw [integral_eq_lintegral_of_nonneg_ae ae_nonneg_prod_rpow_dirichletMeasure
    (integrable_prod_rpow_dirichletMeasure hq).aestronglyMeasurable,
    lintegral_prod_rpow_dirichletMeasure ha hq,
    ENNReal.toReal_ofReal (dirichletMomentConst_nonneg ha hq), Finset.sum_add_distrib]

omit [Nonempty ι] in
/-- Every natural mixed moment of a Dirichlet law is integrable, including for invalid parameters
or an empty coordinate type, when the measure is zero. -/
theorem integrable_prod_pow_dirichletMeasure (a : ι → ℝ)
    (k : ι → ℕ) : Integrable (fun x ↦ ∏ i, x i ^ k i) (dirichletMeasure a) := by
  by_cases h : Nonempty ι ∧ ∀ i, 0 < a i
  · simpa only [Real.rpow_natCast] using integrable_prod_rpow_dirichletMeasure
      (q := fun i ↦ (k i : ℝ)) (fun i ↦ add_pos_of_pos_of_nonneg (h.2 i) (Nat.cast_nonneg _))
  · rw [dirichletMeasure_eq_zero_of_invalid h]
    simp

/-- Natural mixed moments of a Dirichlet law, including the zeroth moment. -/
theorem integral_prod_pow_dirichletMeasure {a : ι → ℝ} (ha : ∀ i, 0 < a i) (k : ι → ℕ) :
    ∫ x, (∏ i, x i ^ k i) ∂dirichletMeasure a =
      Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + ∑ i, (k i : ℝ)) *
        ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i) := by
  simpa only [Real.rpow_natCast] using integral_prod_rpow_dirichletMeasure ha
    (q := fun i ↦ (k i : ℝ)) (fun i ↦ add_pos_of_pos_of_nonneg (ha i) (Nat.cast_nonneg _))

end

/-- On a one-coordinate Dirichlet law every real mixed power is integrable, even when the
shifted concentration parameter is nonpositive. For invalid parameters, the measure is zero. -/
theorem integrable_prod_rpow_dirichletMeasure_of_card_eq_one {a : ι → ℝ}
    (hcard : Fintype.card ι = 1) (q : ι → ℝ) :
    Integrable (fun x ↦ ∏ i, x i ^ q i) (dirichletMeasure a) := by
  by_cases h : Nonempty ι ∧ ∀ i, 0 < a i
  · rw [dirichletMeasure_eq_dirac_of_card_eq_one h.2 hcard]
    exact integrable_dirac (by simp)
  · rw [dirichletMeasure_eq_zero_of_invalid h]
    simp

/-- On a one-coordinate Dirichlet law every mixed real-power moment is one, with no
restriction on the exponent. -/
theorem integral_prod_rpow_dirichletMeasure_of_card_eq_one {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hcard : Fintype.card ι = 1) (q : ι → ℝ) :
    ∫ x, (∏ i, x i ^ q i) ∂dirichletMeasure a = 1 := by
  rw [dirichletMeasure_eq_dirac_of_card_eq_one ha hcard]
  simp

end TauCeti.Probability
