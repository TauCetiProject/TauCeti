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
private theorem map_reindexed_dirichletStickInsert_eq {K : Type*} [Fintype K] [Nonempty K]
    (e : Option K ≃ ι) {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ((betaMeasure (a (e none)) (∑ j : K, a (e (some j)))).prod
      (dirichletMeasure fun j ↦ a (e (some j)))).map
        (euclideanFiberSum e ∘ dirichletStickInsert) = dirichletMeasure a := by
  classical
  let a' : Option K → ℝ := fun j ↦ a (e j)
  have ha' (j : Option K) : 0 < a' j := ha (e j)
  rw [← Measure.map_map (measurable_euclideanFiberSum e)
    measurable_dirichletStickInsert,
    map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure ha',
    map_euclideanFiberSum_dirichletMeasure e.surjective ha']
  congr 1
  funext j
  rw [e.sum_fiber_eq]
  simp [a']

omit [Nonempty ι] in
private theorem prod_rpow_reindexed_dirichletStickInsert_ae {K : Type*}
    [Fintype K] [Nonempty K] (e : Option K ≃ ι) {a q : ι → ℝ}
    (ha : ∀ i, 0 < a i) :
    ∀ᵐ z ∂((betaMeasure (a (e none)) (∑ j : K, a (e (some j)))).prod
        (dirichletMeasure fun j ↦ a (e (some j)))),
      (∏ j, (euclideanFiberSum e (dirichletStickInsert z)) j ^ q j) =
        (z.1 ^ q (e none) * (1 - z.1) ^ (∑ j : K, q (e (some j)))) *
          ∏ j, z.2 j ^ q (e (some j)) := by
  have hsum_a : 0 < ∑ j : K, a (e (some j)) :=
    Finset.sum_pos (fun j _ ↦ ha (e (some j))) Finset.univ_nonempty
  let _ := isProbabilityMeasureBeta (ha (e none)) hsum_a
  let _ := isProbabilityMeasure_dirichletMeasure (fun j : K ↦ ha (e (some j)))
  apply Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop)) |>.2
  filter_upwards [ae_mem_Ioo_betaMeasure (a (e none))
    (∑ j : K, a (e (some j)))] with v hv
  filter_upwards [ae_pos_dirichletMeasure (a := fun j : K ↦ a (e (some j)))] with y hy
  rw [Fintype.prod_equiv e.symm
    (fun j ↦ (euclideanFiberSum e (dirichletStickInsert (v, y))) j ^ q j)
    (fun j ↦ dirichletStickInsert (v, y) j ^ q (e j))]
  · simp only [Fintype.prod_option, dirichletStickInsert_none,
      dirichletStickInsert_some]
    simp_rw [Real.mul_rpow (sub_pos.mpr hv.2).le (hy _).le]
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (sub_pos.mpr hv.2)]
    simp [mul_assoc]
  · intro j
    simp

private theorem Integrable.left_of_mul_prod_of_ae_pos {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {f : X → ℝ} {g : Y → ℝ}
    {mu : Measure X} {nu : Measure Y} [SFinite mu] [IsProbabilityMeasure nu]
    (hfg : Integrable (fun z ↦ f z.1 * g z.2) (mu.prod nu))
    (hg : ∀ᵐ y ∂nu, 0 < g y) : Integrable f mu := by
  obtain ⟨y, hgy, hy⟩ := (hg.and hfg.prod_left_ae).exists
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.2 hgy.ne') f).1 hy

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
    have he_none : e none = i := by rfl
    have hne : ∃ j, j ≠ i :=
      Fintype.exists_ne_of_one_lt_card (lt_of_lt_of_le one_lt_two hcard) i
    let _ : Nonempty κ := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    let mu := (betaMeasure (a (e none)) (∑ j : κ, a (e (some j)))).prod
      (dirichletMeasure fun j ↦ a (e (some j)))
    let insert := euclideanFiberSum e ∘ dirichletStickInsert
    let f : ℝ → ℝ := fun v ↦
      v ^ q (e none) * (1 - v) ^ (∑ j : κ, q (e (some j)))
    let g : EuclideanSpace ℝ κ → ℝ := fun y ↦ ∏ j, y j ^ q (e (some j))
    have hsum_a : 0 < ∑ j : κ, a (e (some j)) :=
      Finset.sum_pos (fun j _ ↦ ha (e (some j))) Finset.univ_nonempty
    have _ : IsProbabilityMeasure (betaMeasure (a (e none))
        (∑ j : κ, a (e (some j)))) :=
      isProbabilityMeasureBeta (ha (e none)) hsum_a
    have _ : IsProbabilityMeasure (dirichletMeasure fun j : κ ↦ a (e (some j))) :=
      isProbabilityMeasure_dirichletMeasure (fun j ↦ ha (e (some j)))
    -- Reindex the one-step stick-breaking representation so that its first coordinate is `i`.
    have hmap : Measure.map insert mu = dirichletMeasure a := by
      simpa [mu, insert] using map_reindexed_dirichletStickInsert_eq e ha
    have hinsert : Integrable ((fun x ↦ ∏ j, x j ^ q j) ∘ insert) mu := by
      have hi : Integrable (fun x ↦ ∏ j, x j ^ q j) (Measure.map insert mu) :=
        hmap.symm ▸ h
      exact (integrable_map_measure hi.aestronglyMeasurable
        (by fun_prop : AEMeasurable insert mu)).1 hi
    have hfactor : ∀ᵐ z ∂mu, ((fun x ↦ ∏ j, x j ^ q j) ∘ insert) z =
        f z.1 * g z.2 := by
      simpa [mu, insert, f, g] using
        prod_rpow_reindexed_dirichletStickInsert_ae e ha (q := q)
    have hsep : Integrable (fun z ↦ f z.1 * g z.2) mu := hinsert.congr hfactor
    have hpositive : ∀ᵐ y ∂(dirichletMeasure fun j : κ ↦ a (e (some j))), 0 < g y := by
      filter_upwards [ae_pos_dirichletMeasure (a := fun j : κ ↦ a (e (some j)))] with y hy
      exact Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hy j) _
    -- A positive Dirichlet slice lets product integrability descend to the Beta factor.
    have hf : Integrable f (betaMeasure (a (e none)) (∑ j : κ, a (e (some j)))) :=
      Integrable.left_of_mul_prod_of_ae_pos (by simpa [mu] using hsep) hpositive
    have hi := ((integrable_rpow_mul_one_sub_rpow_betaMeasure_iff
      (ha (e none)) hsum_a).1 (by simpa [f] using hf)).1
    simpa [he_none] using hi
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
