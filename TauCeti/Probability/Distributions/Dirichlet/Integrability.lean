/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.MixedMoments
import TauCeti.Probability.Distributions.Dirichlet.Aggregation
import TauCeti.Probability.Distributions.Dirichlet.StickBreaking.Basic
import TauCeti.Probability.Distributions.Beta.Basic

/-!
# Sharp integrability of Dirichlet mixed powers

For a Dirichlet vector with at least two coordinates and positive shapes `a`, the product
`∏ i, x i ^ q i` is integrable exactly when every shifted shape `a i + q i` is positive.
Together with `integral_prod_rpow_dirichletMeasure`, this gives the exact domain of the
Gamma-ratio moment formula. The one-coordinate exception is covered by
`integrable_prod_rpow_dirichletMeasure_of_card_eq_one`.

Necessity follows from the single-step Beta–Dirichlet factorization: after fixing a positive
remainder vector by Fubini, the mixed power becomes a nonzero constant times a Beta mixed
power. Its endpoint singularity detects the shifted shape of the distinguished coordinate.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem shiftedShape_none_pos [Nonempty ι] {a q : Option ι → ℝ}
    (ha : ∀ i, 0 < a i)
    (h : Integrable (fun x ↦ ∏ i, x i ^ q i) (dirichletMeasure a)) :
    0 < a none + q none := by
  have hA : 0 < ∑ i, a (some i) :=
    Finset.sum_pos (fun i _ ↦ ha (some i)) Finset.univ_nonempty
  let _ := isProbabilityMeasureBeta (ha none) hA
  let _ := isProbabilityMeasure_dirichletMeasure (fun i ↦ ha (some i))
  have hm : Measurable (fun x : EuclideanSpace ℝ (Option ι) ↦ ∏ i, x i ^ q i) := by
    fun_prop
  have hpull : Integrable (fun z ↦ ∏ i, dirichletStickInsert z i ^ q i)
      ((betaMeasure (a none) (∑ i, a (some i))).prod
        (dirichletMeasure fun i ↦ a (some i))) := by
    apply (integrable_map_measure hm.aestronglyMeasurable
      measurable_dirichletStickInsert.aemeasurable).1
    rwa [map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure ha]
  obtain ⟨y, hy, hypos⟩ :=
    (hpull.prod_left_ae.and (ae_pos_dirichletMeasure (a := fun i ↦ a (some i)))).exists
  have heq : (fun v ↦ ∏ i, dirichletStickInsert (v, y) i ^ q i) =ᵐ[
      betaMeasure (a none) (∑ i, a (some i))]
      (fun v ↦ (v ^ q none * (1 - v) ^ (∑ i, q (some i))) *
        ∏ i, y i ^ q (some i)) := by
    filter_upwards [ae_mem_Ioo_betaMeasure (a none) (∑ i, a (some i))] with v hv
    simp only [Fintype.prod_option, dirichletStickInsert_none, dirichletStickInsert_some]
    simp_rw [Real.mul_rpow (sub_pos.mpr hv.2).le (hypos _).le]
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (sub_pos.mpr hv.2)]
    ring
  have hc : (∏ i, y i ^ q (some i)) ≠ 0 :=
    (Finset.prod_pos (fun i _ ↦ Real.rpow_pos_of_pos (hypos i) _)).ne'
  have hbeta := (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr hc) _).1
    (hy.congr heq)
  exact ((integrable_rpow_mul_one_sub_rpow_betaMeasure_iff (ha none) hA).1 hbeta).1

/-- On a Dirichlet law with positive shapes and at least two coordinates, a mixed real power
is integrable exactly when every shifted shape is positive. In particular, equality at any
endpoint of this domain already gives non-integrability. -/
@[simp]
theorem integrable_prod_rpow_dirichletMeasure_iff {a q : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hcard : 2 ≤ Fintype.card ι) :
    Integrable (fun x ↦ ∏ i, x i ^ q i) (dirichletMeasure a) ↔
      ∀ i, 0 < a i + q i := by
  classical
  let _ : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨fun h i ↦ ?_, integrable_prod_rpow_dirichletMeasure⟩
  let κ := {j : ι // j ≠ i}
  let e : Option κ ≃ ι := Equiv.optionSubtypeNe i
  have : Nonempty κ := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨⟨j, hj⟩⟩
  have hparam (j : ι) : (∑ k with e k = j, a (e k)) = a j := by
    simp only [← e.eq_symm_apply, Finset.sum_filter]
    simp
  have hmap : (dirichletMeasure (fun k ↦ a (e k))).map (euclideanFiberSum e) =
      dirichletMeasure a := by
    simpa only [hparam] using
      map_euclideanFiberSum_dirichletMeasure e.surjective (fun k ↦ ha (e k))
  have hm : Measurable (fun x : EuclideanSpace ℝ ι ↦ ∏ j, x j ^ q j) := by fun_prop
  have hpull := (integrable_map_measure hm.aestronglyMeasurable
    (measurable_euclideanFiberSum e).aemeasurable).1 (hmap.symm ▸ h)
  have hprod (x : EuclideanSpace ℝ (Option κ)) :
      (∏ j, euclideanFiberSum e x j ^ q j) = ∏ k, x k ^ q (e k) := by
    rw [← e.prod_comp (fun j ↦ euclideanFiberSum e x j ^ q j)]
    apply Finset.prod_congr rfl
    intro k _
    simp [euclideanFiberSum_apply, e.injective.eq_iff, Finset.sum_filter]
  have hi := shiftedShape_none_pos (fun k ↦ ha (e k))
    (hpull.congr (Filter.Eventually.of_forall hprod))
  have henone : e none = i := Equiv.optionSubtypeNe_none i
  simpa only [henone] using hi

/-- A random vector with a positive-shape Dirichlet law on at least two coordinates has an
integrable mixed real power exactly when every shifted shape is positive. -/
theorem integrable_prod_rpow_of_hasLaw_dirichletMeasure_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
    {a q : ι → ℝ} (ha : ∀ i, 0 < a i) (hcard : 2 ≤ Fintype.card ι)
    (hX : HasLaw X (dirichletMeasure a) P) :
    Integrable (fun ω ↦ ∏ i, X ω i ^ q i) P ↔ ∀ i, 0 < a i + q i := by
  have hm : Measurable (fun x : EuclideanSpace ℝ ι ↦ ∏ i, x i ^ q i) := by fun_prop
  have h := integrable_prod_rpow_dirichletMeasure_iff (q := q) ha hcard
  rw [← hX.map_eq, integrable_map_measure hm.aestronglyMeasurable hX.aemeasurable] at h
  exact h

end TauCeti.Probability
