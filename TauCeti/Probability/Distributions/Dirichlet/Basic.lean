/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.Distributions.Gamma.Pi

/-!
# The Dirichlet distribution

For a finite nonempty concentration vector `a`, the Dirichlet distribution is the law obtained by
normalizing independent unit-rate Gamma variables of shapes `a i` by their sum.  This file defines
that normalization and the resulting measure on `EuclideanSpace ℝ ι`.  The measure is
totalized to zero when the coordinate type is empty or any concentration parameter is
nonpositive.

For positive parameters, the Gamma product is almost surely contained in the strictly positive
orthant.  In particular, the denominator in the normalization is almost surely positive, the
resulting measure is a probability measure, and it is concentrated on the standard simplex.

## Main definitions and results

* `TauCeti.Probability.dirichletNormalize` normalizes a vector by its coordinate sum.
* `TauCeti.Probability.dirichletMeasure` is the Dirichlet measure obtained from independent Gamma
  variables.
* `TauCeti.Probability.isProbabilityMeasure_dirichletMeasure_iff` characterizes exactly when this
  totalized measure is a probability measure.
* `TauCeti.ae_pos_sum_pi_gammaMeasure` shows that the zero-denominator locus is null.
* `TauCeti.Probability.ae_mem_stdSimplex_dirichletMeasure` gives the standard-simplex support.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

/-! ### Coordinate normalization -/

/-- Normalize a real vector by the sum of its coordinates.

Lean's division on `ℝ` is totalized, so this map returns the zero vector when the coordinate sum
vanishes. -/
def dirichletNormalize (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm fun i ↦ x i / ∑ j, x j

/-- A coordinate of a normalized vector is the original coordinate divided by the total. -/
@[simp]
theorem dirichletNormalize_apply (x : ι → ℝ) (i : ι) :
    dirichletNormalize x i = x i / ∑ j, x j := by
  simp [dirichletNormalize]

/-- The coordinate-normalization map is measurable. -/
@[fun_prop]
theorem measurable_dirichletNormalize : Measurable (dirichletNormalize (ι := ι)) := by
  refine (EuclideanSpace.equiv ι ℝ).symm.continuous.measurable.comp
    (Measurable.of_eval fun i ↦ ?_)
  exact (measurable_pi_apply i).div
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

/-- A vector with zero coordinate sum is normalized to zero. -/
theorem dirichletNormalize_eq_zero_of_sum_eq_zero {x : ι → ℝ} (hx : ∑ i, x i = 0) :
    dirichletNormalize x = 0 := by
  apply (EuclideanSpace.equiv ι ℝ).injective
  ext i
  simp [dirichletNormalize, hx]

/-- The coordinates of a normalized vector with nonzero total sum to one. -/
theorem sum_dirichletNormalize {x : ι → ℝ} (hx : ∑ i, x i ≠ 0) :
    ∑ i, dirichletNormalize x i = 1 := by
  simp_rw [dirichletNormalize_apply]
  rw [← Finset.sum_div, div_self hx]

/-- Normalizing a nonnegative vector with nonzero total gives a point of the standard simplex. -/
theorem dirichletNormalize_mem_stdSimplex {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hsum : ∑ i, x i ≠ 0) :
    (EuclideanSpace.equiv ι ℝ) (dirichletNormalize x) ∈
      Set.range (fun p : StdSimplex ℝ ι ↦ (p.weights : ι → ℝ)) := by
  rw [StdSimplex.range_toFun_comp_weights]
  have hsum_nonneg : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ ↦ hx i
  constructor
  · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro i
    simp only [dirichletNormalize, ContinuousLinearEquiv.apply_symm_apply]
    exact div_nonneg (hx i) hsum_nonneg
  · simpa [dirichletNormalize] using sum_dirichletNormalize hsum

/-! ### The measure and its support -/

open Classical in
/-- The Dirichlet measure with concentration vector `a`.

For a positive concentration vector, this is the image of independent unit-rate Gamma laws under
coordinate normalization.  For an empty coordinate type or any other concentration vector, it is
the zero measure. -/
def dirichletMeasure (a : ι → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  if Nonempty ι ∧ ∀ i, 0 < a i then
    (Measure.pi fun i ↦ gammaMeasure (a i) 1).map dirichletNormalize
  else 0

/-- At a positive concentration vector, the Dirichlet measure is its defining Gamma
pushforward. -/
theorem dirichletMeasure_of_pos [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    dirichletMeasure a =
      (Measure.pi fun i ↦ gammaMeasure (a i) 1).map dirichletNormalize := by
  rw [dirichletMeasure, ite_eq_left ⟨inferInstance, ha⟩]

/-- An invalid concentration vector gives the zero Dirichlet measure. -/
@[simp]
theorem dirichletMeasure_of_not_pos {a : ι → ℝ} (ha : ¬∀ i, 0 < a i) :
    dirichletMeasure a = 0 := by
  rw [dirichletMeasure, ite_eq_right fun h ↦ ha h.2]

/-- A Dirichlet measure with positive concentration parameters is a probability measure. -/
theorem isProbabilityMeasure_dirichletMeasure [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    IsProbabilityMeasure (dirichletMeasure a) := by
  rw [dirichletMeasure_of_pos ha]
  let _ (i : ι) : IsProbabilityMeasure (gammaMeasure (a i) 1) :=
    isProbabilityMeasure_gammaMeasure (ha i) one_pos
  infer_instance

/-- The totalized Dirichlet measure is a probability measure exactly for a nonempty coordinate type
and positive concentration parameters. -/
@[simp]
theorem isProbabilityMeasure_dirichletMeasure_iff {a : ι → ℝ} :
    IsProbabilityMeasure (dirichletMeasure a) ↔ Nonempty ι ∧ ∀ i, 0 < a i := by
  constructor
  · intro h
    by_contra ha
    rw [dirichletMeasure, ite_eq_right ha] at h
    let _ : IsProbabilityMeasure (0 : Measure (EuclideanSpace ℝ ι)) := h
    exact (IsProbabilityMeasure.ne_zero (0 : Measure (EuclideanSpace ℝ ι))) rfl
  · rintro ⟨hι, ha⟩
    let _ : Nonempty ι := hι
    exact isProbabilityMeasure_dirichletMeasure ha

/-- Every coordinate is almost everywhere strictly positive under a Dirichlet law with positive
concentration parameters. -/
theorem ae_pos_dirichletMeasure [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ∀ᵐ x ∂dirichletMeasure a, ∀ i, 0 < x i := by
  rw [dirichletMeasure_of_pos ha]
  rw [ae_map_iff measurable_dirichletNormalize.aemeasurable]
  · filter_upwards [ae_pos_pi_gammaMeasure a (fun _ ↦ 1),
      ae_pos_sum_pi_gammaMeasure a (fun _ ↦ 1)] with x hx hsum
    intro i
    rw [dirichletNormalize_apply]
    exact div_pos (hx i) hsum
  · measurability

/-- A Dirichlet measure with positive concentration parameters is concentrated on the standard
simplex, represented in Euclidean coordinates. -/
theorem ae_mem_stdSimplex_dirichletMeasure [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ∀ᵐ x ∂dirichletMeasure a,
      (EuclideanSpace.equiv ι ℝ) x ∈
        Set.range (fun p : StdSimplex ℝ ι ↦ (p.weights : ι → ℝ)) := by
  rw [dirichletMeasure_of_pos ha]
  rw [ae_map_iff measurable_dirichletNormalize.aemeasurable]
  · filter_upwards [ae_pos_pi_gammaMeasure a (fun _ ↦ 1),
      ae_pos_sum_pi_gammaMeasure a (fun _ ↦ 1)] with x hx hsum
    exact dirichletNormalize_mem_stdSimplex (fun i ↦ (hx i).le) hsum.ne'
  · exact
      (StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ ι).isClosed_range.measurableSet.preimage
        (EuclideanSpace.equiv ι ℝ).continuous.measurable

end Probability

end TauCeti
