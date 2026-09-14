/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Basic

/-!
# Coordinates on the open simplex

Fixing a coordinate `i₀`, a point of the affine hyperplane whose coordinates sum to one is
determined by all coordinates except `i₀`.  The map `dirichletReconstruct` restores the omitted
coordinate.  Its natural open domain consists of positive displayed coordinates with sum less
than one, and it parametrizes exactly the strictly positive part of the standard simplex.

The scaled map `dirichletScale` adjoins a positive total mass.  It is a bijection from the product
of the open simplex chart and the positive half-line to the positive orthant; its inverse divides
by the coordinate sum.  These are the coordinates in which the product of independent Gamma
densities separates into a Dirichlet density and a Gamma density.

## Main results

* `TauCeti.Probability.dirichletReconstruct_image_source` identifies the open simplex chart.
* `TauCeti.Probability.dirichletScale_image_source` identifies the scaled chart with the positive
  orthant.
* `TauCeti.Probability.dirichletScale_injOn` gives the injectivity needed for change of variables.
* `TauCeti.Probability.dirichletNormalize_dirichletScale` relates these coordinates to the
  normalization used to define `dirichletMeasure`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open Set

namespace TauCeti

namespace Probability

open Classical in
section

variable {ι : Type*} [Fintype ι]

/-! ### The unscaled simplex chart -/

/-- The open coordinate region for the simplex chart omitting `i₀`: every displayed coordinate
is positive and their sum is less than one. -/
def dirichletChartSource (i₀ : ι) : Set ({i : ι // i ≠ i₀} → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∑ j, x j < 1}

/-- The strictly positive part of the affine simplex, written as functions whose coordinates sum
to one. -/
def dirichletChartTarget : Set (ι → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i = 1}

/-- Reconstruct a point whose coordinates sum to one by filling the coordinate `i₀` with one
minus the sum of the other coordinates. -/
def dirichletReconstruct (i₀ : ι) (x : {i : ι // i ≠ i₀} → ℝ) : ι → ℝ :=
  fun i ↦ if h : i = i₀ then 1 - ∑ j, x j else x ⟨i, h⟩

/-- The omitted coordinate of a reconstructed simplex point. -/
@[simp]
theorem dirichletReconstruct_apply_eq (i₀ : ι) (x : {i : ι // i ≠ i₀} → ℝ) :
    dirichletReconstruct i₀ x i₀ = 1 - ∑ j, x j := by
  simp [dirichletReconstruct]

/-- A displayed coordinate is unchanged by simplex reconstruction. -/
@[simp]
theorem dirichletReconstruct_apply_ne (i₀ : ι) (x : {i : ι // i ≠ i₀} → ℝ)
    (i : ι) (hi : i ≠ i₀) : dirichletReconstruct i₀ x i = x ⟨i, hi⟩ := by
  simp [dirichletReconstruct, hi]

/-- Restricting a reconstructed point to the displayed coordinates recovers the input. -/
@[simp]
theorem dirichletReconstruct_subtype (i₀ : ι) (x : {i : ι // i ≠ i₀} → ℝ)
    (j : {i : ι // i ≠ i₀}) : dirichletReconstruct i₀ x j = x j := by
  exact dirichletReconstruct_apply_ne i₀ x j j.property

/-- The coordinates of a reconstructed point sum to one. -/
@[simp]
theorem sum_dirichletReconstruct (i₀ : ι) (x : {i : ι // i ≠ i₀} → ℝ) :
    ∑ i, dirichletReconstruct i₀ x i = 1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  rw [dirichletReconstruct_apply_eq]
  simp_rw [dirichletReconstruct_subtype]
  ring

/-- Simplex reconstruction is injective. -/
theorem dirichletReconstruct_injective (i₀ : ι) :
    Function.Injective (dirichletReconstruct i₀) := by
  intro x y hxy
  funext j
  simpa using congrFun hxy j

/-- A function whose coordinates sum to one is recovered by restricting it away from `i₀` and
then reconstructing the omitted coordinate. -/
theorem dirichletReconstruct_restrict (i₀ : ι) {x : ι → ℝ} (hx : ∑ i, x i = 1) :
    dirichletReconstruct i₀ (fun j ↦ x j) = x := by
  funext i
  by_cases hi : i = i₀
  · subst i
    rw [dirichletReconstruct_apply_eq]
    rw [Fintype.sum_eq_add_sum_subtype_ne x i₀] at hx
    linarith
  · exact dirichletReconstruct_apply_ne i₀ _ i hi

/-- Reconstruction maps the open chart into the strictly positive simplex. -/
theorem dirichletReconstruct_mem_target {i₀ : ι} {x : {i : ι // i ≠ i₀} → ℝ}
    (hx : x ∈ dirichletChartSource i₀) :
    dirichletReconstruct i₀ x ∈ dirichletChartTarget := by
  refine ⟨fun i ↦ ?_, sum_dirichletReconstruct i₀ x⟩
  by_cases hi : i = i₀
  · subst i
    simpa using sub_pos.mpr hx.2
  · simpa [dirichletReconstruct_apply_ne i₀ x i hi] using hx.1 ⟨i, hi⟩

/-- Restricting a strictly positive simplex point gives a point of the open chart. -/
theorem restrict_mem_dirichletChartSource {i₀ : ι} {x : ι → ℝ}
    (hx : x ∈ dirichletChartTarget) :
    (fun j : {i : ι // i ≠ i₀} ↦ x j) ∈ dirichletChartSource i₀ := by
  rw [dirichletChartTarget] at hx
  rw [dirichletChartSource]
  simp only [Set.mem_ofPred_eq] at hx ⊢
  refine ⟨fun j ↦ hx.1 j, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne x i₀] at hx
  linarith [hx.1 i₀]

/-- The image of the open coordinate region is exactly the strictly positive simplex. -/
theorem dirichletReconstruct_image_source (i₀ : ι) :
    dirichletReconstruct i₀ '' dirichletChartSource i₀ = dirichletChartTarget := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact dirichletReconstruct_mem_target hx
  · intro x hx
    exact ⟨fun j ↦ x j, restrict_mem_dirichletChartSource hx,
      dirichletReconstruct_restrict i₀ hx.2⟩

/-- The simplex reconstruction map is continuous. -/
@[fun_prop]
theorem continuous_dirichletReconstruct (i₀ : ι) : Continuous (dirichletReconstruct i₀) := by
  apply continuous_pi
  intro i
  by_cases hi : i = i₀
  · simp only [dirichletReconstruct, dite_eq_left hi]
    fun_prop
  · simp only [dirichletReconstruct, dite_eq_right hi]
    fun_prop

/-- The simplex reconstruction map is measurable. -/
@[fun_prop]
theorem measurable_dirichletReconstruct (i₀ : ι) : Measurable (dirichletReconstruct i₀) :=
  (continuous_dirichletReconstruct i₀).measurable

/-- The open simplex-coordinate region is measurable. -/
theorem measurableSet_dirichletChartSource (i₀ : ι) :
    MeasurableSet (dirichletChartSource i₀) := by
  rw [dirichletChartSource, Set.ofPred_and]
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j : {i : ι // i ≠ i₀} ↦ ?_
    exact measurableSet_lt measurable_const (measurable_pi_apply j)
  · exact measurableSet_Iio.preimage (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

/-- The strictly positive affine simplex is measurable in the ambient coordinate space. -/
theorem measurableSet_dirichletChartTarget : MeasurableSet (dirichletChartTarget (ι := ι)) := by
  rw [dirichletChartTarget, Set.ofPred_and]
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const (measurable_pi_apply i)
  · exact measurableSet_eq_fun (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)
      measurable_const

/-! ### Adding the total mass -/

/-- The source region for scaled simplex coordinates: an open simplex chart together with a
positive total mass. -/
def dirichletScaleSource (i₀ : ι) : Set (({i : ι // i ≠ i₀} → ℝ) × ℝ) :=
  dirichletChartSource i₀ ×ˢ Ioi 0

/-- The target region for scaled simplex coordinates is the positive orthant. -/
def dirichletScaleTarget : Set (ι → ℝ) :=
  {x | ∀ i, 0 < x i}

/-- Scale a reconstructed simplex point by a total mass. -/
def dirichletScale (i₀ : ι) (z : ({i : ι // i ≠ i₀} → ℝ) × ℝ) : ι → ℝ :=
  z.2 • dirichletReconstruct i₀ z.1

/-- Recover the displayed proportions and total mass of a vector.  Division is totalized when the
coordinate sum vanishes; the inverse laws below apply on the positive orthant. -/
def dirichletUnscale (i₀ : ι) (y : ι → ℝ) : ({i : ι // i ≠ i₀} → ℝ) × ℝ :=
  (fun j ↦ y j / ∑ i, y i, ∑ i, y i)

/-- A coordinate of a scaled simplex point is its reconstructed proportion times the total. -/
@[simp]
theorem dirichletScale_apply (i₀ : ι) (z : ({i : ι // i ≠ i₀} → ℝ) × ℝ) (i : ι) :
    dirichletScale i₀ z i = z.2 * dirichletReconstruct i₀ z.1 i := by
  simp [dirichletScale]

/-- The coordinate sum of a scaled simplex point is its total-mass coordinate. -/
theorem sum_dirichletScale (i₀ : ι) (z : ({i : ι // i ≠ i₀} → ℝ) × ℝ) :
    ∑ i, dirichletScale i₀ z i = z.2 := by
  simp only [dirichletScale_apply, ← Finset.mul_sum, sum_dirichletReconstruct, mul_one]

/-- Scaling an open simplex-chart point by a positive total gives a vector in the positive
orthant. -/
theorem dirichletScale_mem_target {i₀ : ι}
    {z : ({i : ι // i ≠ i₀} → ℝ) × ℝ} (hz : z ∈ dirichletScaleSource i₀) :
    dirichletScale i₀ z ∈ dirichletScaleTarget := by
  have hr := dirichletReconstruct_mem_target hz.1
  intro i
  exact mul_pos hz.2 (hr.1 i)

/-- Unscaling a positive vector gives an open simplex-chart point and a positive total. -/
theorem dirichletUnscale_mem_source {i₀ : ι} {y : ι → ℝ} (hy : y ∈ dirichletScaleTarget) :
    dirichletUnscale i₀ y ∈ dirichletScaleSource i₀ := by
  have hsum : 0 < ∑ i, y i := Finset.sum_pos (fun i _ ↦ hy i) ⟨i₀, Finset.mem_univ _⟩
  refine ⟨⟨fun j ↦ div_pos (hy j) hsum, ?_⟩, hsum⟩
  simp only [dirichletUnscale]
  rw [← Finset.sum_div]
  apply (div_lt_one hsum).2
  rw [Fintype.sum_eq_add_sum_subtype_ne y i₀]
  linarith [hy i₀]

/-- Scaling is a left inverse to unscaling on the positive orthant. -/
theorem dirichletScale_dirichletUnscale {i₀ : ι} {y : ι → ℝ}
    (hy : y ∈ dirichletScaleTarget) : dirichletScale i₀ (dirichletUnscale i₀ y) = y := by
  have hsum : ∑ i, y i ≠ 0 :=
    (Finset.sum_pos (fun i _ ↦ hy i) ⟨i₀, Finset.mem_univ _⟩).ne'
  have hnorm : ∑ i, y i / ∑ i, y i = 1 := by
    rw [← Finset.sum_div, div_self hsum]
  rw [dirichletScale]
  simp only [dirichletUnscale]
  rw [dirichletReconstruct_restrict i₀ hnorm]
  funext i
  exact mul_div_cancel₀ (y i) hsum

/-- Unscaling is a left inverse to scaling on its source region. -/
theorem dirichletUnscale_dirichletScale {i₀ : ι}
    {z : ({i : ι // i ≠ i₀} → ℝ) × ℝ} (hz : z ∈ dirichletScaleSource i₀) :
    dirichletUnscale i₀ (dirichletScale i₀ z) = z := by
  have ht : z.2 ≠ 0 := ne_of_gt hz.2
  apply Prod.ext
  · funext j
    simp only [dirichletUnscale]
    rw [sum_dirichletScale, dirichletScale_apply, dirichletReconstruct_subtype]
    exact mul_div_cancel_left₀ _ ht
  · exact sum_dirichletScale i₀ z

/-- The scaled simplex chart maps its source region onto the positive orthant. -/
theorem dirichletScale_image_source (i₀ : ι) :
    dirichletScale i₀ '' dirichletScaleSource i₀ = dirichletScaleTarget := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact dirichletScale_mem_target hz
  · intro y hy
    exact ⟨dirichletUnscale i₀ y, dirichletUnscale_mem_source hy,
      dirichletScale_dirichletUnscale hy⟩

/-- The scaled simplex chart is injective on its source region. -/
theorem dirichletScale_injOn (i₀ : ι) :
    Set.InjOn (dirichletScale i₀) (dirichletScaleSource i₀) := by
  intro z hz w hw hzw
  rw [← dirichletUnscale_dirichletScale hz, ← dirichletUnscale_dirichletScale hw, hzw]

/-- The scaled simplex chart is measurable. -/
@[fun_prop]
theorem measurable_dirichletScale (i₀ : ι) : Measurable (dirichletScale i₀) := by
  unfold dirichletScale
  fun_prop

/-- The inverse scaled simplex chart is measurable. -/
@[fun_prop]
theorem measurable_dirichletUnscale (i₀ : ι) : Measurable (dirichletUnscale i₀) := by
  unfold dirichletUnscale
  fun_prop

/-- The scaled simplex source region is measurable. -/
theorem measurableSet_dirichletScaleSource (i₀ : ι) :
    MeasurableSet (dirichletScaleSource i₀) :=
  (measurableSet_dirichletChartSource i₀).prod measurableSet_Ioi

omit [Fintype ι] in
/-- The positive orthant is measurable. -/
theorem measurableSet_dirichletScaleTarget [Countable ι] :
    MeasurableSet (dirichletScaleTarget (ι := ι)) := by
  rw [dirichletScaleTarget, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const (measurable_pi_apply i)

/-- On the scaled chart source, Gamma-vector normalization forgets precisely the total-mass
coordinate. -/
theorem dirichletNormalize_dirichletScale {i₀ : ι}
    {z : ({i : ι // i ≠ i₀} → ℝ) × ℝ} (hz : z ∈ dirichletScaleSource i₀) :
    dirichletNormalize (dirichletScale i₀ z) =
      (EuclideanSpace.equiv ι ℝ).symm (dirichletReconstruct i₀ z.1) := by
  have ht : z.2 ≠ 0 := ne_of_gt hz.2
  ext i
  rw [dirichletNormalize_apply, sum_dirichletScale, dirichletScale_apply]
  exact mul_div_cancel_left₀ _ ht

end

end Probability

end TauCeti
