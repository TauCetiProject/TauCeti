/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.MeasureTheory.Constructions.Pi
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import TauCeti.Probability.Distributions.PDFInstances

/-!
# The density of the Dirichlet distribution in a simplex chart

The Dirichlet law is carried by the standard simplex, which lies inside the affine hyperplane
`∑ i, x i = 1` of `EuclideanSpace ℝ ι`, so it has no density against the ambient volume.  This
file gives its density in the chart that drops one coordinate: after choosing `i₀ : ι`, a point of
the simplex is determined by its coordinates away from `i₀`, the coordinate at `i₀` being the
remaining mass `1 - ∑ j, x j`.

The Dirichlet law is defined by normalizing independent unit-rate Gamma coordinates by their
total, so the density comes from a change of variables that separates that total from the point of
the simplex it normalizes to.  Writing the Gamma coordinates as `(s, y)` with `s` the total and `y`
the chart coordinates, the change of variables has Jacobian `s ^ (card ι - 1)`, and the transported
Gamma product density factors as the chart density times a Gamma density of shape `∑ i, a i` in
`s`.  Integrating `s` out leaves the chart density.

## Main definitions

* `TauCeti.Probability.dirichletChart` reconstructs a point of `EuclideanSpace ℝ ι` from its
  coordinates away from `i₀`;
* `TauCeti.Probability.dirichletChartRegion` is the part of the chart mapping onto the strictly
  positive part of the simplex;
* `TauCeti.Probability.dirichletChartPDFReal` and `TauCeti.Probability.dirichletChartPDF` are the
  real- and `ℝ≥0∞`-valued densities in that chart, which describe the Dirichlet law at a positive
  concentration vector;
* `TauCeti.Probability.dirichletUnchart` and `TauCeti.Probability.dirichletChartCoords` are the
  two directions of the scaling change of variables, between
  `TauCeti.Probability.dirichletUnchartSource` and `TauCeti.Probability.dirichletUnchartTarget`.

## Main results

* `TauCeti.Probability.det_fderiv_dirichletUnchart` and
  `TauCeti.Probability.map_dirichletUnchart_withDensity` are the Jacobian of the scaling change of
  variables and the resulting identity of Lebesgue measures;
* `TauCeti.Probability.dirichletMeasure_eq_map_withDensity_dirichletChartPDF` presents the
  Dirichlet law as the image, under the chart, of Lebesgue measure on the remaining coordinates
  weighted by `TauCeti.Probability.dirichletChartPDF`;
* `TauCeti.Probability.lintegral_dirichletChartPDF_eq_one` records that this density has total
  mass one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/
public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι}

/-! ### The simplex chart -/

/-- Reconstruct a point of `EuclideanSpace ℝ ι` from its coordinates away from `i₀`, assigning the
remaining mass `1 - ∑ j, x j` to the coordinate `i₀`. -/
def dirichletChart (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm ((Equiv.funSplitAt i₀ ℝ).symm (1 - ∑ j, x j, x))

/-- The coordinate of a reconstructed point at the dropped index is the remaining mass. -/
@[simp]
theorem dirichletChart_apply_self (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) :
    dirichletChart i₀ x i₀ = 1 - ∑ j, x j := by
  simp [dirichletChart]

/-- The chart keeps the displayed coordinates. -/
@[simp]
theorem dirichletChart_apply_coe (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) (j : {i // i ≠ i₀}) :
    dirichletChart i₀ x j = x j := by
  simp [dirichletChart, j.2]

/-- The value of the chart at an index other than `i₀`, indexed by `ι` rather than by the
subtype. -/
@[simp]
theorem dirichletChart_apply_of_ne {i : ι} (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) (h : i ≠ i₀) :
    dirichletChart i₀ x i = x ⟨i, h⟩ :=
  dirichletChart_apply_coe i₀ x ⟨i, h⟩

/-- The chart is continuous. -/
@[fun_prop]
theorem continuous_dirichletChart : Continuous (dirichletChart i₀) := by
  refine (EuclideanSpace.equiv ι ℝ).symm.continuous.comp (continuous_pi fun i ↦ ?_)
  simp only [Equiv.funSplitAt_symm_apply]
  split_ifs with h
  · fun_prop
  · fun_prop

/-- The chart is measurable. -/
@[fun_prop]
theorem measurable_dirichletChart : Measurable (dirichletChart i₀) :=
  continuous_dirichletChart.measurable

/-- The coordinates of a reconstructed point sum to one. -/
@[simp]
theorem sum_dirichletChart (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) :
    ∑ i, dirichletChart i₀ x i = 1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ dirichletChart i₀ x i) i₀]
  simp

/-- The chart is injective. -/
theorem dirichletChart_injective (i₀ : ι) :
    Function.Injective (dirichletChart i₀ (ι := ι)) := fun _ _ hxy ↦
  congrArg Prod.snd ((Equiv.funSplitAt i₀ ℝ).symm.injective
    ((EuclideanSpace.equiv ι ℝ).symm.injective hxy))

/-- The chart recovers a point of `EuclideanSpace ℝ ι` from its own coordinates away from `i₀`
exactly when the coordinates of that point sum to one: the image of the chart is the whole
hyperplane `∑ i, p i = 1`. -/
theorem dirichletChart_eq_self_iff (i₀ : ι) (p : EuclideanSpace ℝ ι) :
    dirichletChart i₀ (fun j : {i // i ≠ i₀} ↦ p j) = p ↔ ∑ i, p i = 1 := by
  have hsplit : ∑ i, p i = p i₀ + ∑ j : {i // i ≠ i₀}, p j :=
    Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ p i) i₀
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact sum_dirichletChart i₀ _
  · ext i
    by_cases hi : i = i₀
    · subst hi
      rw [dirichletChart_apply_self]
      linarith
    · rw [dirichletChart_apply_of_ne i₀ _ hi]

/-- The chart region: the coordinate vectors with positive coordinates of total less than one.
These are exactly the ones the chart sends to points of the standard simplex all of whose
coordinates are strictly positive, that is, to its relative interior inside the affine hyperplane
`∑ i, x i = 1`.  The simplex has empty interior in the ambient `EuclideanSpace ℝ ι`. -/
def dirichletChartRegion (i₀ : ι) : Set ({i // i ≠ i₀} → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∑ j, x j < 1}

/-- Membership in the chart region, unfolded. -/
@[simp]
theorem mem_dirichletChartRegion_iff {x : {i // i ≠ i₀} → ℝ} :
    x ∈ dirichletChartRegion i₀ ↔ (∀ j, 0 < x j) ∧ ∑ j, x j < 1 := Iff.rfl

/-- The chart region is open. -/
theorem isOpen_dirichletChartRegion (i₀ : ι) : IsOpen (dirichletChartRegion i₀) := by
  have h₁ : IsOpen {x : {i // i ≠ i₀} → ℝ | ∀ j, 0 < x j} := by
    simpa only [Set.ofPred_forall] using
      isOpen_iInter_of_finite fun j ↦ isOpen_lt continuous_const (continuous_apply j)
  rw [dirichletChartRegion, Set.ofPred_and]
  exact h₁.inter (isOpen_lt (by fun_prop) continuous_const)

/-- The chart region is measurable. -/
theorem measurableSet_dirichletChartRegion (i₀ : ι) :
    MeasurableSet (dirichletChartRegion i₀) :=
  (isOpen_dirichletChartRegion i₀).measurableSet

/-- On the chart region every reconstructed coordinate is strictly positive. -/
theorem dirichletChart_pos {x : {i // i ≠ i₀} → ℝ} (hx : x ∈ dirichletChartRegion i₀) (i : ι) :
    0 < dirichletChart i₀ x i := by
  by_cases h : i = i₀
  · simpa [h] using sub_pos.mpr hx.2
  · simpa [dirichletChart_apply_of_ne i₀ x h] using hx.1 ⟨i, h⟩

/-- The chart carries the chart region onto the points of the standard simplex all of whose
coordinates are strictly positive. -/
theorem dirichletChart_image_region (i₀ : ι) :
    dirichletChart i₀ '' dirichletChartRegion i₀
      = {p : EuclideanSpace ℝ ι | (∀ i, 0 < p i) ∧ ∑ i, p i = 1} := by
  refine Set.Subset.antisymm ?_ fun p hp ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨dirichletChart_pos hx, sum_dirichletChart i₀ x⟩
  · have hsplit : ∑ i, p i = p i₀ + ∑ j : {i // i ≠ i₀}, p j :=
      Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ p i) i₀
    have hi₀ : 0 < p i₀ := hp.1 i₀
    have hsum : ∑ j : {i // i ≠ i₀}, p j < 1 := by
      have := hp.2
      linarith
    exact ⟨fun j : {i // i ≠ i₀} ↦ p j, ⟨fun j ↦ hp.1 j, hsum⟩,
      (dirichletChart_eq_self_iff i₀ p).2 hp.2⟩

/-! ### The chart density -/

open Classical in
/-- The real-valued density of the Dirichlet law with concentration vector `a` in the chart at
`i₀`, with respect to Lebesgue measure on the coordinates away from `i₀`.  It vanishes outside the
chart region.

The formula is defined for every `a`, but it describes `dirichletMeasure a` only for a positive
concentration vector: outside that range the Dirichlet measure is zero while this formula is
not. -/
def dirichletChartPDFReal (a : ι → ℝ) (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) : ℝ :=
  if x ∈ dirichletChartRegion i₀ then
    (Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) * (∏ j, x j ^ (a j - 1)) *
      (1 - ∑ j, x j) ^ (a i₀ - 1)
  else 0

/-- The `ℝ≥0∞`-valued density of the Dirichlet law in the chart at `i₀`.  As for
`TauCeti.Probability.dirichletChartPDFReal`, it describes the Dirichlet law at a positive
concentration vector. -/
def dirichletChartPDF (a : ι → ℝ) (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (dirichletChartPDFReal a i₀ x)

/-- The `ℝ≥0∞`-valued chart density is `ENNReal.ofReal` of the real-valued one. -/
theorem dirichletChartPDF_eq_ofReal (a : ι → ℝ) (i₀ : ι) (x : {i // i ≠ i₀} → ℝ) :
    dirichletChartPDF a i₀ x = ENNReal.ofReal (dirichletChartPDFReal a i₀ x) := by
  rw [dirichletChartPDF]

/-- The value of the chart density on the chart region. -/
@[simp]
theorem dirichletChartPDFReal_of_mem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∈ dirichletChartRegion i₀) :
    dirichletChartPDFReal a i₀ x =
      (Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) * (∏ j, x j ^ (a j - 1)) *
        (1 - ∑ j, x j) ^ (a i₀ - 1) :=
  ite_eq_left hx

/-- The chart density vanishes off the chart region. -/
@[simp]
theorem dirichletChartPDFReal_of_notMem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∉ dirichletChartRegion i₀) :
    dirichletChartPDFReal a i₀ x = 0 :=
  ite_eq_right hx

/-- The `ℝ≥0∞`-valued chart density vanishes off the chart region. -/
@[simp]
theorem dirichletChartPDF_of_notMem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∉ dirichletChartRegion i₀) :
    dirichletChartPDF a i₀ x = 0 := by
  rw [dirichletChartPDF_eq_ofReal, dirichletChartPDFReal_of_notMem a hx, ENNReal.ofReal_zero]

/-- The value of the `ℝ≥0∞`-valued chart density on the chart region. -/
@[simp]
theorem dirichletChartPDF_of_mem (a : ι → ℝ) {x : ({i // i ≠ i₀}) → ℝ}
    (hx : x ∈ dirichletChartRegion i₀) :
    dirichletChartPDF a i₀ x = ENNReal.ofReal
      ((Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) * (∏ j, x j ^ (a j - 1)) *
        (1 - ∑ j, x j) ^ (a i₀ - 1)) := by
  rw [dirichletChartPDF_eq_ofReal, dirichletChartPDFReal_of_mem a hx]

/-- The chart density is nonnegative at a positive concentration vector. -/
theorem dirichletChartPDFReal_nonneg {a : ι → ℝ} (ha : ∀ i, 0 < a i) (i₀ : ι)
    (x : {i // i ≠ i₀} → ℝ) :
    0 ≤ dirichletChartPDFReal a i₀ x := by
  rw [dirichletChartPDFReal]
  split_ifs with hx
  · have hΓ : 0 < Real.Gamma (∑ i, a i) :=
      Real.Gamma_pos_of_pos (Finset.sum_pos (fun i _ ↦ ha i) ⟨i₀, Finset.mem_univ i₀⟩)
    have hΓ' : 0 < ∏ i, Real.Gamma (a i) :=
      Finset.prod_pos fun i _ ↦ Real.Gamma_pos_of_pos (ha i)
    have h₁ : 0 ≤ ∏ j, x j ^ (a j - 1) :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx.1 j).le _
    have h₂ : 0 ≤ (1 - ∑ j, x j) ^ (a i₀ - 1) :=
      Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _
    positivity
  · exact le_rfl

/-- The chart density is measurable. -/
@[fun_prop]
theorem measurable_dirichletChartPDFReal (a : ι → ℝ) (i₀ : ι) :
    Measurable (dirichletChartPDFReal a i₀) := by
  classical
  refine Measurable.ite (measurableSet_dirichletChartRegion i₀) ?_ measurable_const
  refine ((measurable_const.mul ?_).mul ?_)
  · exact Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
  · exact (measurable_const.sub
      (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)).pow_const _

/-- The `ℝ≥0∞`-valued chart density is measurable. -/
@[fun_prop]
theorem measurable_dirichletChartPDF (a : ι → ℝ) (i₀ : ι) :
    Measurable (dirichletChartPDF a i₀) :=
  (measurable_dirichletChartPDFReal a i₀).ennreal_ofReal

/-! ### The scaling change of variables -/

/-- Reconstruct the raw coordinates from a total `z.1` and a point `z.2` of the chart: the
coordinate at `i₀` is `z.1 * (1 - ∑ j, z.2 j)` and the coordinate at `j` is `z.1 * z.2 j`. -/
def dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ × ({i // i ≠ i₀} → ℝ) :=
  (z.1 * (1 - ∑ j, z.2 j), fun j ↦ z.1 * z.2 j)

/-- The reconstructed coordinate at the dropped index `i₀`. -/
@[simp]
theorem dirichletUnchart_fst (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (dirichletUnchart i₀ z).1 = z.1 * (1 - ∑ j, z.2 j) := by
  simp [dirichletUnchart]

/-- The reconstructed coordinate at an index other than `i₀`. -/
@[simp]
theorem dirichletUnchart_snd_apply (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ))
    (j : {i // i ≠ i₀}) : (dirichletUnchart i₀ z).2 j = z.1 * z.2 j := by
  simp [dirichletUnchart]

/-- Read off the total of the raw coordinates together with the chart coordinates they normalize
to, the coordinate at `i₀` being carried separately as `z.1`. -/
def dirichletChartCoords (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ × ({i // i ≠ i₀} → ℝ) :=
  (z.1 + ∑ j, z.2 j, fun j ↦ z.2 j / (z.1 + ∑ j, z.2 j))

/-- The total of the raw coordinates. -/
@[simp]
theorem dirichletChartCoords_fst (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (dirichletChartCoords i₀ z).1 = z.1 + ∑ j, z.2 j := by
  simp [dirichletChartCoords]

/-- The chart coordinate at `j`: the raw coordinate there divided by the total. -/
@[simp]
theorem dirichletChartCoords_snd_apply (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ))
    (j : {i // i ≠ i₀}) : (dirichletChartCoords i₀ z).2 j = z.2 j / (z.1 + ∑ j, z.2 j) := by
  simp [dirichletChartCoords]

/-- The source region of the scaling change of variables: a positive total together with a point
of the chart region. -/
def dirichletUnchartSource (i₀ : ι) : Set (ℝ × ({i // i ≠ i₀} → ℝ)) :=
  Ioi 0 ×ˢ dirichletChartRegion i₀

/-- Membership in the source region, unfolded. -/
@[simp]
theorem mem_dirichletUnchartSource_iff {z : ℝ × ({i // i ≠ i₀} → ℝ)} :
    z ∈ dirichletUnchartSource i₀ ↔ 0 < z.1 ∧ (∀ j, 0 < z.2 j) ∧ ∑ j, z.2 j < 1 := Iff.rfl

/-- The target region of the scaling change of variables: the open positive orthant. -/
def dirichletUnchartTarget (i₀ : ι) : Set (ℝ × ({i // i ≠ i₀} → ℝ)) :=
  Ioi 0 ×ˢ {y | ∀ j, 0 < y j}

omit [Fintype ι] [DecidableEq ι] in
/-- Membership in the target region, unfolded. -/
@[simp]
theorem mem_dirichletUnchartTarget_iff {z : ℝ × ({i // i ≠ i₀} → ℝ)} :
    z ∈ dirichletUnchartTarget i₀ ↔ 0 < z.1 ∧ ∀ j, 0 < z.2 j := Iff.rfl

/-- The scaling map is measurable. -/
@[fun_prop]
theorem measurable_dirichletUnchart (i₀ : ι) : Measurable (dirichletUnchart i₀) := by
  unfold dirichletUnchart
  fun_prop

/-- The coordinate map is measurable. -/
@[fun_prop]
theorem measurable_dirichletChartCoords (i₀ : ι) : Measurable (dirichletChartCoords i₀) := by
  have hsum : Measurable fun z : ℝ × ({i // i ≠ i₀} → ℝ) ↦ z.1 + ∑ j, z.2 j :=
    measurable_fst.add (Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).comp
      measurable_snd)
  exact hsum.prodMk (Measurable.of_eval fun j ↦
    ((measurable_pi_apply j).comp measurable_snd).div hsum)

/-- The source region is measurable. -/
theorem measurableSet_dirichletUnchartSource (i₀ : ι) :
    MeasurableSet (dirichletUnchartSource i₀) :=
  measurableSet_Ioi.prod (measurableSet_dirichletChartRegion i₀)

omit [Fintype ι] [DecidableEq ι] in
/-- The target region is measurable. -/
theorem measurableSet_dirichletUnchartTarget [Countable ι] (i₀ : ι) :
    MeasurableSet (dirichletUnchartTarget i₀) := by
  refine measurableSet_Ioi.prod ?_
  simpa only [Set.ofPred_forall] using
    MeasurableSet.iInter fun j ↦ measurableSet_lt measurable_const (measurable_pi_apply j)

/-- The scaling map sends the source region into the target region. -/
theorem dirichletUnchart_mem_target {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartSource i₀) : dirichletUnchart i₀ z ∈ dirichletUnchartTarget i₀ := by
  obtain ⟨hs, hy⟩ := hz
  exact ⟨mul_pos hs (sub_pos.mpr hy.2), fun j ↦ mul_pos hs (hy.1 j)⟩

/-- The coordinate map sends the target region into the source region. -/
theorem dirichletChartCoords_mem_source {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartTarget i₀) :
    dirichletChartCoords i₀ z ∈ dirichletUnchartSource i₀ := by
  obtain ⟨hu, hv⟩ := hz
  have hu' : 0 < z.1 := hu
  have hsum : 0 < z.1 + ∑ j, z.2 j :=
    add_pos_of_pos_of_nonneg hu' (Finset.sum_nonneg fun j _ ↦ (hv j).le)
  refine ⟨hsum, fun j ↦ div_pos (hv j) hsum, ?_⟩
  simp only [dirichletChartCoords_snd_apply, ← Finset.sum_div]
  rw [div_lt_one hsum]
  linarith

/-- The coordinate map inverts the scaling map on the source region. -/
theorem dirichletChartCoords_dirichletUnchart {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartSource i₀) :
    dirichletChartCoords i₀ (dirichletUnchart i₀ z) = z := by
  obtain ⟨hs, hy⟩ := hz
  have hs' : 0 < z.1 := hs
  have hsum : z.1 * (1 - ∑ j, z.2 j) + ∑ j, z.1 * z.2 j = z.1 := by
    rw [← Finset.mul_sum]; ring
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simpa [dirichletChartCoords_fst] using hsum
  · simp only [dirichletChartCoords_snd_apply, dirichletUnchart_fst,
      dirichletUnchart_snd_apply, hsum]
    field_simp

/-- The scaling map inverts the coordinate map on the target region. -/
theorem dirichletUnchart_dirichletChartCoords {i₀ : ι} {z : ℝ × ({i // i ≠ i₀} → ℝ)}
    (hz : z ∈ dirichletUnchartTarget i₀) :
    dirichletUnchart i₀ (dirichletChartCoords i₀ z) = z := by
  obtain ⟨hu, hv⟩ := hz
  have hu' : 0 < z.1 := hu
  have hsum : 0 < z.1 + ∑ j, z.2 j :=
    add_pos_of_pos_of_nonneg hu' (Finset.sum_nonneg fun j _ ↦ (hv j).le)
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp only [dirichletUnchart_fst, dirichletChartCoords_fst, dirichletChartCoords_snd_apply,
      ← Finset.sum_div]
    field_simp
    ring
  · simp only [dirichletUnchart_snd_apply, dirichletChartCoords_fst,
      dirichletChartCoords_snd_apply]
    rw [mul_comm, div_mul_cancel₀ _ hsum.ne']

/-- The scaling map is injective on the source region. -/
theorem dirichletUnchart_injOn (i₀ : ι) :
    Set.InjOn (dirichletUnchart i₀) (dirichletUnchartSource i₀) := fun z hz w hw h ↦ by
  rw [← dirichletChartCoords_dirichletUnchart hz, ← dirichletChartCoords_dirichletUnchart hw, h]

/-- The scaling map carries the source region onto the target region. -/
theorem dirichletUnchart_image_source (i₀ : ι) :
    dirichletUnchart i₀ '' dirichletUnchartSource i₀ = dirichletUnchartTarget i₀ := by
  refine Set.Subset.antisymm ?_ fun z hz ↦ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact dirichletUnchart_mem_target hz
  · exact ⟨dirichletChartCoords i₀ z, dirichletChartCoords_mem_source hz,
      dirichletUnchart_dirichletChartCoords hz⟩

/-- The derivative of `TauCeti.Probability.dirichletUnchart` at `z`. -/
def fderivDirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (ℝ × ({i // i ≠ i₀} → ℝ)) →L[ℝ] ℝ × ({i // i ≠ i₀} → ℝ) :=
  (((1 - ∑ j, z.2 j) • ContinuousLinearMap.fst ℝ ℝ ({i // i ≠ i₀} → ℝ)) -
      z.1 • ((∑ j, ContinuousLinearMap.proj j) ∘L
        ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ({i // i ≠ i₀} → ℝ)).smulRight z.2 +
      z.1 • ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))

/-- The value of the derivative of the scaling map. -/
@[simp]
theorem fderivDirichletUnchart_apply (i₀ : ι) (z w : ℝ × ({i // i ≠ i₀} → ℝ)) :
    fderivDirichletUnchart i₀ z w =
      (w.1 * (1 - ∑ j, z.2 j) - z.1 * ∑ j, w.2 j, fun j ↦ w.1 * z.2 j + z.1 * w.2 j) := by
  refine Prod.ext ?_ (funext fun j ↦ ?_) <;>
    simp [fderivDirichletUnchart, Finset.mul_sum, mul_comm]

/-- The stated continuous linear map is the derivative of the scaling map. -/
theorem hasFDerivAt_dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    HasFDerivAt (dirichletUnchart i₀) (fderivDirichletUnchart i₀ z) z := by
  have hfst : HasFDerivAt (fun w : ℝ × ({i // i ≠ i₀} → ℝ) ↦ w.1)
      (ContinuousLinearMap.fst ℝ ℝ ({i // i ≠ i₀} → ℝ)) z := hasFDerivAt_fst
  have hsnd (j : {i // i ≠ i₀}) : HasFDerivAt (fun w : ℝ × ({i // i ≠ i₀} → ℝ) ↦ w.2 j)
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))) z :=
    ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ))).hasFDerivAt
  have hsum : HasFDerivAt (fun w : ℝ × ({i // i ≠ i₀} → ℝ) ↦ 1 - ∑ j, w.2 j)
      (-((∑ j, ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.snd ℝ ℝ ({i // i ≠ i₀} → ℝ)))) z := by
    refine ((hasFDerivAt_const (1 : ℝ) z).fun_sub
      (HasFDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) ↦ hsnd j)).congr_fderiv ?_
    rw [zero_sub, ContinuousLinearMap.finsetSum_comp]
  unfold dirichletUnchart
  refine HasFDerivAt.prodMk ?_ ?_
  · refine (hfst.fun_mul hsum).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [sub_apply, add_apply, smul_apply, neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring
  · rw [hasFDerivAt_pi']
    intro j
    refine (hfst.fun_mul (hsnd j)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.proj_apply, add_apply, smul_apply, Pi.add_apply, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring

/-- `TauCeti.Probability.fderivDirichletUnchart` is the Fréchet derivative of the scaling map. -/
theorem fderiv_dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    fderiv ℝ (dirichletUnchart i₀) z = fderivDirichletUnchart i₀ z :=
  (hasFDerivAt_dirichletUnchart i₀ z).fderiv

/-- The Jacobian determinant of the scaling change of variables is the total raised to the number
of coordinates other than `i₀`. -/
theorem det_fderiv_dirichletUnchart (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) :
    (fderiv ℝ (dirichletUnchart i₀) z).det = z.1 ^ Fintype.card {i // i ≠ i₀} := by
  classical
  rw [fderiv_dirichletUnchart]
  set M : Matrix (Unit ⊕ {i // i ≠ i₀}) (Unit ⊕ {i // i ≠ i₀}) ℝ :=
    Matrix.fromBlocks (Matrix.of fun _ _ ↦ 1 - ∑ j, z.2 j) (Matrix.of fun _ _ ↦ -z.1)
      (Matrix.of fun j _ ↦ z.2 j) (Matrix.diagonal fun _ ↦ z.1) with hM
  have htoMatrix : LinearMap.toMatrix
      ((Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ ({i // i ≠ i₀})))
      ((Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ ({i // i ≠ i₀})))
      (fderivDirichletUnchart i₀ z :
        (ℝ × ({i // i ≠ i₀} → ℝ)) →ₗ[ℝ] ℝ × ({i // i ≠ i₀} → ℝ)) = M := by
    ext (i | i) (j | j) <;>
      simp [hM, LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  have hdet : M.det = z.1 ^ Fintype.card {i // i ≠ i₀} := by
    set T : Matrix (Unit ⊕ {i // i ≠ i₀}) (Unit ⊕ {i // i ≠ i₀}) ℝ :=
      Matrix.fromBlocks 1 (Matrix.of fun _ _ ↦ (1 : ℝ)) 0 1 with hT
    have hTdet : T.det = 1 := by
      rw [hT, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
    have hTM : T * M =
        Matrix.fromBlocks 1 0 (Matrix.of fun j _ ↦ z.2 j) (Matrix.diagonal fun _ ↦ z.1) := by
      ext (i | i) (j | j) <;>
        simp [hT, hM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
          Matrix.diagonal_apply, eq_comm]
    have hsplit : M.det = (T * M).det := by rw [Matrix.det_mul, hTdet, one_mul]
    rw [hsplit, hTM, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    ((Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ ({i // i ≠ i₀}))), htoMatrix, hdet]

/-- The Jacobian formula for the scaling change of variables, as an equality of restricted
Lebesgue measures. -/
theorem map_dirichletUnchart_withDensity (i₀ : ι) :
    Measure.map (dirichletUnchart i₀)
        ((volume.restrict (dirichletUnchartSource i₀)).withDensity
          fun z ↦ ENNReal.ofReal (z.1 ^ Fintype.card {i // i ≠ i₀})) =
      volume.restrict (dirichletUnchartTarget i₀) := by
  let _ : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ({i // i ≠ i₀} → ℝ))) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have heq : (fun z : ℝ × ({i // i ≠ i₀} → ℝ) ↦
        ENNReal.ofReal (z.1 ^ Fintype.card {i // i ≠ i₀}))
      =ᵐ[volume.restrict (dirichletUnchartSource i₀)]
      fun z ↦ ENNReal.ofReal |(fderivDirichletUnchart i₀ z).det| := by
    filter_upwards [ae_restrict_mem (measurableSet_dirichletUnchartSource i₀)] with z hz
    have hz1 : 0 < z.1 := hz.1
    rw [← fderiv_dirichletUnchart, det_fderiv_dirichletUnchart, abs_of_pos (pow_pos hz1 _)]
  rw [withDensity_congr_ae heq, ← dirichletUnchart_image_source]
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume
    (measurableSet_dirichletUnchartSource i₀).nullMeasurableSet
    (fun z _ ↦ (hasFDerivAt_dirichletUnchart i₀ z).hasFDerivWithinAt)
    (dirichletUnchart_injOn i₀)

/-! ### The density computation -/

/-- Transported through the scaling change of variables and weighted by its Jacobian, the Gamma
product density in the split coordinates is the product of the chart density and the Gamma density
of the total. -/
private theorem dirichletUnchart_density_real {a : ι → ℝ} (ha : ∀ i, 0 < a i) (i₀ : ι) {s : ℝ}
    (hs : 0 < s) {y : {i // i ≠ i₀} → ℝ} (hy : y ∈ dirichletChartRegion i₀) :
    s ^ Fintype.card {i // i ≠ i₀} *
        (gammaPDFReal (a i₀) 1 (s * (1 - ∑ j, y j)) *
          ∏ j : {i // i ≠ i₀}, gammaPDFReal (a j) 1 (s * y j)) =
      gammaPDFReal (∑ i, a i) 1 s * dirichletChartPDFReal a i₀ y := by
  -- The unit-rate case of the closed formula for the Gamma density.
  have hone : ∀ {b x : ℝ}, 0 < x →
      gammaPDFReal b 1 x = x ^ (b - 1) * Real.exp (-x) / Real.Gamma b := fun hx ↦ by
    rw [gammaPDFReal_of_nonneg hx.le, Real.one_rpow, one_mul]
    ring
  have hu : 0 < 1 - ∑ j, y j := sub_pos.mpr hy.2
  have hA : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) ⟨i₀, Finset.mem_univ i₀⟩
  have hΓA : Real.Gamma (∑ i, a i) ≠ 0 := (Real.Gamma_pos_of_pos hA).ne'
  have hΓ₀ : Real.Gamma (a i₀) ≠ 0 := (Real.Gamma_pos_of_pos (ha i₀)).ne'
  have hΓJ : (∏ j : {i // i ≠ i₀}, Real.Gamma (a j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ (Real.Gamma_pos_of_pos (ha j)).ne'
  have hsplitΓ : ∏ i, Real.Gamma (a i)
      = Real.Gamma (a i₀) * ∏ j : {i // i ≠ i₀}, Real.Gamma (a j) :=
    Fintype.prod_eq_mul_prod_subtype_ne _ i₀
  have hsplitA : ∑ i, a i = a i₀ + ∑ j : {i // i ≠ i₀}, a j :=
    Fintype.sum_eq_add_sum_subtype_ne a i₀
  -- The product of the coordinate densities away from `i₀`, with the total factored out.
  have hprod : (∏ j : {i // i ≠ i₀}, gammaPDFReal (a j) 1 (s * y j))
      = s ^ ((∑ j : {i // i ≠ i₀}, a j) - (Fintype.card {i // i ≠ i₀} : ℝ)) *
          (∏ j : {i // i ≠ i₀}, y j ^ (a j - 1)) * Real.exp (-(s * ∑ j, y j)) /
          ∏ j : {i // i ≠ i₀}, Real.Gamma (a j) := by
    rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hone (mul_pos hs (hy.1 j)),
      Finset.prod_div_distrib, Finset.prod_mul_distrib]
    refine congrArg (· / _) (congrArg₂ (· * ·) ?_ ?_)
    · rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) ↦
        Real.mul_rpow hs.le (hy.1 j).le, Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hs,
        Finset.sum_sub_distrib]
      simp
    · rw [← Real.exp_sum]
      congr 1
      simp [← Finset.mul_sum]
  have hpow : s ^ Fintype.card {i // i ≠ i₀} * s ^ (a i₀ - 1) *
      s ^ ((∑ j : {i // i ≠ i₀}, a j) - (Fintype.card {i // i ≠ i₀} : ℝ))
      = s ^ ((∑ i, a i) - 1) := by
    rw [← Real.rpow_natCast s (Fintype.card {i // i ≠ i₀}), ← Real.rpow_add hs,
      ← Real.rpow_add hs, hsplitA]
    congr 1
    ring
  have hexp : Real.exp (-(s * (1 - ∑ j, y j))) * Real.exp (-(s * ∑ j, y j)) = Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hone (mul_pos hs hu), hone hs, dirichletChartPDFReal_of_mem a hy, hprod,
    Real.mul_rpow hs.le hu.le, hsplitΓ, ← hpow, ← hexp]
  field_simp

/-! ### The Dirichlet law in the chart -/

/-- The Gamma product density read in the split coordinates. -/
private def gammaSplitPDF (a : ι → ℝ) (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ≥0∞ :=
  gammaPDF (a i₀) 1 z.1 * ∏ j : {i // i ≠ i₀}, gammaPDF (a j) 1 (z.2 j)

/-- The density of the total and the chart coordinates. -/
private def dirichletSourcePDF (a : ι → ℝ) (i₀ : ι) (z : ℝ × ({i // i ≠ i₀} → ℝ)) : ℝ≥0∞ :=
  gammaPDF (∑ i, a i) 1 z.1 * dirichletChartPDF a i₀ z.2

/-- The Gamma product density in split coordinates is measurable. -/
private theorem measurable_gammaSplitPDF (a : ι → ℝ) (i₀ : ι) :
    Measurable (gammaSplitPDF a i₀) :=
  ((measurable_gammaPDF _ _).comp measurable_fst).mul
    (Finset.measurable_prod _ fun j _ ↦
      (measurable_gammaPDF _ _).comp ((measurable_pi_apply j).comp measurable_snd))

/-- The pointwise form of the change-of-variables identity, in `ℝ≥0∞`. -/
private theorem dirichletUnchart_density {a : ι → ℝ} (ha : ∀ i, 0 < a i) (i₀ : ι)
    {z : ℝ × ({i // i ≠ i₀} → ℝ)} (hz : z ∈ dirichletUnchartSource i₀) :
    ENNReal.ofReal (z.1 ^ Fintype.card {i // i ≠ i₀}) *
        gammaSplitPDF a i₀ (dirichletUnchart i₀ z) = dirichletSourcePDF a i₀ z := by
  obtain ⟨hs, hy⟩ := hz
  have hs' : 0 < z.1 := hs
  have hA : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) ⟨i₀, Finset.mem_univ i₀⟩
  simp only [gammaSplitPDF, dirichletSourcePDF, dirichletChartPDF, gammaPDF, dirichletUnchart_fst,
    dirichletUnchart_snd_apply]
  rw [← ENNReal.ofReal_prod_of_nonneg
      fun (j : {i // i ≠ i₀}) _ ↦ gammaPDFReal_nonneg (ha j) one_pos _,
    ← ENNReal.ofReal_mul (gammaPDFReal_nonneg (ha i₀) one_pos _),
    ← ENNReal.ofReal_mul (pow_nonneg hs'.le _),
    ← ENNReal.ofReal_mul (gammaPDFReal_nonneg hA one_pos _)]
  exact congrArg ENNReal.ofReal (dirichletUnchart_density_real ha i₀ hs' hy)

/-- The Gamma product, split off at `i₀`, is Lebesgue measure weighted by the product density. -/
private theorem prod_gammaMeasure_eq_withDensity (a : ι → ℝ) (i₀ : ι) :
    (gammaMeasure (a i₀) 1).prod (Measure.pi fun j : {i // i ≠ i₀} ↦ gammaMeasure (a j) 1)
      = volume.withDensity (gammaSplitPDF a i₀) := by
  rw [gammaMeasure, pi_gammaMeasure_eq_withDensity (fun j : {i // i ≠ i₀} ↦ a j) fun _ ↦ 1,
    prod_withDensity (f := gammaPDF (a i₀) 1)
      (g := fun x : {i // i ≠ i₀} → ℝ ↦ ∏ j : {i // i ≠ i₀}, gammaPDF (a j) 1 (x j))
      (measurable_gammaPDF (a i₀) 1)
      (Finset.measurable_prod _ fun (j : {i // i ≠ i₀}) _ ↦
        (measurable_gammaPDF (a j) 1).comp (measurable_pi_apply j)),
    ← Measure.volume_eq_prod]
  rfl

/-- The source measure of the change of variables is the product of the Gamma law of the total and
the chart density. -/
private theorem withDensity_dirichletSourcePDF (a : ι → ℝ) (i₀ : ι) :
    (volume.restrict (dirichletUnchartSource i₀)).withDensity (dirichletSourcePDF a i₀)
      = (gammaMeasure (∑ i, a i) 1).prod
          ((volume : Measure ({i // i ≠ i₀} → ℝ)).withDensity (dirichletChartPDF a i₀)) := by
  have hnull : (volume : Measure (ℝ × ({i // i ≠ i₀} → ℝ))) {z | z.1 = 0} = 0 := by
    have : {z : ℝ × ({i // i ≠ i₀} → ℝ) | z.1 = 0} = ({0} : Set ℝ) ×ˢ (univ : Set _) := by
      ext z; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hne : ∀ᵐ z : ℝ × ({i // i ≠ i₀} → ℝ) ∂volume, z.1 ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  rw [← withDensity_indicator (measurableSet_dirichletUnchartSource i₀)]
  have hae : (dirichletUnchartSource i₀).indicator (dirichletSourcePDF a i₀)
      =ᵐ[volume] dirichletSourcePDF a i₀ := by
    filter_upwards [hne] with z hz
    by_cases hmem : z ∈ dirichletUnchartSource i₀
    · rw [indicator_of_mem hmem]
    · rw [indicator_of_notMem hmem, dirichletSourcePDF]
      rcases hz.lt_or_gt with h | h
      · rw [gammaPDF_of_neg h, zero_mul]
      · have hy : z.2 ∉ dirichletChartRegion i₀ := fun hy ↦ hmem ⟨h, hy⟩
        rw [dirichletChartPDF_of_notMem a hy, mul_zero]
  have hsrc : dirichletSourcePDF a i₀
      = fun z ↦ gammaPDF (∑ i, a i) 1 z.1 * dirichletChartPDF a i₀ z.2 := rfl
  rw [withDensity_congr_ae hae, hsrc, gammaMeasure,
    prod_withDensity (measurable_gammaPDF (∑ i, a i) 1) (measurable_dirichletChartPDF a i₀),
    ← Measure.volume_eq_prod]

/-- Almost every point of the Gamma product in split coordinates lies in the target region of the
scaling change of variables. -/
private theorem ae_mem_dirichletUnchartTarget (a : ι → ℝ) (i₀ : ι) :
    ∀ᵐ z ∂((gammaMeasure (a i₀) 1).prod
      (Measure.pi fun j : {i // i ≠ i₀} ↦ gammaMeasure (a j) 1)),
      z ∈ dirichletUnchartTarget i₀ := by
  rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_dirichletUnchartTarget i₀)]
  filter_upwards [ae_pos_gammaMeasure (a i₀) 1] with s hs
  filter_upwards [ae_pos_pi_gammaMeasure (fun j : {i // i ≠ i₀} ↦ a j) fun _ ↦ 1] with y hy
  exact ⟨hs, hy⟩

/-- The change-of-variables identity between the Gamma product in split coordinates and the
product of the Gamma law of the total with the chart density. -/
private theorem map_dirichletUnchart_source {a : ι → ℝ} (ha : ∀ i, 0 < a i) (i₀ : ι) :
    Measure.map (dirichletUnchart i₀)
        ((volume.restrict (dirichletUnchartSource i₀)).withDensity (dirichletSourcePDF a i₀))
      = (gammaMeasure (a i₀) 1).prod
          (Measure.pi fun j : {i // i ≠ i₀} ↦ gammaMeasure (a j) 1) := by
  rw [← Measure.restrict_eq_self_of_ae_mem (ae_mem_dirichletUnchartTarget a i₀),
    prod_gammaMeasure_eq_withDensity,
    restrict_withDensity (measurableSet_dirichletUnchartTarget i₀)]
  refine Measure.map_withDensity_eq_withDensity (measurable_dirichletUnchart i₀) (by fun_prop)
    (measurable_gammaSplitPDF a i₀) (map_dirichletUnchart_withDensity i₀) ?_
  filter_upwards [ae_restrict_mem (measurableSet_dirichletUnchartSource i₀)] with z hz
  exact dirichletUnchart_density ha i₀ hz

/-- On the strictly positive orthant, coordinate normalization is the chart applied to the chart
coordinates of the split vector. -/
private theorem dirichletNormalize_eq_dirichletChart (i₀ : ι) {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    dirichletNormalize x
      = dirichletChart i₀ (dirichletChartCoords i₀ (x i₀, fun j : {i // i ≠ i₀} ↦ x j)).2 := by
  have hT : x i₀ + ∑ j : {i // i ≠ i₀}, x j = ∑ i, x i :=
    (Fintype.sum_eq_add_sum_subtype_ne x i₀).symm
  have hTpos : 0 < ∑ i, x i := Finset.sum_pos (fun i _ ↦ hx i) ⟨i₀, Finset.mem_univ i₀⟩
  ext i
  rw [dirichletNormalize_apply]
  by_cases h : i = i₀
  · subst h
    rw [dirichletChart_apply_self]
    simp only [dirichletChartCoords_snd_apply, hT]
    rw [← Finset.sum_div]
    field_simp
    linarith
  · rw [dirichletChart_apply_of_ne i₀ _ h]
    simp only [dirichletChartCoords_snd_apply, hT]

/-- **The Dirichlet law has a density in the chart that drops the coordinate `i₀`.**  It is the
image, under the chart, of Lebesgue measure on the remaining coordinates weighted by
`TauCeti.Probability.dirichletChartPDF`.

The law lives on the simplex, which lies inside the affine hyperplane `∑ i, x i = 1` of
`EuclideanSpace ℝ ι`, so it has no density against the ambient volume; this lower-dimensional
presentation is the substitute. -/
theorem dirichletMeasure_eq_map_withDensity_dirichletChartPDF {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (i₀ : ι) :
    dirichletMeasure a
      = ((volume : Measure ({i // i ≠ i₀} → ℝ)).withDensity (dirichletChartPDF a i₀)).map
        (dirichletChart i₀) := by
  have : Nonempty ι := ⟨i₀⟩
  have hA : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) ⟨i₀, Finset.mem_univ i₀⟩
  have : IsProbabilityMeasure (gammaMeasure (∑ i, a i) 1) :=
    isProbabilityMeasure_gammaMeasure hA one_pos
  have hchart : Measurable (dirichletChart i₀ ∘ Prod.snd ∘ dirichletChartCoords i₀) :=
    measurable_dirichletChart.comp (measurable_snd.comp (measurable_dirichletChartCoords i₀))
  have hsplit : Measurable ⇑(Equiv.piSplitAt i₀ fun _ : ι ↦ ℝ) :=
    (measurePreserving_piSplitAt (fun i ↦ gammaMeasure (a i) 1) i₀).measurable
  have hM : ∀ᵐ z ∂((volume.restrict (dirichletUnchartSource i₀)).withDensity
      (dirichletSourcePDF a i₀)), z ∈ dirichletUnchartSource i₀ :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (measurableSet_dirichletUnchartSource i₀))
  calc dirichletMeasure a
      = (Measure.pi fun i ↦ gammaMeasure (a i) 1).map
          ((dirichletChart i₀ ∘ Prod.snd ∘ dirichletChartCoords i₀) ∘
            ⇑(Equiv.piSplitAt i₀ fun _ : ι ↦ ℝ)) := by
        rw [dirichletMeasure_of_pos ha]
        refine Measure.map_congr ?_
        filter_upwards [ae_pos_pi_gammaMeasure a fun _ ↦ (1 : ℝ)] with x hx
        exact dirichletNormalize_eq_dirichletChart i₀ hx
    _ = ((gammaMeasure (a i₀) 1).prod
          (Measure.pi fun j : {i // i ≠ i₀} ↦ gammaMeasure (a j) 1)).map
          (dirichletChart i₀ ∘ Prod.snd ∘ dirichletChartCoords i₀) := by
        rw [← Measure.map_map hchart hsplit,
          (measurePreserving_piSplitAt (fun i ↦ gammaMeasure (a i) 1) i₀).map_eq]
    _ = ((volume.restrict (dirichletUnchartSource i₀)).withDensity
          (dirichletSourcePDF a i₀)).map (dirichletChart i₀ ∘ Prod.snd) := by
        rw [← map_dirichletUnchart_source ha i₀,
          Measure.map_map hchart (measurable_dirichletUnchart i₀)]
        refine Measure.map_congr ?_
        filter_upwards [hM] with z hz
        simp only [Function.comp_apply, dirichletChartCoords_dirichletUnchart hz]
    _ = ((volume : Measure ({i // i ≠ i₀} → ℝ)).withDensity (dirichletChartPDF a i₀)).map
          (dirichletChart i₀) := by
        rw [← Measure.map_map measurable_dirichletChart measurable_snd,
          withDensity_dirichletSourcePDF a i₀, Measure.map_snd_prod, measure_univ, one_smul]

/-- The chart density integrates to one against Lebesgue measure on the coordinates away from
`i₀`: the chart carries the whole Dirichlet mass. -/
theorem lintegral_dirichletChartPDF_eq_one {a : ι → ℝ} (ha : ∀ i, 0 < a i) (i₀ : ι) :
    ∫⁻ x, dirichletChartPDF a i₀ x = 1 := by
  have : Nonempty ι := ⟨i₀⟩
  have : IsProbabilityMeasure (dirichletMeasure a) := isProbabilityMeasure_dirichletMeasure ha
  have h : dirichletMeasure a univ = 1 := measure_univ
  rw [dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha i₀,
    Measure.map_apply measurable_dirichletChart MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact h

end Probability

end TauCeti
