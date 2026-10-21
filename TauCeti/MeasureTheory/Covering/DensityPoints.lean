/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Points of density and the essential boundary

For a measure `μ` on a pseudometric space, a point `x` is a *point of density `c`* of a set `s`
when the proportion `μ (s ∩ closedBall x r) / μ (closedBall x r)` of `s` in small closed balls
around `x` tends to `c` as `r → 0⁺`. The points of density one form the *essential interior* of
`s`, the points of density zero its *essential exterior*, and the points of neither kind its
*essential boundary*

`∂ᵉ s = (s⁽¹⁾ ∪ s⁽⁰⁾)ᶜ`.

These are the measure-theoretic replacements for the interior, exterior and frontier of `s`:
they only see `s` up to `μ`-null sets (`TauCeti.essentialBoundary_congr_ae`), so they are
attached to the a.e. class of a set rather than to a representative. In the theory of sets of
finite perimeter, the essential boundary is the measure-theoretic boundary on which the
perimeter is compared with codimension-one Hausdorff measure (Federer's theorem, not proved
here).

For a null-measurable set, along sets of positive finite measure the proportion of the
complement is one minus the proportion of the set
(`MeasureTheory.NullMeasurableSet.tendsto_measure_compl_inter_div_iff`), so density one of `s`
is density zero of `sᶜ`. This lets density arguments estimate the complement, where measures
add, and return to density-one points.

For a locally finite measure positive on open sets, the essential boundary is contained in the
topological frontier (`TauCeti.essentialBoundary_subset_frontier`), a null-measurable set and
its complement have the same essential boundary, and the essential boundary of an intersection
or a difference of null-measurable sets lies in the union of the essential boundaries. For an
arbitrary measure the same holds for a union of arbitrary sets. The inclusion in the frontier is
strict in general: null modifications change the frontier but not the essential boundary.

For a locally finite measure on a space with the Besicovitch covering property (for instance a
finite-dimensional real normed space), Lebesgue's density theorem says that a null-measurable
set agrees almost everywhere with its essential interior, its complement with its essential
exterior, and hence its essential boundary is null
(`MeasureTheory.NullMeasurableSet.measure_essentialBoundary`).

As a basic example, an endpoint of a nondegenerate interval in `ℝ` is a point of density `1/2`,
and the essential boundary of `[a, b]` is `{a, b}` (`TauCeti.essentialBoundary_Icc`).

We use closed balls, as Mathlib's density theorems do. For an additive Haar measure on a
finite-dimensional space, spheres are null, so open balls give the same notions.

## Main definitions

* `TauCeti.densityPoints μ s c`: the points of density `c` of `s`.
* `TauCeti.essentialInterior μ s`, `TauCeti.essentialExterior μ s`: the points of density one
  and zero.
* `TauCeti.essentialBoundary μ s`: the points of density neither one nor zero.

## Main results

* `MeasureTheory.NullMeasurableSet.tendsto_measure_compl_inter_div_iff`: density one of a
  null-measurable set along a family of sets is density zero of its complement.
* `TauCeti.essentialBoundary_congr_ae`: invariance under null modification.
* `TauCeti.essentialBoundary_subset_frontier`: the essential boundary lies in the frontier.
* `TauCeti.essentialBoundary_compl`: a null-measurable set and its complement have the same
  essential boundary.
* `TauCeti.essentialBoundary_union_subset`, `TauCeti.essentialBoundary_inter_subset`,
  `TauCeti.essentialBoundary_diff_subset`: essential boundaries of Boolean combinations (of
  null-measurable sets, for intersections and differences).
* `MeasureTheory.NullMeasurableSet.essentialInterior_ae_eq`: Lebesgue's density theorem in set
  form for a locally finite measure, and
  `MeasureTheory.NullMeasurableSet.measure_essentialBoundary`: the essential boundary is null.
* `TauCeti.essentialBoundary_Icc`: the essential boundary of a closed interval.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapters 5 and 16.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal

namespace MeasureTheory.NullMeasurableSet

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- For a null-measurable set `s`, along sets of positive finite measure the proportion of `sᶜ`
tends to zero exactly when the proportion of `s` tends to one. -/
theorem tendsto_measure_compl_inter_div_iff (hs : NullMeasurableSet s μ) {l : Filter ι}
    {u : ι → Set α} (hu : ∀ᶠ i in l, μ (u i) ≠ 0 ∧ μ (u i) ≠ ∞) :
    Tendsto (fun i => μ (sᶜ ∩ u i) / μ (u i)) l (𝓝 0) ↔
      Tendsto (fun i => μ (s ∩ u i) / μ (u i)) l (𝓝 1) := by
  have hle : ∀ i, μ (s ∩ u i) / μ (u i) ≤ 1 := fun i =>
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
  have hcompl : ∀ᶠ i in l, μ (sᶜ ∩ u i) / μ (u i) = 1 - μ (s ∩ u i) / μ (u i) := by
    filter_upwards [hu] with i ⟨h0, htop⟩
    have hadd : μ (s ∩ u i) + μ (sᶜ ∩ u i) = μ (u i) := by
      rw [inter_comm s, inter_comm sᶜ, ← Set.sdiff_eq, measure_inter_add_sdiff₀ _ hs]
    rw [← ENNReal.div_self h0 htop, ← ENNReal.sub_div (fun _ _ => h0), ← hadd,
      ENNReal.add_sub_cancel_left (measure_ne_top_of_subset inter_subset_right htop)]
  constructor
  · intro h
    have h' := ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at h'
    refine h'.congr' ?_
    filter_upwards [hcompl] with i hi
    rw [hi, ENNReal.sub_sub_cancel ENNReal.one_ne_top (hle i)]
  · intro h
    have h' := ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
    rw [tsub_self] at h'
    exact h'.congr' (hcompl.mono fun i hi => hi.symm)

end MeasureTheory.NullMeasurableSet

namespace TauCeti

section PseudoMetric

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α} {s t : Set α}
  {x : α} {c d : ℝ≥0∞}

/-- The points of density `c` of a set `s` with respect to the measure `μ`: the points `x` at
which the proportion `μ (s ∩ closedBall x r) / μ (closedBall x r)` tends to `c` as `r → 0⁺`. -/
def densityPoints (μ : Measure α) (s : Set α) (c : ℝ≥0∞) : Set α :=
  {x | Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 c)}

@[simp]
theorem mem_densityPoints : x ∈ densityPoints μ s c ↔
    Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 c) :=
  Iff.rfl

/-- The essential interior of `s` with respect to `μ`: the points of density one of `s`. -/
def essentialInterior (μ : Measure α) (s : Set α) : Set α :=
  densityPoints μ s 1

/-- The essential exterior of `s` with respect to `μ`: the points of density zero of `s`. -/
def essentialExterior (μ : Measure α) (s : Set α) : Set α :=
  densityPoints μ s 0

/-- The essential boundary of `s` with respect to `μ`: the points at which `s` has density
neither one nor zero, that is the complement of the union of the essential interior and the
essential exterior. -/
def essentialBoundary (μ : Measure α) (s : Set α) : Set α :=
  (essentialInterior μ s ∪ essentialExterior μ s)ᶜ

theorem essentialInterior_def : essentialInterior μ s = densityPoints μ s 1 :=
  (rfl)

theorem essentialExterior_def : essentialExterior μ s = densityPoints μ s 0 :=
  (rfl)

theorem essentialBoundary_def :
    essentialBoundary μ s = (essentialInterior μ s ∪ essentialExterior μ s)ᶜ :=
  (rfl)

@[simp]
theorem mem_essentialInterior : x ∈ essentialInterior μ s ↔
    Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1) :=
  Iff.rfl

@[simp]
theorem mem_essentialExterior : x ∈ essentialExterior μ s ↔
    Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

@[simp]
theorem mem_essentialBoundary : x ∈ essentialBoundary μ s ↔
    x ∉ essentialInterior μ s ∧ x ∉ essentialExterior μ s := by
  rw [essentialBoundary_def, mem_compl_iff, mem_union, not_or]

/-! ### Basic properties -/

/-- A point has at most one density. -/
theorem disjoint_densityPoints (h : c ≠ d) : Disjoint (densityPoints μ s c) (densityPoints μ s d) :=
  Set.disjoint_left.2 fun _ hc hd => h (tendsto_nhds_unique hc hd)

theorem disjoint_essentialInterior_essentialExterior :
    Disjoint (essentialInterior μ s) (essentialExterior μ s) :=
  disjoint_densityPoints one_ne_zero

/-- A point of density strictly between zero and one lies in the essential boundary. -/
theorem densityPoints_subset_essentialBoundary (h₀ : c ≠ 0) (h₁ : c ≠ 1) :
    densityPoints μ s c ⊆ essentialBoundary μ s := fun _ hx =>
  mem_essentialBoundary.2 ⟨fun h => Set.disjoint_left.1 (disjoint_densityPoints h₁) hx h,
    fun h => Set.disjoint_left.1 (disjoint_densityPoints h₀) hx h⟩

/-- **Locality.** Points of density only depend on the `μ`-a.e. class of the set. -/
theorem densityPoints_congr_ae (h : s =ᵐ[μ] t) : densityPoints μ s c = densityPoints μ t c := by
  ext x
  have hμ : ∀ r, μ (s ∩ closedBall x r) = μ (t ∩ closedBall x r) := fun r =>
    measure_congr (h.inter (EventuallyEq.refl _ _))
  simp only [mem_densityPoints, hμ]

theorem essentialInterior_congr_ae (h : s =ᵐ[μ] t) :
    essentialInterior μ s = essentialInterior μ t :=
  densityPoints_congr_ae h

theorem essentialExterior_congr_ae (h : s =ᵐ[μ] t) :
    essentialExterior μ s = essentialExterior μ t :=
  densityPoints_congr_ae h

/-- **Locality.** The essential boundary only depends on the `μ`-a.e. class of the set. -/
theorem essentialBoundary_congr_ae (h : s =ᵐ[μ] t) :
    essentialBoundary μ s = essentialBoundary μ t := by
  rw [essentialBoundary_def, essentialBoundary_def, essentialInterior_congr_ae h,
    essentialExterior_congr_ae h]

/-- The essential interior is monotone, up to null sets. -/
theorem essentialInterior_mono (h : s ≤ᵐ[μ] t) : essentialInterior μ s ⊆ essentialInterior μ t :=
  fun _ hx => tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds
    (fun _ => ENNReal.div_le_div_right (measure_mono_ae (h.inter (ae_eq_refl _).le)) _)
    fun _ => ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

/-- The essential exterior is antitone, up to null sets. -/
theorem essentialExterior_anti (h : s ≤ᵐ[μ] t) : essentialExterior μ t ⊆ essentialExterior μ s :=
  fun _ hx => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx (fun _ => zero_le)
    fun _ => ENNReal.div_le_div_right (measure_mono_ae (h.inter (ae_eq_refl _).le)) _

/-- A point is of density zero for a union exactly when it is of density zero for both sets. -/
theorem essentialExterior_union :
    essentialExterior μ (s ∪ t) = essentialExterior μ s ∩ essentialExterior μ t := by
  refine Subset.antisymm (fun x hx => ⟨essentialExterior_anti subset_union_left.eventuallyLE hx,
    essentialExterior_anti subset_union_right.eventuallyLE hx⟩) fun x ⟨hs, ht⟩ => ?_
  have hsum := hs.add ht
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun r => ?_
  rw [← ENNReal.add_div, union_inter_distrib_right]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _

@[simp]
theorem essentialExterior_empty : essentialExterior μ (∅ : Set α) = univ :=
  eq_univ_of_forall fun _ => by simp [mem_essentialExterior]

@[simp]
theorem essentialInterior_empty : essentialInterior μ (∅ : Set α) = ∅ :=
  eq_empty_of_forall_notMem fun _ hx =>
    Set.disjoint_left.1 disjoint_essentialInterior_essentialExterior hx (by simp)

@[simp]
theorem essentialBoundary_empty : essentialBoundary μ (∅ : Set α) = ∅ := by
  simp [essentialBoundary_def]

/-- **The essential boundary of a union** lies in the union of the essential boundaries. -/
theorem essentialBoundary_union_subset :
    essentialBoundary μ (s ∪ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  intro x hx
  by_contra h
  simp only [mem_union, mem_essentialBoundary, not_or, not_and_or, not_not] at h hx
  obtain ⟨hs | hs, ht | ht⟩ := h
  · exact hx.1 (essentialInterior_mono subset_union_left.eventuallyLE hs)
  · exact hx.1 (essentialInterior_mono subset_union_left.eventuallyLE hs)
  · exact hx.1 (essentialInterior_mono subset_union_right.eventuallyLE ht)
  · exact hx.2 (by rw [essentialExterior_union]; exact ⟨hs, ht⟩)

/-! ### Comparison with the topological interior, exterior and frontier -/

/-- Points of the topological exterior are points of density zero. -/
theorem interior_compl_subset_essentialExterior : interior sᶜ ⊆ essentialExterior μ s := by
  intro x hx
  obtain ⟨ε, hε, hεs⟩ := nhds_basis_closedBall.mem_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  rw [(disjoint_compl_right.mono_right
    ((closedBall_subset_closedBall hr.2.le).trans hεs)).inter_eq, measure_empty, ENNReal.zero_div]

variable [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- Points of the topological interior are points of density one, for a locally finite measure
positive on open sets. -/
theorem interior_subset_essentialInterior : interior s ⊆ essentialInterior μ s := by
  intro x hx
  obtain ⟨ε, hε, hεs⟩ := nhds_basis_closedBall.mem_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε, eventually_measure_closedBall_ne_zero_ne_top μ x]
    with r hr ⟨h₀, h₁⟩
  rw [inter_eq_right.2 ((closedBall_subset_closedBall hr.2.le).trans hεs),
    ENNReal.div_self h₀ h₁]

/-- **The essential boundary lies in the topological frontier**, for a locally finite measure
positive on open sets. -/
theorem essentialBoundary_subset_frontier : essentialBoundary μ s ⊆ frontier s := by
  intro x hx
  rw [mem_essentialBoundary] at hx
  rw [frontier, Set.mem_sdiff]
  refine ⟨by_contra fun h => hx.2 ?_, fun h => hx.1 (interior_subset_essentialInterior h)⟩
  exact interior_compl_subset_essentialExterior (interior_compl (s := s) ▸ h)

@[simp]
theorem essentialInterior_univ : essentialInterior μ (univ : Set α) = univ :=
  eq_univ_of_forall fun _ => interior_subset_essentialInterior (by simp)

@[simp]
theorem essentialExterior_univ : essentialExterior μ (univ : Set α) = ∅ :=
  eq_empty_of_forall_notMem fun _ hx =>
    Set.disjoint_left.1 disjoint_essentialInterior_essentialExterior (by simp) hx

@[simp]
theorem essentialBoundary_univ : essentialBoundary μ (univ : Set α) = ∅ :=
  eq_empty_of_subset_empty (frontier_univ (X := α) ▸ essentialBoundary_subset_frontier)

/-! ### Complements and Boolean combinations -/

/-- The points of density zero of the complement of a null-measurable set are its points of
density one. -/
theorem essentialExterior_compl (hs : NullMeasurableSet s μ) :
    essentialExterior μ sᶜ = essentialInterior μ s := by
  ext x
  exact hs.tendsto_measure_compl_inter_div_iff (eventually_measure_closedBall_ne_zero_ne_top μ x)

/-- The points of density one of the complement of a null-measurable set are its points of
density zero. -/
theorem essentialInterior_compl (hs : NullMeasurableSet s μ) :
    essentialInterior μ sᶜ = essentialExterior μ s := by
  rw [← essentialExterior_compl hs.compl, compl_compl]

/-- **Complements have the same essential boundary.** -/
theorem essentialBoundary_compl (hs : NullMeasurableSet s μ) :
    essentialBoundary μ sᶜ = essentialBoundary μ s := by
  rw [essentialBoundary_def, essentialBoundary_def, essentialInterior_compl hs,
    essentialExterior_compl hs, union_comm]

/-- A point is of density one for an intersection of null-measurable sets exactly when it is of
density one for both sets. -/
theorem essentialInterior_inter (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    essentialInterior μ (s ∩ t) = essentialInterior μ s ∩ essentialInterior μ t := by
  rw [← essentialExterior_compl (hs.inter ht), compl_inter, essentialExterior_union,
    essentialExterior_compl hs, essentialExterior_compl ht]

/-- **The essential boundary of an intersection** of null-measurable sets lies in the union of
the essential boundaries. -/
theorem essentialBoundary_inter_subset (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    essentialBoundary μ (s ∩ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  rw [← essentialBoundary_compl (hs.inter ht), compl_inter, ← essentialBoundary_compl hs,
    ← essentialBoundary_compl ht]
  exact essentialBoundary_union_subset

/-- **The essential boundary of a difference** of null-measurable sets lies in the union of the
essential boundaries. -/
theorem essentialBoundary_diff_subset (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    essentialBoundary μ (s \ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  rw [sdiff_eq, ← essentialBoundary_compl ht]
  exact essentialBoundary_inter_subset hs ht.compl

end PseudoMetric

/-! ### Intervals -/

section Interval

variable {a b : ℝ}

/-- The left endpoint of a nondegenerate closed interval is a point of density `1/2`. -/
theorem left_mem_densityPoints_Icc (h : a < b) : a ∈ densityPoints volume (Icc a b) 2⁻¹ := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 h)] with r hr
  rw [Real.closedBall_eq_Icc, Icc_inter_Icc, max_eq_left (by linarith [hr.1]),
    min_eq_right (by linarith [hr.2]), Real.volume_Icc, Real.volume_Icc, add_sub_cancel_left,
    show a + r - (a - r) = 2 * r by ring, ← ENNReal.ofReal_div_of_pos (by linarith [hr.1]),
    div_mul_cancel_right₀ hr.1.ne', ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- The right endpoint of a nondegenerate closed interval is a point of density `1/2`. -/
theorem right_mem_densityPoints_Icc (h : a < b) : b ∈ densityPoints volume (Icc a b) 2⁻¹ := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 h)] with r hr
  rw [Real.closedBall_eq_Icc, Icc_inter_Icc, max_eq_right (by linarith [hr.2]),
    min_eq_left (by linarith [hr.1]), Real.volume_Icc, Real.volume_Icc, sub_sub_cancel,
    show b + r - (b - r) = 2 * r by ring, ← ENNReal.ofReal_div_of_pos (by linarith [hr.1]),
    div_mul_cancel_right₀ hr.1.ne', ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- The essential boundary of a nondegenerate closed interval consists of its endpoints. -/
theorem essentialBoundary_Icc (h : a < b) : essentialBoundary volume (Icc a b) = {a, b} := by
  have h₀ : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  have h₁ : (2⁻¹ : ℝ≥0∞) ≠ 1 := by norm_num
  refine Subset.antisymm (frontier_Icc h.le ▸ essentialBoundary_subset_frontier)
    (insert_subset ?_ (singleton_subset_iff.2 ?_))
  · exact densityPoints_subset_essentialBoundary h₀ h₁ (left_mem_densityPoints_Icc h)
  · exact densityPoints_subset_essentialBoundary h₀ h₁ (right_mem_densityPoints_Icc h)

end Interval

end TauCeti

/-! ### Lebesgue's density theorem -/

namespace MeasureTheory.NullMeasurableSet

open TauCeti

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [SecondCountableTopology α]
  [BorelSpace α] [HasBesicovitchCovering α] {μ : Measure α} [IsLocallyFiniteMeasure μ]
  {s : Set α}

/-- **Lebesgue's density theorem.** Almost every point of a null-measurable set `s` is a point
of density one of `s`, and almost every point outside `s` is a point of density zero. -/
theorem ae_mem_densityPoints_indicator (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ densityPoints μ s (s.indicator 1 x) := by
  have hmeas : ∀ x r, μ (s ∩ closedBall x r) = μ (toMeasurable μ s ∩ closedBall x r) :=
    fun x r => measure_congr (hs.toMeasurable_ae_eq.symm.inter (ae_eq_refl _))
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ
    (measurableSet_toMeasurable μ s), eventuallyEqSet_iff.1 hs.toMeasurable_ae_eq] with x hx hxs
  have hind : s.indicator (1 : α → ℝ≥0∞) x = (toMeasurable μ s).indicator 1 x := by
    by_cases h : x ∈ s <;> simp [h, hxs]
  rw [mem_densityPoints, hind]
  simpa only [hmeas] using hx

/-- **Lebesgue's density theorem**, set form: a null-measurable set agrees almost everywhere
with its essential interior. -/
theorem essentialInterior_ae_eq (hs : NullMeasurableSet s μ) : essentialInterior μ s =ᵐ[μ] s := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hs.ae_mem_densityPoints_indicator] with x hx
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, Pi.one_apply] at hx
    exact iff_of_true hx hxs
  · rw [indicator_of_notMem hxs] at hx
    exact iff_of_false (fun h => Set.disjoint_left.1
      disjoint_essentialInterior_essentialExterior h hx) hxs

/-- **Lebesgue's density theorem** for the complement: the complement of a null-measurable set
agrees almost everywhere with its essential exterior. -/
theorem essentialExterior_ae_eq (hs : NullMeasurableSet s μ) :
    essentialExterior μ s =ᵐ[μ] sᶜ := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hs.ae_mem_densityPoints_indicator] with x hx
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, Pi.one_apply] at hx
    exact iff_of_false (fun h => Set.disjoint_left.1
      disjoint_essentialInterior_essentialExterior hx h) (not_not_intro hxs)
  · rw [indicator_of_notMem hxs] at hx
    exact iff_of_true hx hxs

/-- The essential boundary of a null-measurable set is null. -/
theorem measure_essentialBoundary (hs : NullMeasurableSet s μ) :
    μ (essentialBoundary μ s) = 0 := by
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [hs.ae_mem_densityPoints_indicator] with x hx
  rw [mem_essentialBoundary, not_and_or, not_not, not_not]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, Pi.one_apply] at hx
    exact Or.inl hx
  · rw [indicator_of_notMem hxs] at hx
    exact Or.inr hx

end MeasureTheory.NullMeasurableSet
