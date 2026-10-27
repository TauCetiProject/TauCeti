/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Covering.Besicovitch
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Essential interior and essential boundary

For a measure `μ` on a pseudometric space and a set `s`, the *essential interior*
`μ.essentialInterior s` is the set of points at which the complement `sᶜ` has density zero:
`μ (sᶜ ∩ closedBall x r) / μ (closedBall x r) → 0` as `r → 0⁺`. The essential interior of `sᶜ`
is the *essential exterior* of `s`, and the *essential boundary* `μ.essentialBoundary s` is the
set of points lying in neither. Equivalently, `x` is an essential boundary point when both `s`
and `sᶜ` have positive upper density at `x`.

These are the measure-theoretic replacements for the topological interior, exterior and
frontier used in the theory of sets of finite perimeter. They depend only on the `μ`-a.e. class
of `s`, the essential boundary of `s` and of `sᶜ` coincide, and both notions are compared with
their topological counterparts: `interior s ⊆ μ.essentialInterior s` and
`μ.essentialBoundary s ⊆ frontier s`. The inclusion can be strict: a null modification can
enlarge the frontier without changing the essential boundary.

## Main results

* `MeasureTheory.Measure.essentialInterior_congr`, `essentialBoundary_congr`: invariance under
  equality almost everywhere.
* `MeasureTheory.Measure.essentialBoundary_compl`: `s` and `sᶜ` have the same essential
  boundary.
* `MeasureTheory.Measure.essentialInterior_inter`, `essentialBoundary_union_subset`,
  `essentialBoundary_inter_subset`: behaviour under unions and intersections.
* `MeasureTheory.Measure.interior_subset_essentialInterior`,
  `essentialBoundary_subset_frontier`, `essentialInterior_subset_closure`: comparison with the
  topological notions.
* `MeasureTheory.NullMeasurableSet.mem_essentialInterior_iff`: for a null-measurable set and a
  locally finite measure positive on balls, the essential interior is the set of points of
  density one.
* `MeasureTheory.NullMeasurableSet.essentialInterior_ae_eq` and
  `MeasureTheory.NullMeasurableSet.measure_essentialBoundary`: by Lebesgue's density theorem, a
  null-measurable set agrees a.e. with its essential interior, and its essential boundary is
  `μ`-null.
* `MeasureTheory.Measure.essentialBoundary_closedBall`, `essentialBoundary_ball`,
  `essentialInterior_closedBall`, `essentialInterior_ball`: for an additive Haar measure on a
  finite-dimensional real normed space, the essential boundary of a ball of positive radius is
  its sphere, and its essential interior is the open ball.

## References

* H. Federer, *Geometric Measure Theory*, 4.5.11 (the measure-theoretic boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §5.8.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §16.1.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal

namespace MeasureTheory

namespace Measure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α} {s t : Set α}
  {x : α}

/-- The essential (measure-theoretic) interior of `s` with respect to `μ`: the points at which the
complement `sᶜ` has density zero, `μ (sᶜ ∩ closedBall x r) / μ (closedBall x r) → 0` as
`r → 0⁺`. The essential interior `μ.essentialInterior sᶜ` of the complement is the essential
exterior of `s`, the set of points at which `s` has density zero. -/
def essentialInterior (μ : Measure α) (s : Set α) : Set α :=
  {x | Tendsto (fun r => μ (sᶜ ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)}

/-- The essential (measure-theoretic) boundary of `s` with respect to `μ`: the points lying
neither in the essential interior nor in the essential exterior of `s`, that is, the points at
which neither `s` nor `sᶜ` has density zero. -/
def essentialBoundary (μ : Measure α) (s : Set α) : Set α :=
  (μ.essentialInterior s ∪ μ.essentialInterior sᶜ)ᶜ

/-- A point is an essential interior point of `s` when `sᶜ` has density zero there. -/
theorem mem_essentialInterior :
    x ∈ μ.essentialInterior s ↔
      Tendsto (fun r => μ (sᶜ ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- The essential boundary is the complement of the union of the essential interior and the
essential exterior. -/
theorem essentialBoundary_def :
    μ.essentialBoundary s = (μ.essentialInterior s ∪ μ.essentialInterior sᶜ)ᶜ :=
  (rfl)

/-- A point is an essential boundary point of `s` when it lies neither in the essential interior
of `s` nor in that of `sᶜ`. -/
theorem mem_essentialBoundary :
    x ∈ μ.essentialBoundary s ↔ x ∉ μ.essentialInterior s ∧ x ∉ μ.essentialInterior sᶜ := by
  rw [essentialBoundary_def, mem_compl_iff, mem_union, not_or]

/-- A set and its complement have the same essential boundary. -/
@[simp]
theorem essentialBoundary_compl : μ.essentialBoundary sᶜ = μ.essentialBoundary s := by
  rw [essentialBoundary_def, essentialBoundary_def, compl_compl, union_comm]

/-- The essential interior is monotone in the set. -/
theorem essentialInterior_mono (h : s ⊆ t) : μ.essentialInterior s ⊆ μ.essentialInterior t :=
  fun _ hx => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx
    (fun _ => zero_le) fun _ => ENNReal.div_le_div_right
      (measure_mono (inter_subset_inter_left _ (compl_subset_compl.2 h))) _

/-- Every point is an essential interior point of the whole space. -/
@[simp]
theorem essentialInterior_univ : μ.essentialInterior univ = univ :=
  eq_univ_of_forall fun _ => by simp [mem_essentialInterior]

/-- The whole space has empty essential boundary. -/
@[simp]
theorem essentialBoundary_univ : μ.essentialBoundary univ = ∅ := by
  simp [essentialBoundary_def]

/-- The empty set has empty essential boundary. -/
@[simp]
theorem essentialBoundary_empty : μ.essentialBoundary ∅ = ∅ := by
  rw [← essentialBoundary_compl, compl_empty, essentialBoundary_univ]

/-- The essential interior depends only on the `μ`-a.e. class of the set. -/
theorem essentialInterior_congr (h : s =ᵐ[μ] t) :
    μ.essentialInterior s = μ.essentialInterior t := by
  have hμ (x : α) (r : ℝ) : μ (sᶜ ∩ closedBall x r) = μ (tᶜ ∩ closedBall x r) :=
    measure_congr (h.compl.inter (ae_eq_refl _))
  ext x
  simp only [mem_essentialInterior, hμ]

/-- The essential boundary depends only on the `μ`-a.e. class of the set. -/
theorem essentialBoundary_congr (h : s =ᵐ[μ] t) :
    μ.essentialBoundary s = μ.essentialBoundary t := by
  rw [essentialBoundary_def, essentialBoundary_def, essentialInterior_congr h,
    essentialInterior_congr h.compl]

/-- A point is in the essential interior of `s ∩ t` exactly when it is in the essential
interiors of both `s` and `t`. -/
@[simp]
theorem essentialInterior_inter :
    μ.essentialInterior (s ∩ t) = μ.essentialInterior s ∩ μ.essentialInterior t := by
  refine Subset.antisymm (subset_inter (essentialInterior_mono inter_subset_left)
    (essentialInterior_mono inter_subset_right)) fun x ⟨hs, ht⟩ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hs.add ht) (fun _ => zero_le) fun r => ?_
  rw [← ENNReal.add_div, compl_inter, union_inter_distrib_right]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _

/-- The essential boundary of an intersection lies in the union of the essential boundaries. -/
theorem essentialBoundary_inter_subset :
    μ.essentialBoundary (s ∩ t) ⊆ μ.essentialBoundary s ∪ μ.essentialBoundary t := by
  intro x hx
  by_contra h
  simp only [mem_union, mem_essentialBoundary, not_or, not_and_or, not_not] at h hx
  obtain ⟨hs | hs, ht | ht⟩ := h
  · exact hx.1 (by rw [essentialInterior_inter]; exact ⟨hs, ht⟩)
  · exact hx.2 (essentialInterior_mono (compl_subset_compl.2 inter_subset_right) ht)
  · exact hx.2 (essentialInterior_mono (compl_subset_compl.2 inter_subset_left) hs)
  · exact hx.2 (essentialInterior_mono (compl_subset_compl.2 inter_subset_left) hs)

/-- The essential boundary of a union lies in the union of the essential boundaries. -/
theorem essentialBoundary_union_subset :
    μ.essentialBoundary (s ∪ t) ⊆ μ.essentialBoundary s ∪ μ.essentialBoundary t := by
  have h := essentialBoundary_inter_subset (μ := μ) (s := sᶜ) (t := tᶜ)
  rwa [← compl_union, essentialBoundary_compl, essentialBoundary_compl,
    essentialBoundary_compl] at h

/-- Every interior point of `s` is an essential interior point, for any measure. -/
theorem interior_subset_essentialInterior : interior s ⊆ μ.essentialInterior s := by
  intro x hx
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  have hsub : sᶜ ∩ closedBall x r ⊆ ∅ := fun y hy =>
    hy.1 (hεs (closedBall_subset_ball hr.2 hy.2))
  rw [measure_mono_null hsub measure_empty, ENNReal.zero_div]

/-- The essential boundary is contained in the topological frontier, for any measure. -/
theorem essentialBoundary_subset_frontier : μ.essentialBoundary s ⊆ frontier s := by
  intro x hx
  rw [mem_essentialBoundary] at hx
  refine ⟨by_contra fun h => hx.2 (interior_subset_essentialInterior ?_),
    fun h => hx.1 (interior_subset_essentialInterior h)⟩
  rwa [interior_compl, mem_compl_iff]

section Positive

variable [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- For a locally finite measure positive on nonempty open sets, small closed balls have positive
finite measure. -/
theorem eventually_measure_closedBall_pos_lt_top (x : α) :
    ∀ᶠ r in 𝓝[>] 0, 0 < μ (closedBall x r) ∧ μ (closedBall x r) < ∞ := by
  obtain ⟨u, hu, hμu⟩ := μ.finiteAt_nhds x
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  exact ⟨Metric.measure_closedBall_pos μ x hr.1,
    (measure_mono ((closedBall_subset_ball hr.2).trans hεu)).trans_lt hμu⟩

/-- The essential interior and the essential exterior of a set are disjoint. -/
theorem disjoint_essentialInterior_essentialInterior_compl :
    Disjoint (μ.essentialInterior s) (μ.essentialInterior sᶜ) := by
  refine disjoint_left.2 fun x hs hc => ?_
  rw [mem_essentialInterior, compl_compl] at hc
  have hle : ∀ᶠ r in 𝓝[>] 0, 1 ≤ μ (sᶜ ∩ closedBall x r) / μ (closedBall x r) +
      μ (s ∩ closedBall x r) / μ (closedBall x r) := by
    filter_upwards [eventually_measure_closedBall_pos_lt_top (μ := μ) x] with r ⟨hpos, hfin⟩
    rw [← ENNReal.add_div, ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hfin.ne),
      one_mul]
    calc μ (closedBall x r) = μ ((sᶜ ∩ closedBall x r) ∪ (s ∩ closedBall x r)) := by
          rw [← union_inter_distrib_right, compl_union_self, univ_inter]
      _ ≤ _ := measure_union_le _ _
  have h := ge_of_tendsto (by simpa using hs.add hc) hle
  exact absurd h (by simp)

/-- Every essential interior point of `s` lies in the closure of `s`. -/
theorem essentialInterior_subset_closure : μ.essentialInterior s ⊆ closure s := fun x hx =>
  by_contra fun h => disjoint_left.1 disjoint_essentialInterior_essentialInterior_compl hx
    (interior_subset_essentialInterior (by rwa [interior_compl, mem_compl_iff]))

/-- For a locally finite measure positive on nonempty open sets, the empty set has empty
essential interior. -/
@[simp]
theorem essentialInterior_empty : μ.essentialInterior ∅ = ∅ :=
  subset_empty_iff.1 (essentialInterior_subset_closure.trans closure_empty.subset)

end Positive

end Measure

namespace NullMeasurableSet

open Measure

section Positive

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  {x : α} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- For a null-measurable set, the essential interior is the set of density-one points. -/
theorem mem_essentialInterior_iff (hs : NullMeasurableSet s μ) :
    x ∈ μ.essentialInterior s ↔
      Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1) :=
  hs.tendsto_measure_compl_inter_div_iff ((eventually_measure_closedBall_pos_lt_top x).mono
    fun _ hr => ⟨hr.1.ne', hr.2.ne⟩)

end Positive

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [SecondCountableTopology α]
  [BorelSpace α] [HasBesicovitchCovering α] {μ : Measure α} [IsLocallyFiniteMeasure μ]
  {s : Set α}

/-- **Lebesgue's density theorem**, essential-interior form: a null-measurable set agrees almost
everywhere with its essential interior. -/
theorem essentialInterior_ae_eq (hs : NullMeasurableSet s μ) :
    μ.essentialInterior s =ᵐ[μ] s := by
  -- Replace `s` by its measurable hull `t`, which has the same essential interior.
  set t := toMeasurable μ s
  have hst : s =ᵐ[μ] t := hs.toMeasurable_ae_eq.symm
  rw [essentialInterior_congr hst]
  refine (eventuallyEqSet_iff.2 ?_).trans hst.symm
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ
    (measurableSet_toMeasurable μ s).compl] with x hx
  by_cases hxt : x ∈ t
  · rw [indicator_of_notMem (notMem_compl_iff.2 hxt)] at hx
    exact iff_of_true hx hxt
  · rw [indicator_of_mem hxt, Pi.one_apply] at hx
    exact iff_of_false (fun h => one_ne_zero (tendsto_nhds_unique hx h)) hxt

/-- The essential boundary of a null-measurable set is `μ`-null. -/
theorem measure_essentialBoundary (hs : NullMeasurableSet s μ) :
    μ (μ.essentialBoundary s) = 0 := by
  rw [essentialBoundary_def, ← ae_eq_univ]
  refine (hs.essentialInterior_ae_eq.union hs.compl.essentialInterior_ae_eq).trans ?_
  rw [union_compl_self]

end NullMeasurableSet

namespace Measure

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] {x : E} {r : ℝ}

/-- If closed balls of a quarter of the radius, centred near `y`, eventually fit in `t`, then `t`
does not have density zero at `y` for an additive Haar measure. -/
private theorem not_tendsto_measure_inter_closedBall_div_zero {t : Set E} {y : E}
    (h : ∀ᶠ ρ in 𝓝[>] 0, ∃ z, closedBall z (ρ / 4) ⊆ t ∩ closedBall y ρ) :
    ¬ Tendsto (fun ρ => μ (t ∩ closedBall y ρ) / μ (closedBall y ρ)) (𝓝[>] 0) (𝓝 0) := by
  intro hlim
  have hle : ∀ᶠ ρ in 𝓝[>] 0, ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ E) ≤
      μ (t ∩ closedBall y ρ) / μ (closedBall y ρ) := by
    filter_upwards [h, self_mem_nhdsWithin] with ρ ⟨z, hz⟩ (hρ : 0 < ρ)
    rw [ENNReal.le_div_iff_mul_le (Or.inl (Metric.measure_closedBall_pos μ y hρ).ne')
      (Or.inl measure_closedBall_lt_top.ne)]
    calc ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ E) * μ (closedBall y ρ)
        = μ (closedBall z (1 / 4 * ρ)) := by
          rw [addHaar_closedBall_mul μ z (by norm_num) hρ.le, addHaar_closedBall_center μ y]
      _ ≤ μ (t ∩ closedBall y ρ) := measure_mono (by rwa [one_div_mul_eq_div])
  have h0 := ge_of_tendsto hlim hle
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h0
  exact absurd h0 (not_le.2 (by positivity))

/-- For an additive Haar measure, the essential boundary of a closed ball of positive radius is
its sphere. -/
theorem essentialBoundary_closedBall (hr : 0 < r) :
    μ.essentialBoundary (closedBall x r) = sphere x r := by
  refine Subset.antisymm (essentialBoundary_subset_frontier.trans
    (frontier_closedBall x hr.ne').subset) fun y hy => ?_
  rw [mem_sphere] at hy
  rw [mem_essentialBoundary, mem_essentialInterior, mem_essentialInterior, compl_compl]
  constructor
  · -- Points just outside `y`, beyond the sphere, form a quarter-radius ball in the complement.
    refine not_tendsto_measure_inter_closedBall_div_zero μ ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ ⟨hρ, hρr⟩
    refine ⟨AffineMap.lineMap y x (-(ρ / (2 * r))), fun w hw => ⟨fun hwx => ?_, ?_⟩⟩
    · have h₁ := dist_lineMap_right y x (-(ρ / (2 * r)))
      have h₂ := dist_triangle_left (AffineMap.lineMap y x (-(ρ / (2 * r)))) x w
      rw [mem_closedBall] at hw hwx
      rw [hy, Real.norm_eq_abs, sub_neg_eq_add, abs_of_pos (by positivity)] at h₁
      have : (1 + ρ / (2 * r)) * r = r + ρ / 2 := by field_simp
      linarith
    · have h₁ := dist_left_lineMap y x (-(ρ / (2 * r)))
      rw [mem_closedBall] at hw ⊢
      rw [hy, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity),
        div_mul_eq_mul_div, mul_div_mul_right _ _ hr.ne'] at h₁
      linarith [dist_triangle w (AffineMap.lineMap y x (-(ρ / (2 * r)))) y, dist_comm y
        (AffineMap.lineMap y x (-(ρ / (2 * r))))]
  · -- Points just inside `y`, towards the centre, form a quarter-radius ball in the ball.
    refine not_tendsto_measure_inter_closedBall_div_zero μ ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ ⟨hρ, hρr⟩
    refine ⟨AffineMap.lineMap y x (ρ / (2 * r)), fun w hw => ⟨?_, ?_⟩⟩
    · have h₁ := dist_lineMap_right y x (ρ / (2 * r))
      rw [mem_closedBall] at hw ⊢
      have hlt : ρ / (2 * r) < 1 := by rw [div_lt_one (by positivity)]; linarith
      rw [hy, Real.norm_eq_abs, abs_of_pos (by linarith)] at h₁
      have : (1 - ρ / (2 * r)) * r = r - ρ / 2 := by field_simp
      linarith [dist_triangle w (AffineMap.lineMap y x (ρ / (2 * r))) x]
    · have h₁ := dist_left_lineMap y x (ρ / (2 * r))
      rw [mem_closedBall] at hw ⊢
      rw [hy, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_eq_mul_div, mul_div_mul_right _ _ hr.ne'] at h₁
      linarith [dist_triangle w (AffineMap.lineMap y x (ρ / (2 * r))) y, dist_comm y
        (AffineMap.lineMap y x (ρ / (2 * r)))]

/-- For an additive Haar measure, the essential interior of a closed ball of positive radius is
the open ball. -/
theorem essentialInterior_closedBall (hr : 0 < r) :
    μ.essentialInterior (closedBall x r) = ball x r := by
  refine Subset.antisymm (fun y hy => ?_) ((interior_closedBall x hr.ne').symm.subset.trans
    interior_subset_essentialInterior)
  rcases lt_trichotomy (dist y x) r with h | h | h
  · exact h
  · have hb : y ∈ μ.essentialBoundary (closedBall x r) := by
      rw [essentialBoundary_closedBall μ hr]
      exact h
    exact absurd hy ((mem_essentialBoundary.1 hb).1)
  · refine absurd (interior_subset_essentialInterior ?_)
      (disjoint_left.1 disjoint_essentialInterior_essentialInterior_compl hy)
    rw [interior_compl, closure_closedBall, mem_compl_iff, mem_closedBall, not_le]
    exact h

/-- For an additive Haar measure, the essential boundary of an open ball of positive radius is
its sphere. -/
theorem essentialBoundary_ball (hr : 0 < r) : μ.essentialBoundary (ball x r) = sphere x r := by
  rw [essentialBoundary_congr (ball_ae_eq_closedBall μ x hr.ne'),
    essentialBoundary_closedBall μ hr]

/-- For an additive Haar measure, the essential interior of an open ball of positive radius is
the ball itself. -/
theorem essentialInterior_ball (hr : 0 < r) : μ.essentialInterior (ball x r) = ball x r := by
  rw [essentialInterior_congr (ball_ae_eq_closedBall μ x hr.ne'),
    essentialInterior_closedBall μ hr]

end Haar

end Measure

end MeasureTheory
