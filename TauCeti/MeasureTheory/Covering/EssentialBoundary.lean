/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.Besicovitch
public import TauCeti.MeasureTheory.Measure.OpenPos
public import TauCeti.MeasureTheory.OuterMeasure.Basic

/-!
# Densities, essential interior and essential boundary

Let `μ` be a measure on a metric space. A set `s` has **density** `d` at `x`
(`TauCeti.HasDensityAt μ s x d`) when the proportion `μ (s ∩ closedBall x r) / μ (closedBall x r)`
of `s` in closed balls around `x` tends to `d` as `r → 0⁺`. The points of density one form the
**essential interior** `TauCeti.essentialInterior μ s`, those of density zero the
**essential exterior** `TauCeti.essentialExterior μ s`, and the points of neither kind the
**essential boundary** `TauCeti.essentialBoundary μ s`. For Lebesgue measure these are the sets
`E⁽¹⁾`, `E⁽⁰⁾` and `∂ᵉE` of the theory of sets of finite perimeter.

All three sets depend only on the `μ`-a.e. class of `s`, unlike the topological interior and
frontier. They are nevertheless comparable to them: for a locally finite measure that charges
every open set, `interior s ⊆ essentialInterior μ s ⊆ closure s` and
`essentialBoundary μ s ⊆ frontier s`. For such a measure and a null-measurable set `s`,
complements exchange the essential interior and exterior, so the essential boundary of `sᶜ` is
that of `s`. The essential boundary of a union of any two sets lies in the union of their
essential boundaries; the same holds for an intersection of two sets one of which is
null-measurable, for any measure.

For a locally finite measure on a second-countable metric space with its Borel σ-algebra and the
Besicovitch covering property, such as a finite-dimensional real normed space, Lebesgue's density
theorem shows that the essential interior of a null-measurable set `s` agrees with `s` almost
everywhere and the essential boundary is null. The essential interior is
thus a canonical representative of the a.e. class of `s`.

## Main declarations

* `TauCeti.HasDensityAt μ s x d`: the set `s` has density `d` at `x` with respect to `μ`.
* `TauCeti.essentialInterior`, `TauCeti.essentialExterior`, `TauCeti.essentialBoundary`.
* `TauCeti.essentialInterior_congr_ae` and its companions: invariance under null modification.
* `TauCeti.essentialInterior_compl` and `TauCeti.essentialBoundary_compl`: complements.
* `TauCeti.essentialBoundary_union_subset` and `TauCeti.essentialBoundary_inter_subset`.
* `TauCeti.interior_subset_essentialInterior`, `TauCeti.essentialInterior_subset_closure` and
  `TauCeti.essentialBoundary_subset_frontier`: comparison with the topological notions.
* `TauCeti.essentialInterior_ae_eq` and `TauCeti.measure_essentialBoundary`: Lebesgue's density
  theorem.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §5.4 and §16.1.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §1.7 and
  §5.8.
-/

public section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

section PseudoMetricSpace

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α} {s t : Set α}
  {x : α} {d d' : ℝ≥0∞}

/-- The set `s` has **density** `d` at `x` with respect to `μ`: the proportion
`μ (s ∩ closedBall x r) / μ (closedBall x r)` of `s` in the closed ball of radius `r` around `x`
tends to `d` as `r → 0⁺`. -/
def HasDensityAt (μ : Measure α) (s : Set α) (x : α) (d : ℝ≥0∞) : Prop :=
  Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 d)

theorem hasDensityAt_iff : HasDensityAt μ s x d ↔
    Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 d) :=
  Iff.rfl

namespace HasDensityAt

/-- A density is unique. -/
theorem unique (h : HasDensityAt μ s x d) (h' : HasDensityAt μ s x d') : d = d' :=
  tendsto_nhds_unique h h'

/-- A density is at most one. -/
theorem le_one (h : HasDensityAt μ s x d) : d ≤ 1 :=
  le_of_tendsto' h fun r => measure_inter_div_le_one s (closedBall x r)

/-- Densities only depend on the set up to `μ`-null sets. -/
theorem congr_ae (h : HasDensityAt μ s x d) (hst : s =ᵐ[μ] t) : HasDensityAt μ t x d := by
  have hm (r : ℝ) : μ (s ∩ closedBall x r) = μ (t ∩ closedBall x r) :=
    measure_congr (hst.inter EventuallyEq.rfl)
  simpa only [HasDensityAt, hm] using h

/-- A positive density forces closed balls of small positive radius around the point to have
positive finite measure: otherwise the proportions vanish. -/
theorem eventually_measure_closedBall_ne_zero_ne_top (h : HasDensityAt μ s x d) (hd : d ≠ 0) :
    ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≠ 0 ∧ μ (closedBall x r) ≠ ∞ := by
  filter_upwards [h.eventually_ne hd] with r hr
  refine ⟨fun h0 => hr ?_, fun htop => hr ?_⟩
  · rw [measure_mono_null inter_subset_right h0, ENNReal.zero_div]
  · rw [htop, ENNReal.div_top]

/-- **Complements.** If a null-measurable set `s` has density `d` at `x`, then `sᶜ` has density
`1 - d` there, provided closed balls of small positive radius around `x` have positive finite
measure. This holds at every point for a locally finite measure that charges every open set
(`Metric.eventually_measure_closedBall_ne_zero_ne_top`). -/
theorem compl (hs : NullMeasurableSet s μ)
    (hx : ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≠ 0 ∧ μ (closedBall x r) ≠ ∞)
    (h : HasDensityAt μ s x d) : HasDensityAt μ sᶜ x (1 - d) :=
  hs.tendsto_measure_compl_inter_div hx h

end HasDensityAt

/-- Densities only depend on the set up to `μ`-null sets. -/
theorem hasDensityAt_congr_ae (hst : s =ᵐ[μ] t) : HasDensityAt μ s x d ↔ HasDensityAt μ t x d :=
  ⟨fun h => h.congr_ae hst, fun h => h.congr_ae hst.symm⟩

/-! ### Essential interior, exterior and boundary -/

/-- The **essential interior** of `s` with respect to `μ`: the points at which `s` has density
one. For Lebesgue measure this is the set `E⁽¹⁾` of points of density one of `E`. -/
def essentialInterior (μ : Measure α) (s : Set α) : Set α :=
  {x | HasDensityAt μ s x 1}

/-- The **essential exterior** of `s` with respect to `μ`: the points at which `s` has density
zero. For Lebesgue measure this is the set `E⁽⁰⁾` of points of density zero of `E`. -/
def essentialExterior (μ : Measure α) (s : Set α) : Set α :=
  {x | HasDensityAt μ s x 0}

/-- The **essential boundary** of `s` with respect to `μ`: the points at which `s` has neither
density one nor density zero. This is the measure-theoretic boundary `∂ᵉE`, which ignores
modifications of `E` by null sets. -/
def essentialBoundary (μ : Measure α) (s : Set α) : Set α :=
  (essentialInterior μ s ∪ essentialExterior μ s)ᶜ

@[simp]
theorem mem_essentialInterior : x ∈ essentialInterior μ s ↔ HasDensityAt μ s x 1 :=
  Iff.rfl

@[simp]
theorem mem_essentialExterior : x ∈ essentialExterior μ s ↔ HasDensityAt μ s x 0 :=
  Iff.rfl

@[simp]
theorem mem_essentialBoundary :
    x ∈ essentialBoundary μ s ↔ x ∉ essentialInterior μ s ∧ x ∉ essentialExterior μ s := by
  simp [essentialBoundary]

theorem essentialBoundary_def :
    essentialBoundary μ s = (essentialInterior μ s ∪ essentialExterior μ s)ᶜ :=
  (rfl)

/-- The essential interior and the essential exterior are disjoint. -/
theorem disjoint_essentialInterior_essentialExterior :
    Disjoint (essentialInterior μ s) (essentialExterior μ s) :=
  disjoint_left.2 fun _ h₁ h₀ =>
    one_ne_zero ((mem_essentialInterior.1 h₁).unique (mem_essentialExterior.1 h₀))

/-- The essential interior is invariant under modification of the set by null sets. -/
theorem essentialInterior_congr_ae (h : s =ᵐ[μ] t) :
    essentialInterior μ s = essentialInterior μ t :=
  ext fun _ => hasDensityAt_congr_ae h

/-- The essential exterior is invariant under modification of the set by null sets. -/
theorem essentialExterior_congr_ae (h : s =ᵐ[μ] t) :
    essentialExterior μ s = essentialExterior μ t :=
  ext fun _ => hasDensityAt_congr_ae h

/-- The essential boundary is invariant under modification of the set by null sets. -/
theorem essentialBoundary_congr_ae (h : s =ᵐ[μ] t) :
    essentialBoundary μ s = essentialBoundary μ t := by
  rw [essentialBoundary_def, essentialBoundary_def, essentialInterior_congr_ae h,
    essentialExterior_congr_ae h]

/-! ### Monotonicity, unions and intersections -/

/-- The essential interior is monotone, up to null sets. -/
theorem essentialInterior_mono_ae (h : s ≤ᵐ[μ] t) :
    essentialInterior μ s ⊆ essentialInterior μ t := fun x hx => by
  rw [mem_essentialInterior, hasDensityAt_iff] at hx ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds
    (fun _ => ENNReal.div_le_div_right (measure_mono_ae (h.inter EventuallyLE.rfl)) _)
    fun r => measure_inter_div_le_one t (closedBall x r)

/-- The essential interior is monotone. -/
theorem essentialInterior_mono (h : s ⊆ t) : essentialInterior μ s ⊆ essentialInterior μ t :=
  essentialInterior_mono_ae h.eventuallyLE

/-- The essential exterior is antitone, up to null sets. -/
theorem essentialExterior_anti_ae (h : s ≤ᵐ[μ] t) :
    essentialExterior μ t ⊆ essentialExterior μ s := fun _ hx => by
  rw [mem_essentialExterior, hasDensityAt_iff] at hx ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx (fun _ => zero_le)
    fun _ => ENNReal.div_le_div_right (measure_mono_ae (h.inter EventuallyLE.rfl)) _

/-- The essential exterior is antitone. -/
theorem essentialExterior_anti (h : s ⊆ t) : essentialExterior μ t ⊆ essentialExterior μ s :=
  essentialExterior_anti_ae h.eventuallyLE

/-- A point is in the essential exterior of a union exactly when it is in the essential exterior
of both sets. -/
@[simp]
theorem essentialExterior_union :
    essentialExterior μ (s ∪ t) = essentialExterior μ s ∩ essentialExterior μ t := by
  refine Subset.antisymm (subset_inter (essentialExterior_anti subset_union_left)
    (essentialExterior_anti subset_union_right)) fun x ⟨hs, ht⟩ => ?_
  rw [mem_essentialExterior, hasDensityAt_iff] at hs ht ⊢
  have hsum : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r) +
      μ (t ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hs.add ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun r => ?_
  rw [← ENNReal.add_div, union_inter_distrib_right]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _

/-- The essential boundary of a union lies in the union of the essential boundaries. -/
theorem essentialBoundary_union_subset :
    essentialBoundary μ (s ∪ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  intro x hx
  by_contra hst
  simp only [mem_union, mem_essentialBoundary, not_or, not_and_or, not_not] at hx hst
  obtain ⟨hs | hs, ht | ht⟩ := hst
  · exact hx.1 (essentialInterior_mono subset_union_left hs)
  · exact hx.1 (essentialInterior_mono subset_union_left hs)
  · exact hx.1 (essentialInterior_mono subset_union_right ht)
  · exact hx.2 (essentialExterior_union (μ := μ) ▸ ⟨hs, ht⟩)

/-- A point is in the essential interior of an intersection with a null-measurable set exactly
when it is in the essential interior of both sets. -/
@[simp]
theorem essentialInterior_inter (hs : NullMeasurableSet s μ) :
    essentialInterior μ (s ∩ t) = essentialInterior μ s ∩ essentialInterior μ t := by
  refine Subset.antisymm (subset_inter (essentialInterior_mono inter_subset_left)
    (essentialInterior_mono inter_subset_right)) fun x ⟨hxs, hxt⟩ => ?_
  have hc : HasDensityAt μ sᶜ x 0 := by
    simpa using (mem_essentialInterior.1 hxs).compl hs
      ((mem_essentialInterior.1 hxs).eventually_measure_closedBall_ne_zero_ne_top one_ne_zero)
  rw [mem_essentialInterior, hasDensityAt_iff] at hxt ⊢
  -- `t ∩ B ⊆ (s ∩ t ∩ B) ∪ (sᶜ ∩ B)` bounds the proportion of `s ∩ t` below by that of `t`
  -- minus that of `sᶜ`, which tends to `1 - 0`.
  have hlow := ENNReal.Tendsto.sub hxt hc (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun r => ?_)
    fun r => measure_inter_div_le_one _ _
  rw [tsub_le_iff_right, ← ENNReal.add_div]
  have hsub : t ∩ closedBall x r ⊆ s ∩ t ∩ closedBall x r ∪ sᶜ ∩ closedBall x r :=
    fun y ⟨hyt, hyB⟩ => (em (y ∈ s)).imp (fun hys => ⟨⟨hys, hyt⟩, hyB⟩) fun hys => ⟨hys, hyB⟩
  exact ENNReal.div_le_div_right ((measure_mono hsub).trans (measure_union_le _ _)) _

/-- The essential boundary of an intersection with a null-measurable set lies in the union of the
essential boundaries. -/
theorem essentialBoundary_inter_subset (hs : NullMeasurableSet s μ) :
    essentialBoundary μ (s ∩ t) ⊆ essentialBoundary μ s ∪ essentialBoundary μ t := by
  intro x hx
  by_contra hst
  simp only [mem_union, mem_essentialBoundary, not_or, not_and_or, not_not] at hx hst
  obtain ⟨hs' | hs', ht' | ht'⟩ := hst
  · exact hx.1 (essentialInterior_inter hs ▸ ⟨hs', ht'⟩)
  · exact hx.2 (essentialExterior_anti inter_subset_right ht')
  · exact hx.2 (essentialExterior_anti inter_subset_left hs')
  · exact hx.2 (essentialExterior_anti inter_subset_left hs')

section Compl

variable [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- The essential interior of the complement of a null-measurable set is its essential
exterior. -/
@[simp]
theorem essentialInterior_compl (hs : NullMeasurableSet s μ) :
    essentialInterior μ sᶜ = essentialExterior μ s := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa using (mem_essentialInterior.1 hx).compl hs.compl
      (eventually_measure_closedBall_ne_zero_ne_top μ x)
  · simpa using (mem_essentialExterior.1 hx).compl hs
      (eventually_measure_closedBall_ne_zero_ne_top μ x)

/-- The essential exterior of the complement of a null-measurable set is its essential
interior. -/
@[simp]
theorem essentialExterior_compl (hs : NullMeasurableSet s μ) :
    essentialExterior μ sᶜ = essentialInterior μ s := by
  rw [← essentialInterior_compl hs.compl, compl_compl]

/-- A null-measurable set and its complement have the same essential boundary. -/
@[simp]
theorem essentialBoundary_compl (hs : NullMeasurableSet s μ) :
    essentialBoundary μ sᶜ = essentialBoundary μ s := by
  rw [essentialBoundary_def, essentialBoundary_def, essentialInterior_compl hs,
    essentialExterior_compl hs, union_comm]

end Compl

/-! ### Comparison with the topological interior and frontier -/

/-- A point outside the closure of `s` is in its essential exterior. -/
theorem compl_closure_subset_essentialExterior : (closure s)ᶜ ⊆ essentialExterior μ s := by
  intro x hx
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hx
  rw [mem_essentialExterior, hasDensityAt_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  rw [(disjoint_left.2 fun y hys hy => hεs (closedBall_subset_ball hr.2 hy)
    (subset_closure hys)).inter_eq, measure_empty, ENNReal.zero_div]

/-- The essential interior of `s` lies in its closure. -/
theorem essentialInterior_subset_closure : essentialInterior μ s ⊆ closure s := fun _ hx =>
  not_not.1 fun hcl => disjoint_left.1 disjoint_essentialInterior_essentialExterior hx
    (compl_closure_subset_essentialExterior hcl)

section OpenPos

variable [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- An interior point of `s` is in its essential interior, for a locally finite measure that
charges every open set. -/
theorem interior_subset_essentialInterior : interior s ⊆ essentialInterior μ s := by
  intro x hx
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  rw [mem_essentialInterior, hasDensityAt_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε, eventually_measure_closedBall_ne_zero_ne_top μ x]
    with r hr hμ
  rw [inter_eq_right.2 ((closedBall_subset_ball hr.2).trans (hεs.trans interior_subset)),
    ENNReal.div_self hμ.1 hμ.2]

/-- The essential exterior of `s` lies in the complement of its interior. -/
theorem essentialExterior_subset_compl_interior : essentialExterior μ s ⊆ (interior s)ᶜ :=
  fun _ hx hint => disjoint_left.1 disjoint_essentialInterior_essentialExterior
    (interior_subset_essentialInterior hint) hx

/-- **The essential boundary lies in the topological frontier**, for a locally finite measure
that charges every open set. -/
theorem essentialBoundary_subset_frontier : essentialBoundary μ s ⊆ frontier s := by
  intro x hx
  rw [mem_essentialBoundary] at hx
  exact ⟨not_not.1 fun hcl => hx.2 (compl_closure_subset_essentialExterior hcl),
    fun hint => hx.1 (interior_subset_essentialInterior hint)⟩

end OpenPos

end PseudoMetricSpace

/-! ### Lebesgue's density theorem -/

section Lebesgue

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [SecondCountableTopology α]
  [BorelSpace α] [HasBesicovitchCovering α] {μ : Measure α} [IsLocallyFiniteMeasure μ]
  {s : Set α}

/-- **Lebesgue's density theorem.** At almost every point a null-measurable set has density one
or zero, according to whether the point lies in the set. -/
theorem ae_hasDensityAt_indicator (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, HasDensityAt μ s x (s.indicator 1 x) :=
  hs.ae_tendsto_measure_inter_div

/-- **Lebesgue's density theorem.** A null-measurable set agrees almost everywhere with its
essential interior. -/
theorem essentialInterior_ae_eq (hs : NullMeasurableSet s μ) : essentialInterior μ s =ᵐ[μ] s :=
  hs.ae_eq_setOf_tendsto_measure_inter_div.symm

/-- **Lebesgue's density theorem.** The essential exterior of a null-measurable set agrees almost
everywhere with its complement. -/
theorem essentialExterior_ae_eq (hs : NullMeasurableSet s μ) :
    essentialExterior μ s =ᵐ[μ] sᶜ := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_hasDensityAt_indicator hs] with x hx
  rw [mem_essentialExterior, mem_compl_iff]
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs, Pi.one_apply] at hx
    exact iff_of_false (fun h => one_ne_zero (hx.unique h)) (not_not.2 hxs)
  · simp only [indicator_of_notMem hxs] at hx
    exact iff_of_true hx hxs

/-- **Lebesgue's density theorem.** The essential boundary of a null-measurable set is null. -/
theorem measure_essentialBoundary (hs : NullMeasurableSet s μ) :
    μ (essentialBoundary μ s) = 0 := by
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [ae_hasDensityAt_indicator hs] with x hx
  rw [mem_essentialBoundary, not_and_or, not_not, not_not, mem_essentialInterior,
    mem_essentialExterior]
  by_cases hxs : x ∈ s
  · exact Or.inl (by simpa [indicator_of_mem hxs] using hx)
  · exact Or.inr (by simpa [indicator_of_notMem hxs] using hx)

/-- The essential interior is idempotent: it is a canonical representative of the a.e. class of
a null-measurable set. -/
@[simp]
theorem essentialInterior_essentialInterior (hs : NullMeasurableSet s μ) :
    essentialInterior μ (essentialInterior μ s) = essentialInterior μ s :=
  essentialInterior_congr_ae (essentialInterior_ae_eq hs)

end Lebesgue

end TauCeti
