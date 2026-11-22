/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.Besicovitch
public import TauCeti.MeasureTheory.Measure.OpenPos
public import TauCeti.MeasureTheory.OuterMeasure.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Topology.Order.IntermediateValue

/-!
# Densities, essential interior and essential boundary

Let `μ` be a measure on a metric space. A set `s` has **density** `d` at `x`
(`TauCeti.HasDensityAt μ s x d`) when the proportion `μ (s ∩ closedBall x r) / μ (closedBall x r)`
of `s` in closed balls around `x` tends to `d` as `r → 0⁺`. The points of density one form the
**essential interior** `TauCeti.essentialInterior μ s`, those of density zero the
**essential exterior** `TauCeti.essentialExterior μ s`, and the points of neither kind the
**essential boundary** `TauCeti.essentialBoundary μ s`. For Lebesgue measure these are the sets
`E⁽¹⁾`, `E⁽⁰⁾` and `∂ᵉE` of the theory of sets of finite perimeter.

Unlike the topological interior and frontier, all three sets depend only on the `μ`-a.e. class of
`s`; moreover, locally on an open set `U` they depend only on `s ∩ U`. They are nevertheless
comparable to them: for a locally finite measure that charges every open set,
`interior s ⊆ essentialInterior μ s ⊆ closure s`, while `essentialBoundary μ s ⊆ frontier s`
holds for any measure. For a locally finite measure that charges every open set and a
null-measurable set `s`, complements exchange the essential interior and exterior, and `univ` has
essential interior `univ` and empty essential exterior; for any measure, a null-measurable set and
its complement have the same essential boundary, so `∅`, `univ` and subsets of subsingleton spaces
have empty essential boundary. The essential boundary of a union of any two sets lies in the union
of their essential boundaries; the same holds for an intersection of two sets one of which is
null-measurable, for any measure.

For a locally finite measure on a second-countable metric space with its Borel σ-algebra and the
Besicovitch covering property, such as a finite-dimensional real normed space, Lebesgue's density
theorem shows that the essential interior of a null-measurable set `s` agrees with `s` almost
everywhere and the essential boundary is null. The essential interior is
thus a canonical representative of the a.e. class of `s`.

Whenever `μ` has measurable closed balls and positive, finite, continuous closed-ball mass on some
interval `(0, ε)` around `x`, if the smaller of `μ (s ∩ closedBall x r)` and
`μ (closedBall x r \ s)` has proportion tending to zero as `r → 0⁺`, continuity of the closed-ball
proportion on `(0, ε)` forces `s` to have density zero or density one at `x`, so `x` lies outside
the essential boundary without any measurability assumption on `s`. In particular, this applies to
any additive Haar measure on a finite-dimensional real normed space of dimension `n`, where
conversely a set filling a proportion `r ^ n ≤ c μ(s ∩ ball x r)` of every small ball around `x`
does not have density zero at `x`, and at any point of the essential boundary both `s` and its
complement fill a fixed positive proportion of arbitrarily small closed balls.

## Main declarations

* `TauCeti.HasDensityAt μ s x d`: the set `s` has density `d` at `x` with respect to `μ`.
* `TauCeti.essentialInterior`, `TauCeti.essentialExterior`, `TauCeti.essentialBoundary`.
* `TauCeti.essentialInterior_congr_ae`, `TauCeti.inter_essentialBoundary_inter_of_isOpen` and
  companions: invariance under null modification and open localization.
* `TauCeti.essentialInterior_compl` and `TauCeti.essentialBoundary_compl`: complements.
* `TauCeti.essentialBoundary_union_subset` and `TauCeti.essentialBoundary_inter_subset`.
* `TauCeti.essentialInterior_preimage_add_right` and its companions: for a translation-invariant
  measure, the three sets commute with translations.
* `TauCeti.interior_subset_essentialInterior`, `TauCeti.essentialInterior_subset_closure` and
  `TauCeti.essentialBoundary_subset_frontier`: comparison with the topological notions.
* `TauCeti.hasDensityAt_zero_or_one_of_tendsto_min_div_of_continuousOn` and
  `TauCeti.notMem_essentialBoundary_of_tendsto_min_div_of_continuousOn`: vanishing of the smaller
  closed-ball proportion forces density zero or one when closed-ball mass is positive, finite, and
  continuous on `(0, ε)`.
* `TauCeti.essentialInterior_ae_eq` and `TauCeti.measure_essentialBoundary`: Lebesgue's density
  theorem.
* `TauCeti.not_hasDensityAt_zero_of_eventually_ofReal_pow_le_mul_measure_inter_ball`: a lower
  volume density bound against a Haar measure rules out density zero.
* `TauCeti.hasDensityAt_zero_or_one_of_tendsto_min_div` and
  `TauCeti.notMem_essentialBoundary_of_tendsto_min_div`: Haar-measure specialization of the
  zero-one density dichotomy.
* `TauCeti.exists_pos_frequently_ofReal_mul_measure_closedBall_le`: at a point of the essential
  boundary, `s` and its complement both fill a proportion at least `a > 0` of arbitrarily small
  closed balls.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §5.4 and §16.1.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §1.7 and
  §5.8.
-/

public section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section PseudoMetricSpace

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α} {s t : Set α}
  {x : α} {d d' : ℝ≥0∞}

/-- The set `s` has **density** `d` at `x` with respect to `μ`: the proportion
`μ (s ∩ closedBall x r) / μ (closedBall x r)` of `s` in the closed ball of radius `r` around `x`
tends to `d` as `r → 0⁺`. The quotient is taken in `ℝ≥0∞`, so where the small closed balls around
`x` are null or of infinite measure (for instance at every point outside the support of `μ`) it is
the junk value `0`, and every set, `univ` included, has density `0` at `x`. -/
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
    measure_congr (hst.inter Filter.EventuallyEqSet.rfl)
  simpa only [HasDensityAt, hm] using h

/-- Densities only depend on the set in a neighborhood of the point. -/
theorem congr_nhds (h : HasDensityAt μ s x d) (hst : s =ᶠ[𝓝 x] t) : HasDensityAt μ t x d := by
  obtain ⟨ε, hε, hεst⟩ := Metric.mem_nhds_iff.1 (eventuallyEqSet_iff.1 hst)
  refine hasDensityAt_iff.2 ((hasDensityAt_iff.1 h).congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  congr 2
  exact ext fun y => and_congr_left fun hy => hεst (closedBall_subset_ball hr.2 hy)

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

/-- The empty set has density zero everywhere. -/
theorem hasDensityAt_empty : HasDensityAt μ ∅ x 0 := by
  simp [HasDensityAt]

/-- The empty set has density `d` at `x` if and only if `d = 0`. -/
@[simp]
theorem hasDensityAt_empty_iff : HasDensityAt μ ∅ x d ↔ d = 0 :=
  ⟨fun h => h.unique hasDensityAt_empty, fun h => h ▸ hasDensityAt_empty⟩

/-- The whole space has density one at `x`, provided closed balls of small positive radius around
`x` have positive finite measure. -/
theorem hasDensityAt_univ
    (hx : ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≠ 0 ∧ μ (closedBall x r) ≠ ∞) :
    HasDensityAt μ univ x 1 := by
  refine hasDensityAt_iff.2 (tendsto_const_nhds.congr' (hx.mono fun r hr => ?_))
  simp only [univ_inter, ENNReal.div_self hr.1 hr.2]

/-- For a locally finite measure that charges every open set, the whole space has density `d` at
`x` if and only if `d = 1`. -/
@[simp]
theorem hasDensityAt_univ_iff [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] :
    HasDensityAt μ univ x d ↔ d = 1 :=
  ⟨fun h => h.unique (hasDensityAt_univ (eventually_measure_closedBall_ne_zero_ne_top μ x)),
    fun h => h ▸ hasDensityAt_univ (eventually_measure_closedBall_ne_zero_ne_top μ x)⟩

/-- For a null-measurable set `s`, if closed balls of small positive radius around `x` have
positive finite measure, then `sᶜ` has density zero at `x` exactly when `s` has density one. -/
theorem hasDensityAt_compl_zero_iff (hs : NullMeasurableSet s μ)
    (hx : ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≠ 0 ∧ μ (closedBall x r) ≠ ∞) :
    HasDensityAt μ sᶜ x 0 ↔ HasDensityAt μ s x 1 :=
  hs.tendsto_measure_compl_inter_div_iff hx

/-- For a null-measurable set `s`, if closed balls of small positive radius around `x` have
positive finite measure, then `sᶜ` has density one at `x` exactly when `s` has density zero. -/
theorem hasDensityAt_compl_one_iff (hs : NullMeasurableSet s μ)
    (hx : ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≠ 0 ∧ μ (closedBall x r) ≠ ∞) :
    HasDensityAt μ sᶜ x 1 ↔ HasDensityAt μ s x 0 := by
  simpa only [compl_compl] using (hasDensityAt_compl_zero_iff hs.compl hx).symm

/-- Densities only depend on the set up to `μ`-null sets. -/
theorem hasDensityAt_congr_ae (hst : s =ᵐ[μ] t) : HasDensityAt μ s x d ↔ HasDensityAt μ t x d :=
  ⟨fun h => h.congr_ae hst, fun h => h.congr_ae hst.symm⟩

/-- Densities only depend on the set in a neighborhood of the point. -/
theorem hasDensityAt_congr_nhds (hst : s =ᶠ[𝓝 x] t) :
    HasDensityAt μ s x d ↔ HasDensityAt μ t x d :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

/-- Intersecting a set with a neighborhood of `x` does not change its density at `x`. -/
theorem hasDensityAt_inter_of_mem_nhds {U : Set α} (hU : U ∈ 𝓝 x) :
    HasDensityAt μ (s ∩ U) x d ↔ HasDensityAt μ s x d :=
  hasDensityAt_congr_nhds
    (eventuallyEqSet_iff.2 (eventually_of_mem hU fun _ hy => and_iff_left hy))

/-- Densities at `x` only depend on the set up to a `μ.restrict U`-null subset of a neighborhood
`U` of `x`. -/
theorem hasDensityAt_congr_ae_of_mem_nhds {U : Set α} (hU : U ∈ 𝓝 x) (h : s =ᵐ[μ.restrict U] t) :
    HasDensityAt μ s x d ↔ HasDensityAt μ t x d := by
  have hUae : (s ∩ U : Set α) =ᵐ[μ] (t ∩ U) :=
    eventuallyEqSet_iff.2 ((ae_imp_of_ae_restrict (eventuallyEqSet_iff.1 h)).mono
      fun _ hy => and_congr_left hy)
  rw [← hasDensityAt_inter_of_mem_nhds hU, hasDensityAt_congr_ae hUae,
    hasDensityAt_inter_of_mem_nhds hU]

/-- Small closed balls around a point either all have positive finite measure, or every set has
density zero at the point: the measures of the closed balls increase with the radius, so either
some small ball is null, or every ball is infinite, or the small balls have positive finite
measure. -/
theorem eventually_measure_closedBall_ne_zero_ne_top_or_forall_hasDensityAt_zero (μ : Measure α)
    (x : α) : (∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≠ 0 ∧ μ (closedBall x r) ≠ ∞) ∨
      ∀ s : Set α, HasDensityAt μ s x 0 := by
  by_cases hnull : ∃ r > 0, μ (closedBall x r) = 0
  · obtain ⟨r₀, hr₀, h₀⟩ := hnull
    refine Or.inr fun s => hasDensityAt_iff.2 <| tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    rw [measure_mono_null inter_subset_right
      (measure_mono_null (closedBall_subset_closedBall hr.2.le) h₀), ENNReal.zero_div]
  by_cases htop : ∀ r > 0, μ (closedBall x r) = ∞
  · refine Or.inr fun s => hasDensityAt_iff.2 <| tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [htop r hr, ENNReal.div_top]
  push Not at hnull htop
  obtain ⟨r₁, hr₁, h₁⟩ := htop
  refine Or.inl ?_
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
  exact ⟨hnull r hr.1, ne_top_of_le_ne_top h₁ (measure_mono (closedBall_subset_closedBall hr.2.le))⟩

/-! ### Essential interior, exterior and boundary -/

/-- The **essential interior** of `s` with respect to `μ`: the points at which `s` has density
one. For Lebesgue measure this is the set `E⁽¹⁾` of points of density one of `E`. -/
def essentialInterior (μ : Measure α) (s : Set α) : Set α :=
  {x | HasDensityAt μ s x 1}

/-- The **essential exterior** of `s` with respect to `μ`: the points at which `s` has density
zero. For Lebesgue measure this is the set `E⁽⁰⁾` of points of density zero of `E`. Where small
closed balls are null or of infinite measure every set has density zero (see `HasDensityAt`), so
`essentialExterior μ s` contains the complement of the support of `μ`. -/
def essentialExterior (μ : Measure α) (s : Set α) : Set α :=
  {x | HasDensityAt μ s x 0}

/-- The **essential boundary** of `s` with respect to `μ`: the points at which `s` has neither
density one nor density zero. This is the measure-theoretic boundary `∂ᵉE`, which ignores
modifications of `E` by null sets. Since the complement of the support of `μ` lies in
`essentialExterior μ s` (see `HasDensityAt`), the essential boundary lies inside the support. -/
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

/-- A point at which `s` has density distinct from `0` and `1` lies in the essential boundary. -/
theorem HasDensityAt.mem_essentialBoundary (h : HasDensityAt μ s x d) (hd0 : d ≠ 0) (hd1 : d ≠ 1) :
    x ∈ essentialBoundary μ s :=
  TauCeti.mem_essentialBoundary.2 ⟨fun h1 => hd1 (h.unique (mem_essentialInterior.1 h1)),
    fun h0 => hd0 (h.unique (mem_essentialExterior.1 h0))⟩

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

/-- The essential exterior of the empty set is the whole space. -/
@[simp]
theorem essentialExterior_empty : essentialExterior μ ∅ = univ :=
  eq_univ_of_forall fun _ => hasDensityAt_empty

/-- The essential interior of the empty set is empty. -/
@[simp]
theorem essentialInterior_empty : essentialInterior μ ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hx =>
    one_ne_zero ((mem_essentialInterior.1 hx).unique hasDensityAt_empty)

/-- The essential boundary of the empty set is empty. -/
@[simp]
theorem essentialBoundary_empty : essentialBoundary μ ∅ = ∅ := by
  simp [essentialBoundary_def]

/-- Inside an open set `U`, the essential interior of `s ∩ U` agrees with that of `s`. -/
theorem inter_essentialInterior_inter_of_isOpen {U : Set α} (hU : IsOpen U) :
    U ∩ essentialInterior μ (s ∩ U) = U ∩ essentialInterior μ s :=
  ext fun _ => and_congr_right fun hx => hasDensityAt_inter_of_mem_nhds (hU.mem_nhds hx)

/-- Inside an open set `U`, the essential exterior of `s ∩ U` agrees with that of `s`. -/
theorem inter_essentialExterior_inter_of_isOpen {U : Set α} (hU : IsOpen U) :
    U ∩ essentialExterior μ (s ∩ U) = U ∩ essentialExterior μ s :=
  ext fun _ => and_congr_right fun hx => hasDensityAt_inter_of_mem_nhds (hU.mem_nhds hx)

/-- Inside an open set `U`, the essential boundary of `s ∩ U` agrees with that of `s`. -/
theorem inter_essentialBoundary_inter_of_isOpen {U : Set α} (hU : IsOpen U) :
    U ∩ essentialBoundary μ (s ∩ U) = U ∩ essentialBoundary μ s := by
  ext x
  simp only [mem_inter_iff, mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior]
  exact and_congr_right fun hx => by
    rw [hasDensityAt_inter_of_mem_nhds (hU.mem_nhds hx),
      hasDensityAt_inter_of_mem_nhds (hU.mem_nhds hx)]

/-- Modifying a set on a `μ.restrict U`-null subset of an open set `U` does not change its
essential interior inside `U`. -/
theorem inter_essentialInterior_congr_ae {U : Set α} (hU : IsOpen U) (h : s =ᵐ[μ.restrict U] t) :
    U ∩ essentialInterior μ s = U ∩ essentialInterior μ t :=
  ext fun _ => and_congr_right fun hx => hasDensityAt_congr_ae_of_mem_nhds (hU.mem_nhds hx) h

/-- Modifying a set on a `μ.restrict U`-null subset of an open set `U` does not change its
essential exterior inside `U`. -/
theorem inter_essentialExterior_congr_ae {U : Set α} (hU : IsOpen U) (h : s =ᵐ[μ.restrict U] t) :
    U ∩ essentialExterior μ s = U ∩ essentialExterior μ t :=
  ext fun _ => and_congr_right fun hx => hasDensityAt_congr_ae_of_mem_nhds (hU.mem_nhds hx) h

/-- Modifying a set on a `μ.restrict U`-null subset of an open set `U` does not change its
essential boundary inside `U`. -/
theorem inter_essentialBoundary_congr_ae {U : Set α} (hU : IsOpen U) (h : s =ᵐ[μ.restrict U] t) :
    U ∩ essentialBoundary μ s = U ∩ essentialBoundary μ t := by
  ext x
  simp only [mem_inter_iff, mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior]
  exact and_congr_right fun hx => by
    rw [hasDensityAt_congr_ae_of_mem_nhds (hU.mem_nhds hx) h,
      hasDensityAt_congr_ae_of_mem_nhds (hU.mem_nhds hx) h]

/-! ### Monotonicity, unions and intersections -/

/-- The essential interior is monotone, up to null sets. -/
theorem essentialInterior_mono_ae (h : s ≤ᵐ[μ] t) :
    essentialInterior μ s ⊆ essentialInterior μ t := fun x hx => by
  rw [mem_essentialInterior, hasDensityAt_iff] at hx ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds
    (fun _ => ENNReal.div_le_div_right (measure_mono_ae (h.inter Filter.EventuallySubset.rfl)) _)
    fun r => measure_inter_div_le_one t (closedBall x r)

/-- The essential interior is monotone. -/
theorem essentialInterior_mono (h : s ⊆ t) : essentialInterior μ s ⊆ essentialInterior μ t :=
  essentialInterior_mono_ae h.eventuallySubset

/-- The essential exterior is antitone, up to null sets. -/
theorem essentialExterior_anti_ae (h : s ≤ᵐ[μ] t) :
    essentialExterior μ t ⊆ essentialExterior μ s := fun _ hx => by
  rw [mem_essentialExterior, hasDensityAt_iff] at hx ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx (fun _ => zero_le)
    fun _ => ENNReal.div_le_div_right (measure_mono_ae (h.inter Filter.EventuallySubset.rfl)) _

/-- The essential exterior is antitone. -/
theorem essentialExterior_anti (h : s ⊆ t) : essentialExterior μ t ⊆ essentialExterior μ s :=
  essentialExterior_anti_ae h.eventuallySubset

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
  rw [mem_essentialInterior, mem_essentialExterior]
  exact hasDensityAt_compl_one_iff hs (eventually_measure_closedBall_ne_zero_ne_top μ x)

/-- The essential exterior of the complement of a null-measurable set is its essential
interior. -/
@[simp]
theorem essentialExterior_compl (hs : NullMeasurableSet s μ) :
    essentialExterior μ sᶜ = essentialInterior μ s := by
  rw [← essentialInterior_compl hs.compl, compl_compl]

/-- The essential interior of the whole space is the whole space. -/
@[simp]
theorem essentialInterior_univ : essentialInterior μ univ = univ :=
  eq_univ_of_forall fun x => hasDensityAt_univ (eventually_measure_closedBall_ne_zero_ne_top μ x)

/-- The essential exterior of the whole space is empty. -/
@[simp]
theorem essentialExterior_univ : essentialExterior μ univ = ∅ :=
  eq_empty_of_forall_notMem fun x hx =>
    one_ne_zero ((hasDensityAt_univ (eventually_measure_closedBall_ne_zero_ne_top μ x)).unique
      (mem_essentialExterior.1 hx))

omit [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] in
/-- A null-measurable set and its complement have the same essential boundary. -/
@[simp]
theorem essentialBoundary_compl (hs : NullMeasurableSet s μ) :
    essentialBoundary μ sᶜ = essentialBoundary μ s := by
  ext x
  simp only [mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior]
  rcases eventually_measure_closedBall_ne_zero_ne_top_or_forall_hasDensityAt_zero μ x with hx | hx
  · rw [hasDensityAt_compl_one_iff hs hx, hasDensityAt_compl_zero_iff hs hx]
    tauto
  · simp [hx s, hx sᶜ]

omit [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] in
/-- The essential boundary of the whole space is empty. -/
@[simp]
theorem essentialBoundary_univ : essentialBoundary μ univ = ∅ := by
  rw [← compl_empty, essentialBoundary_compl MeasurableSet.empty.nullMeasurableSet,
    essentialBoundary_empty]

omit [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] in
/-- In a subsingleton space, every essential boundary is empty. -/
@[simp]
theorem essentialBoundary_eq_empty_of_subsingleton [Subsingleton α] :
    essentialBoundary μ s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · exact essentialBoundary_empty
  · have hs : s = univ := eq_univ_of_forall fun z => Subsingleton.elim y z ▸ hy
    rw [hs, essentialBoundary_univ]

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

/-- An interior point of `s` is in its essential interior, provided closed balls of small positive
radius around it have positive finite measure. -/
theorem mem_essentialInterior_of_mem_interior
    (hμ : ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≠ 0 ∧ μ (closedBall x r) ≠ ∞)
    (hx : x ∈ interior s) : x ∈ essentialInterior μ s := by
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  rw [mem_essentialInterior, hasDensityAt_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε, hμ] with r hr hr'
  rw [inter_eq_right.2 ((closedBall_subset_ball hr.2).trans (hεs.trans interior_subset)),
    ENNReal.div_self hr'.1 hr'.2]

section OpenPos

variable [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- An interior point of `s` is in its essential interior, for a locally finite measure that
charges every open set. -/
theorem interior_subset_essentialInterior : interior s ⊆ essentialInterior μ s := fun x hx =>
  mem_essentialInterior_of_mem_interior (eventually_measure_closedBall_ne_zero_ne_top μ x) hx

/-- The essential exterior of `s` lies in the complement of its interior. -/
theorem essentialExterior_subset_compl_interior : essentialExterior μ s ⊆ (interior s)ᶜ :=
  fun _ hx hint => disjoint_left.1 disjoint_essentialInterior_essentialExterior
    (interior_subset_essentialInterior hint) hx

end OpenPos

/-- **The essential boundary lies in the topological frontier.** -/
theorem essentialBoundary_subset_frontier : essentialBoundary μ s ⊆ frontier s := by
  intro x hx
  rw [mem_essentialBoundary] at hx
  refine ⟨not_not.1 fun hcl => hx.2 (compl_closure_subset_essentialExterior hcl),
    fun hint => ?_⟩
  rcases eventually_measure_closedBall_ne_zero_ne_top_or_forall_hasDensityAt_zero μ x with hμ | hμ
  · exact hx.1 (mem_essentialInterior_of_mem_interior hμ hint)
  · exact hx.2 (hμ s)

section ContinuousClosedBall

variable [OpensMeasurableSpace α]

/-- **Zero-one density dichotomy.** On a metric space with measurable closed balls, if `μ` has
positive, finite, continuous closed-ball mass `r ↦ μ (closedBall x r)` on `(0, ε)` (`ε > 0`), and
`min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r) → 0` as `r → 0⁺`, then
`s` has either density zero or density one at `x`. No measurability of `s` is needed. -/
theorem hasDensityAt_zero_or_one_of_tendsto_min_div_of_continuousOn {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ r ∈ Set.Ioo 0 ε, μ (closedBall x r) ≠ 0)
    (hfin : ∀ r ∈ Set.Ioo 0 ε, μ (closedBall x r) ≠ ∞)
    (hcont : ContinuousOn (fun r => μ (closedBall x r)) (Set.Ioo 0 ε))
    (h : Tendsto (fun r =>
      min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) :
    HasDensityAt μ s x 0 ∨ HasDensityAt μ s x 1 := by
  set b : ℝ → ℝ := fun r => μ.real (closedBall x r)
  set f : ℝ → ℝ := fun r => μ.real (s ∩ closedBall x r) / b r
  set g : ℝ → ℝ := fun r => μ.real (closedBall x r \ s) / b r
  have hb_pos {r : ℝ} (hr : r ∈ Set.Ioo 0 ε) : 0 < b r :=
    ENNReal.toReal_pos (hpos r hr) (hfin r hr)
  have hb_cont : ContinuousOn b (Set.Ioo 0 ε) :=
    ENNReal.continuousOn_toReal.comp hcont fun r hr => hfin r hr
  have hf_cont : ContinuousOn f (Set.Ioo 0 ε) :=
    (μ.continuousOn_real_inter_closedBall x s hfin hb_cont).div hb_cont
      fun r hr => (hb_pos hr).ne'
  have hsum {r : ℝ} (hr : r ∈ Set.Ioo 0 ε) : 1 ≤ f r + g r ∧ f r ≤ 1 := by
    have hb0 := hb_pos hr
    have hle : b r ≤ μ.real (s ∩ closedBall x r) + μ.real (closedBall x r \ s) := by
      simpa only [b, inter_comm s, inter_union_sdiff] using
        measureReal_union_le (s ∩ closedBall x r) (closedBall x r \ s)
    refine ⟨?_, div_le_one_of_le₀
      (measureReal_mono inter_subset_right (hfin r hr)) hb0.le⟩
    rw [← add_div, one_le_div hb0]
    exact hle
  have hf_toReal (r : ℝ) : (μ (s ∩ closedBall x r) / μ (closedBall x r)).toReal = f r := by
    rw [ENNReal.toReal_div, ← measureReal_def, ← measureReal_def]
  have hg_toReal (r : ℝ) : (μ (closedBall x r \ s) / μ (closedBall x r)).toReal = g r := by
    rw [ENNReal.toReal_div, ← measureReal_def, ← measureReal_def]
  have hmin : Tendsto (fun r => min (f r) (g r)) (𝓝[>] 0) (𝓝 0) := by
    refine ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).congr'
      (eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr => ?_)
    have hfin₁ : μ (s ∩ closedBall x r) ≠ ∞ :=
      measure_ne_top_of_subset inter_subset_right (hfin r hr)
    have hfin₂ : μ (closedBall x r \ s) ≠ ∞ :=
      measure_ne_top_of_subset sdiff_subset (hfin r hr)
    have hdiv : min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r) =
        min (μ (s ∩ closedBall x r) / μ (closedBall x r))
          (μ (closedBall x r \ s) / μ (closedBall x r)) :=
      Monotone.map_min (fun _ _ h => ENNReal.div_le_div_right h _)
    rw [Function.comp_apply, hdiv, ENNReal.toReal_min (ENNReal.div_ne_top hfin₁ (hpos r hr))
      (ENNReal.div_ne_top hfin₂ (hpos r hr)), hf_toReal, hg_toReal]
  have hconv {c : ℝ} (hc : Tendsto f (𝓝[>] 0) (𝓝 c)) :
      HasDensityAt μ s x (ENNReal.ofReal c) := by
    refine hasDensityAt_iff.2 ((ENNReal.tendsto_ofReal hc).congr'
      (eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr => ?_))
    have hfin₁ : μ (s ∩ closedBall x r) ≠ ∞ :=
      measure_ne_top_of_subset inter_subset_right (hfin r hr)
    rw [← hf_toReal r, ENNReal.ofReal_toReal (ENNReal.div_ne_top hfin₁ (hpos r hr))]
  have hdich := hf_cont.tendsto_zero_or_tendsto_of_tendsto_min hε
    (eventually_of_mem (Ioo_mem_nhdsGT hε) fun _ hr => (hsum hr).1)
    (eventually_of_mem (Ioo_mem_nhdsGT hε) fun _ hr => (hsum hr).2) hmin
  exact hdich.imp (fun h0 => by simpa using hconv h0) (fun h1 => by simpa using hconv h1)

/-- If `μ` has measurable closed balls and positive, finite, continuous closed-ball mass on
`(0, ε)` (`ε > 0`) around `x`, and
`min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r) → 0` as `r → 0⁺`, then
`x` does not belong to the essential boundary of `s`. No measurability of `s` is needed. -/
theorem notMem_essentialBoundary_of_tendsto_min_div_of_continuousOn {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ r ∈ Set.Ioo 0 ε, μ (closedBall x r) ≠ 0)
    (hfin : ∀ r ∈ Set.Ioo 0 ε, μ (closedBall x r) ≠ ∞)
    (hcont : ContinuousOn (fun r => μ (closedBall x r)) (Set.Ioo 0 ε))
    (h : Tendsto (fun r =>
      min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) :
    x ∉ essentialBoundary μ s := by
  rw [mem_essentialBoundary, not_and_or, not_not, not_not]
  exact (hasDensityAt_zero_or_one_of_tendsto_min_div_of_continuousOn hε hpos hfin hcont h).symm

end ContinuousClosedBall

end PseudoMetricSpace

/-! ### Translations -/

section Translation

variable {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
  {μ : Measure E} [μ.IsAddRightInvariant] {s : Set E} {x h : E} {d : ℝ≥0∞}

/-- For a translation-invariant measure, the density of the translate `(· + h) ⁻¹' s` at `x` is the
density of `s` at `x + h`. -/
@[simp]
theorem hasDensityAt_preimage_add_right :
    HasDensityAt μ ((· + h) ⁻¹' s) x d ↔ HasDensityAt μ s (x + h) d := by
  have hball (r : ℝ) : closedBall x r = (· + h) ⁻¹' closedBall (x + h) r := by
    rw [preimage_add_right_closedBall, add_sub_cancel_right]
  simp only [hasDensityAt_iff, hball, ← preimage_inter, measure_preimage_add_right]

/-- For a translation-invariant measure, the essential interior commutes with translations. -/
@[simp]
theorem essentialInterior_preimage_add_right :
    essentialInterior μ ((· + h) ⁻¹' s) = (· + h) ⁻¹' essentialInterior μ s :=
  ext fun _ => hasDensityAt_preimage_add_right

/-- For a translation-invariant measure, the essential exterior commutes with translations. -/
@[simp]
theorem essentialExterior_preimage_add_right :
    essentialExterior μ ((· + h) ⁻¹' s) = (· + h) ⁻¹' essentialExterior μ s :=
  ext fun _ => hasDensityAt_preimage_add_right

/-- For a translation-invariant measure, the essential boundary commutes with translations. -/
@[simp]
theorem essentialBoundary_preimage_add_right :
    essentialBoundary μ ((· + h) ⁻¹' s) = (· + h) ⁻¹' essentialBoundary μ s := by
  rw [essentialBoundary_def, essentialBoundary_def, essentialInterior_preimage_add_right,
    essentialExterior_preimage_add_right, preimage_compl, preimage_union]

end Translation

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

/-! ### Lower volume density bounds for Haar measures -/

section AddHaar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E} {x : E}

/-- Against an additive Haar measure on a space of dimension `n`, a set filling a proportion
`ofReal (r ^ n) ≤ c μ(s ∩ ball x r)`, `c ≠ ∞`, of every small ball around `x` does not have density
zero at `x`. -/
theorem not_hasDensityAt_zero_of_eventually_ofReal_pow_le_mul_measure_inter_ball {c : ℝ≥0∞}
    (hc : c ≠ ∞)
    (h : ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤ c * μ (s ∩ ball x r)) :
    ¬HasDensityAt μ s x 0 := by
  intro h0
  have hB : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  -- The proportions of `s` in the closed balls stay above `(c μ(ball 0 1))⁻¹`.
  have hlim : Tendsto (fun r => c * μ (ball (0 : E) 1) *
      (μ (s ∩ closedBall x r) / μ (closedBall x r))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hasDensityAt_iff.1 h0)
      (Or.inr (ENNReal.mul_ne_top hc hB))
  refine absurd (ge_of_tendsto hlim ?_) (by simp : ¬(1 : ℝ≥0∞) ≤ 0)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  have h0' : μ (closedBall x r) ≠ 0 := (measure_closedBall_pos μ x hr0).ne'
  have htop : μ (closedBall x r) ≠ ∞ := measure_closedBall_lt_top.ne
  rw [← ENNReal.div_self h0' htop, ← mul_div_assoc]
  refine ENNReal.div_le_div_right ?_ _
  rw [Measure.addHaar_closedBall μ x hr0.le, mul_right_comm]
  gcongr
  exact hr.trans (by gcongr; exact ball_subset_closedBall)

/-- **Zero-one density dichotomy.** Against an additive Haar measure on a finite-dimensional real
normed space, if `min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r) → 0`
as `r → 0⁺`, then `s` has either density zero or density one at `x`. No measurability of `s` is
needed. -/
theorem hasDensityAt_zero_or_one_of_tendsto_min_div
    (h : Tendsto (fun r =>
      min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) :
    HasDensityAt μ s x 0 ∨ HasDensityAt μ s x 1 :=
  hasDensityAt_zero_or_one_of_tendsto_min_div_of_continuousOn one_pos
    (fun _ hr => (measure_closedBall_pos μ x hr.1).ne')
    (fun _ _ => measure_closedBall_lt_top.ne)
    (((μ.continuousOn_addHaar_inter_closedBall x univ).mono
        (Ioo_subset_Ico_self.trans Ico_subset_Ici_self)).congr
      fun _ _ => congrArg (μ ·) (univ_inter _).symm)
    h

/-- If `min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r) → 0` as
`r → 0⁺` against an additive Haar measure, then `x` does not belong to the essential boundary of
`s`. No measurability of `s` is needed. -/
theorem notMem_essentialBoundary_of_tendsto_min_div
    (h : Tendsto (fun r =>
      min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) :
    x ∉ essentialBoundary μ s :=
  notMem_essentialBoundary_of_tendsto_min_div_of_continuousOn one_pos
    (fun _ hr => (measure_closedBall_pos μ x hr.1).ne')
    (fun _ _ => measure_closedBall_lt_top.ne)
    (((μ.continuousOn_addHaar_inter_closedBall x univ).mono
        (Ioo_subset_Ico_self.trans Ico_subset_Ici_self)).congr
      fun _ _ => congrArg (μ ·) (univ_inter _).symm)
    h

/-- **Points of the essential boundary are balanced at arbitrarily small scales.** Against an
additive Haar measure, at a point `x` of the essential boundary of any set `s`, there is `a > 0`
such that for arbitrarily small radii `r > 0` both `s` and its complement fill a proportion at
least `a` of `closedBall x r`. -/
theorem exists_pos_frequently_ofReal_mul_measure_closedBall_le (hx : x ∈ essentialBoundary μ s) :
    ∃ a > 0, ∃ᶠ r in 𝓝[>] 0,
      ENNReal.ofReal a * μ (closedBall x r) ≤ μ (s ∩ closedBall x r) ∧
        ENNReal.ofReal a * μ (closedBall x r) ≤ μ (closedBall x r \ s) := by
  have hnot : ¬Tendsto (fun r =>
      min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) :=
    fun h => notMem_essentialBoundary_of_tendsto_min_div h hx
  rw [ENNReal.tendsto_nhds_zero] at hnot
  push Not at hnot
  obtain ⟨ε, hεpos, hfreq⟩ := hnot
  have hle1 (r : ℝ) :
      min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r) ≤ 1 := by
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact (min_le_left _ _).trans (measure_mono inter_subset_right)
  have hεlt : ε < 1 := by
    obtain ⟨r, hr⟩ := hfreq.exists
    exact hr.trans_le (hle1 r)
  have hεtop : ε ≠ ∞ := hεlt.trans_le le_top |>.ne
  refine ⟨ε.toReal, ENNReal.toReal_pos hεpos.ne' hεtop,
    (hfreq.and_eventually self_mem_nhdsWithin).mono fun r ⟨hrε, (hr0 : 0 < r)⟩ => ?_⟩
  rw [ENNReal.ofReal_toReal hεtop]
  have hle := (ENNReal.le_div_iff_mul_le (.inl (measure_closedBall_pos μ x hr0).ne')
    (.inl measure_closedBall_lt_top.ne)).1 hrε.le
  exact ⟨hle.trans (min_le_left _ _), hle.trans (min_le_right _ _)⟩

end AddHaar

end TauCeti
