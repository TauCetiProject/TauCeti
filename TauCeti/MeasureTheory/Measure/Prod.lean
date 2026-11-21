/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.EMetricSpace.Defs
public import TauCeti.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Marginal masses and sections of product measures

For a measure `π` on `α × β` with measurable singletons, the mass that the first marginal
`π.map Prod.fst` gives to a point `x` is the sum of the masses of the points `(x, y)` of the row
over `x`, when `β` is finite, and symmetrically for the second marginal. Mathlib records this for
the extended masses (`MeasureTheory.measure_preimage_fst_singleton_eq_sum`); this file states it
for the real masses `Measure.real`. A set of zero first-marginal mass carries no mass in any
rectangle over it (`MeasureTheory.Measure.measure_prod_eq_zero_of_fst_eq_zero`). The graph
`{z | z.2 = f z.1}` of a measurable function is null for `μ.prod ν` whenever `ν` gives no mass to
points (`MeasureTheory.Measure.prod_graph_eq_zero`). More generally, for an s-finite second factor
the graph has measure `∑' y, μ (f ⁻¹' {y}) * ν {y}` (`MeasureTheory.Measure.prod_graph`), and the
diagonal carries mass `∑' x, μ {x} * ν {x}` (`MeasureTheory.Measure.prod_diagonal`, with real-valued
counterparts `MeasureTheory.Measure.hasSum_prod_real_diagonal` and
`MeasureTheory.Measure.prod_real_diagonal` for finite measures).
For a probability measure `μ`, the pairs with a coordinate in a set `s` have `μ.prod μ`-measure
at most `2 * μ s` (`MeasureTheory.Measure.prod_self_union_le_two_mul`). Weighting by a function
of the first coordinate commutes with taking the first marginal (`fst_withDensity`).
Projecting a measurable restriction of a product weights the first factor by the masses of
its vertical sections (`map_fst_restrict_prod_eq_withDensity`). Rectangle bounds also give
finite interval-selection masses and a local-finiteness criterion for projected restrictions
away from an initial endpoint. Partitioning an arbitrary measure on `X × ι` into countable
singleton slices `univ ×ˢ {i}` and projecting onto `X` sums back to `μ.map Prod.fst`
(`sum_map_fst_restrict_univ_prod_singleton`).

If the pushforward of a product `(μ.map Z).prod ρ` along `(z, t) ↦ (z, f z t)` is the joint law of
`(Z, X)` for a nonzero finite `μ`, then `ρ` is a probability measure
(`MeasureTheory.Measure.isProbabilityMeasure_of_map_prod_eq`). If such a coding `g` has a joint law
with its base point invariant under a measurable involution `sw` of the base and the swap of the
pair, then coding at the swapped base point and swapping the output has the same joint law
(`MeasureTheory.Measure.map_prod_swap_apply_eq`).

It also records that almost every section of an almost-everywhere measurable function on a
product `μ.prod ν` is almost-everywhere measurable (`AEMeasurable.prodMk_left`), the counterpart of
Mathlib's `MeasureTheory.AEStronglyMeasurable.prodMk_left`.
For a countable first factor with measurable singletons, the converse is characterized by
`MeasureTheory.Measure.aemeasurable_uncurry_prod_iff`. Mapping an indexed family over a product
then gives a measure bind (`MeasureTheory.Measure.map_uncurry_prod_eq_bind_map`), with evaluation
specializations for function-valued and product laws.

Finally, for a measurable map `f` into an additive group, the law of `f z.1 - f z.2` under
`μ.prod μ` is symmetric (`MeasureTheory.Measure.map_neg_map_sub_prod_self`): swapping the two
identical factors negates the difference.

If the second factor has a negation-invariant law, negating the second coordinate exactly when
the first satisfies a measurable predicate preserves the product measure
(`MeasureTheory.Measure.measurePreserving_prod_skew_neg`). For real-valued coordinates, the
quotient `z.1 / z.2` has the same law as `z.1 / |z.2|` when the numerator's law is reflection
invariant (`MeasureTheory.Measure.map_div_prod_eq_map_div_abs`).

A coupling that moves almost every point by less than `r` and is carried in its second marginal
by a set `s` gives no first-marginal mass to a point at distance at least `r` from every point of
`s` (`MeasureTheory.measure_fst_singleton_eq_zero_of_ae_edist_lt`).
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

/-- Partitioning a measure on `X × ι` (for a countable discrete space `ι`) into vertical singleton
slices `univ ×ˢ {i}` and projecting onto `X` recovers `μ.map Prod.fst` for every measure `μ`. -/
theorem sum_map_fst_restrict_univ_prod_singleton {X ι : Type*} [MeasurableSpace X] [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (μ : Measure (X × ι)) :
    (Measure.sum fun i : ι ↦ (μ.restrict (Set.univ ×ˢ {i})).map Prod.fst) = μ.map Prod.fst := by
  have hunion : (⋃ i : ι, (Set.univ ×ˢ ({i} : Set ι) : Set (X × ι))) = Set.univ := by
    ext ⟨_, i⟩
    simp
  have hd : Pairwise (Function.onFun Disjoint
      fun i : ι ↦ (Set.univ ×ˢ ({i} : Set ι) : Set (X × ι))) :=
    fun _ _ hij ↦ Set.disjoint_left.mpr fun _ h₁ h₂ ↦
      hij ((Set.mem_singleton_iff.mp h₁.2).symm.trans (Set.mem_singleton_iff.mp h₂.2))
  rw [← Measure.map_sum measurable_fst.aemeasurable,
    ← Measure.restrict_iUnion hd (fun i ↦ MeasurableSet.univ.prod (measurableSet_singleton i)),
    hunion, Measure.restrict_univ]

/-- Projecting a joint measure restricted to `u ×ˢ A` assigns mass `μ ((s ∩ u) ×ˢ A)`
to each measurable set `s` in the first coordinate. -/
@[simp]
theorem map_fst_restrict_prod_apply {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure (α × β)) (u : Set α) (A : Set β)
    {s : Set α} (hs : MeasurableSet s) :
    ((μ.restrict (u ×ˢ A)).map Prod.fst) s = μ ((s ∩ u) ×ˢ A) := by
  rw [map_apply measurable_fst hs, ← Set.prod_univ,
    restrict_apply (hs.prod MeasurableSet.univ)]
  simp only [Set.prod_inter_prod, Set.univ_inter]

/-- The mass of a rectangle under a product measure is bounded by the product of its masses,
without measurability or s-finiteness assumptions. -/
theorem prod_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (s : Set α) (t : Set β) :
    μ.prod ν (s ×ˢ t) ≤ μ s * ν t := by
  by_cases hν : SFinite ν
  · let := hν
    exact le_of_eq (prod_prod s t)
  · simp [prod_eq_zero_of_not_sfinite hν]

/-- A bounded right-closed interval paired with a finite-mass selection has finite product
mass when the first measure is locally finite. The second measure need not be s-finite. -/
theorem prod_Ioc_prod_lt_top {α β : Type*} [Preorder α] [TopologicalSpace α]
    [CompactIccSpace α] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] (ν : Measure β)
    {A : Set β} (hνA : ν A ≠ ∞) (a b : α) : (μ.prod ν) (Set.Ioc a b ×ˢ A) < ∞ :=
  (prod_prod_le μ ν _ _).trans_lt (ENNReal.mul_lt_top measure_Ioc_lt_top hνA.lt_top)

/-- A rectangle consisting of a bounded right-closed interval and a singleton has finite mass
under any measure finite on compact sets. -/
theorem measure_Ioc_prod_singleton_lt_top {α β : Type*} [Preorder α]
    [TopologicalSpace α] [CompactIccSpace α] [MeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] (μ : Measure (α × β))
    [IsFiniteMeasureOnCompacts μ] (y : β) (a b : α) : μ (Set.Ioc a b ×ˢ {y}) < ∞ :=
  (measure_mono (Set.prod_mono Set.Ioc_subset_Icc_self Set.Subset.rfl)).trans_lt
    (isCompact_Icc.prod isCompact_singleton).measure_lt_top

/-- A projected restriction above an endpoint is locally finite if all its bounded
right-closed windows have finite mass. No finiteness at the excluded endpoint is needed. -/
theorem isLocallyFiniteMeasure_map_fst_restrict_Ioi_prod {α β : Type*} [LinearOrder α]
    [TopologicalSpace α] [ClosedIciTopology α] [ClosedIicTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) (a : α) (A : Set β)
    (hfin : ∀ t : α, μ (Set.Ioc a t ×ˢ A) < ∞) :
    IsLocallyFiniteMeasure ((μ.restrict (Set.Ioi a ×ˢ A)).map Prod.fst) := by
  apply Measure.isLocallyFiniteMeasure_of_measure_Iic_lt_top
  intro t
  rw [map_fst_restrict_prod_apply _ _ _ measurableSet_Iic,
    Set.inter_comm (Set.Iic t), Set.Ioi_inter_Iic]
  exact hfin t

/-- A first marginal is locally finite when the joint measure is locally finite and the
second space is compact. -/
theorem isLocallyFiniteMeasure_map_fst {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [TopologicalSpace α] [TopologicalSpace β] [OpensMeasurableSpace α]
    [CompactSpace β] (μ : Measure (α × β))
    [IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (μ.map Prod.fst) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨W, hW, hWo, hWfin⟩ :=
    (isCompact_singleton (x := x)).prod isCompact_univ |>.exists_open_superset_measure_lt_top μ
  obtain ⟨u, v, huo, _, hxu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hWo hW
  refine ⟨u, huo.mem_nhds (hxu (Set.mem_singleton x)), ?_⟩
  rw [map_apply measurable_fst huo.measurableSet, ← Set.prod_univ]
  exact (measure_mono ((Set.prod_mono Set.Subset.rfl hv).trans huv)).trans_lt hWfin

/-- Projecting the part of a product measure in a measurable set gives the first measure
weighted by the masses of the vertical sections. Only the second factor must be s-finite. -/
theorem map_fst_restrict_prod_eq_withDensity {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    ((μ.prod ν).restrict A).map Prod.fst =
      μ.withDensity (fun x ↦ ν (Prod.mk x ⁻¹' A)) := by
  ext s hs
  rw [map_apply measurable_fst hs, restrict_apply (measurable_fst hs),
    prod_apply ((measurable_fst hs).inter hA), withDensity_apply _ hs,
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s <;> simp [Set.preimage, hx]

/-- Weighting a joint measure by a function of its first coordinate weights its first marginal
by the same function. The weight only needs to be almost everywhere measurable for the first
marginal, and no finiteness assumption is needed. -/
@[simp]
theorem fst_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) {f : α → ℝ≥0∞} (hf : AEMeasurable f ρ.fst) :
    (ρ.withDensity (fun p ↦ f p.1)).fst = ρ.fst.withDensity f := by
  ext s hs
  have hfs : AEMeasurable f ((ρ.restrict (Prod.fst ⁻¹' s)).map Prod.fst) := by
    rw [← restrict_map measurable_fst hs]
    exact hf.restrict
  rw [fst_apply hs, withDensity_apply _ (measurable_fst hs), withDensity_apply _ hs, fst,
    restrict_map measurable_fst hs, lintegral_map' hfs measurable_fst.aemeasurable]

/-- A weight on the first marginal with finite integral makes the weighted joint measure
finite. -/
theorem isFiniteMeasure_withDensity_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) {f : α → ℝ≥0∞} (hf : AEMeasurable f ρ.fst)
    (hint : ∫⁻ x, f x ∂ρ.fst ≠ ∞) :
    IsFiniteMeasure (ρ.withDensity (fun p ↦ f p.1)) :=
  isFiniteMeasure_withDensity <| by
    rwa [fst, lintegral_map' hf measurable_fst.aemeasurable] at hint

/-- A set of zero first-marginal mass carries no mass in any rectangle over it: if
`σ.fst t = 0`, then `σ (t ×ˢ s) = 0` for every `s`. Neither set needs to be measurable. -/
theorem measure_prod_eq_zero_of_fst_eq_zero {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (σ : Measure (α × β)) {t : Set α} (ht : σ.fst t = 0) (s : Set β) :
    σ (t ×ˢ s) = 0 :=
  measure_mono_null (Set.prod_subset_preimage_fst t s)
    (preimage_null_of_map_null measurable_fst.aemeasurable ht)

/-- The graph of a measurable function is null for a product measure whose second factor gives
no mass to points, since each vertical section of the graph is a single point. No
sigma-finiteness assumption is needed. -/
theorem prod_graph_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableEq β] {μ : Measure α} {ν : Measure β} [NullSingletonClass ν] {f : α → β}
    (hf : Measurable f) : μ.prod ν {z : α × β | z.2 = f z.1} = 0 :=
  measure_prod_null_of_ae_null (measurableSet_eq_fun measurable_snd (hf.comp measurable_fst))
    (Filter.Eventually.of_forall fun x ↦ by simp)

/-- The product measure of the graph `{z | z.2 = f z.1}` of a measurable function is the sum over
all target points `y` of `μ (f ⁻¹' {y}) * ν {y}`. Only the second factor must be s-finite. -/
theorem prod_graph {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableEq β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] {f : α → β} (hf : Measurable f) :
    (μ.prod ν) {z : α × β | z.2 = f z.1} = ∑' y : β, μ (f ⁻¹' {y}) * ν {y} := by
  have hmeas : MeasurableSet {z : α × β | z.2 = f z.1} :=
    measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  have hS : ({y : β | 0 < ν {y}}).Countable := by
    simpa using Measure.countable_meas_level_set_pos (μ := ν) (g := id) measurable_id
  set S : Set β := {y : β | 0 < ν {y}}
  have hSm : MeasurableSet (f ⁻¹' S) := hf hS.measurableSet
  have hcompl : ∫⁻ x in (f ⁻¹' S)ᶜ, ν {f x} ∂μ = 0 := by
    refine setLIntegral_eq_zero hSm.compl ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_preimage, S, Set.mem_ofPred_eq, not_lt,
      nonpos_iff_eq_zero] at hx
    exact hx
  have hbiUnion : f ⁻¹' S = ⋃ y ∈ S, f ⁻¹' {y} := by
    ext x
    simp
  rw [prod_apply hmeas]
  have hsec : ∀ x : α, Prod.mk x ⁻¹' {z : α × β | z.2 = f z.1} = {f x} := fun x ↦ by
    ext y
    simp
  simp_rw [hsec]
  rw [← lintegral_add_compl _ hSm, hcompl, add_zero, hbiUnion,
    lintegral_biUnion hS (fun y _ ↦ hf (measurableSet_singleton y))
      (Set.pairwiseDisjoint_fiber f S)]
  have hterm (y : S) : ∫⁻ x in f ⁻¹' {(y : β)}, ν {f x} ∂μ = μ (f ⁻¹' {(y : β)}) * ν {(y : β)} := by
    calc ∫⁻ x in f ⁻¹' {(y : β)}, ν {f x} ∂μ
        = ∫⁻ _ in f ⁻¹' {(y : β)}, ν {(y : β)} ∂μ :=
          setLIntegral_congr_fun (hf (measurableSet_singleton _)) fun x hx ↦ by
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
            rw [hx]
      _ = ν {(y : β)} * μ (f ⁻¹' {(y : β)}) := setLIntegral_const _ _
      _ = μ (f ⁻¹' {(y : β)}) * ν {(y : β)} := mul_comm _ _
  simp_rw [hterm]
  rw [tsum_subtype S (fun y ↦ μ (f ⁻¹' {y}) * ν {y})]
  congr 1 with y
  by_cases hy : y ∈ S
  · simp [Set.indicator_of_mem hy]
  · have hνy : ν {y} = 0 := by
      simpa [S, not_lt, nonpos_iff_eq_zero] using hy
    simp [Set.indicator_of_notMem hy, hνy]

/-- The product measure of the diagonal `Set.diagonal α` is `∑' x, μ {x} * ν {x}`. Only the second
factor must be s-finite. -/
theorem prod_diagonal {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (μ ν : Measure α) [SFinite ν] :
    (μ.prod ν) (Set.diagonal α) = ∑' x : α, μ {x} * ν {x} := by
  have hdiag : Set.diagonal α = {z : α × α | z.2 = id z.1} := by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [hdiag, prod_graph μ ν measurable_id]
  simp

/-- For finite measures `μ` and `ν` on a space with measurable diagonal, the products
`μ.real {x} * ν.real {x}` of their singleton masses are summable with sum
`(μ.prod ν).real (Set.diagonal α)`. -/
theorem hasSum_prod_real_diagonal {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HasSum (fun x : α ↦ μ.real {x} * ν.real {x}) ((μ.prod ν).real (Set.diagonal α)) := by
  have hne : ∑' x : α, μ {x} * ν {x} ≠ ∞ := by
    rw [← prod_diagonal]
    exact measure_ne_top _ _
  have hsum : Summable fun x : α ↦ μ.real {x} * ν.real {x} := by
    simpa only [ENNReal.toReal_mul, measureReal_def] using ENNReal.summable_toReal hne
  have htsum : ∑' x : α, μ.real {x} * ν.real {x} = (μ.prod ν).real (Set.diagonal α) := by
    rw [measureReal_def, prod_diagonal, ENNReal.tsum_toReal_eq (fun _ ↦ by finiteness)]
    simp_rw [ENNReal.toReal_mul, measureReal_def]
  exact htsum ▸ hsum.hasSum

/-- For finite measures `μ` and `ν` on a space with measurable diagonal, the real mass of the
diagonal under `μ.prod ν` is `∑' x, μ.real {x} * ν.real {x}`. -/
theorem prod_real_diagonal {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ.prod ν).real (Set.diagonal α) = ∑' x : α, μ.real {x} * ν.real {x} :=
  (hasSum_prod_real_diagonal μ ν).tsum_eq.symm

/-- For a probability measure `μ` and any set `s`, the pairs having a first or a second coordinate
in `s` have `μ.prod μ`-measure at most twice `μ s`. No measurability is needed. -/
theorem prod_self_union_le_two_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) :
    (μ.prod μ) ((s ×ˢ (Set.univ : Set α)) ∪ ((Set.univ : Set α) ×ˢ s)) ≤ 2 * μ s := by
  calc _ ≤ (μ.prod μ) (s ×ˢ (Set.univ : Set α)) + (μ.prod μ) ((Set.univ : Set α) ×ˢ s) :=
        measure_union_le _ _
    _ = μ s + μ s := by
        rw [Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, one_mul]
    _ = 2 * μ s := (two_mul _).symm

variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] {π : Measure (α × β)}

/-- The real mass of a point under the first marginal of a measure on `α × β`, with `β` finite, is
the sum of the real masses of the points of its row. -/
theorem map_fst_real_singleton [Fintype β] (x : α)
    (h : ∀ y, π {(x, y)} ≠ ∞ := by finiteness) :
    (π.map Prod.fst).real {x} = ∑ y, π.real {(x, y)} := by
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton x), measureReal_def,
    measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum fun y _ ↦ h y]
  simp_rw [measureReal_def]

/-- The real mass of a point under the second marginal of a measure on `α × β`, with `α` finite,
is the sum of the real masses of the points of its column. -/
theorem map_snd_real_singleton [Fintype α] (y : β)
    (h : ∀ x, π {(x, y)} ≠ ∞ := by finiteness) :
    (π.map Prod.snd).real {y} = ∑ x, π.real {(x, y)} := by
  rw [map_measureReal_apply measurable_snd (measurableSet_singleton y), measureReal_def,
    measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum fun x _ ↦ h x]
  simp_rw [measureReal_def]

/-- The law of the difference `f z.1 - f z.2` of two coordinates of a product measure `μ.prod μ`
is symmetric: swapping the two identical factors negates the difference. No finiteness
assumption on `μ` is needed. -/
theorem map_neg_map_sub_prod_self {γ G : Type*} [MeasurableSpace γ] [MeasurableSpace G]
    [AddGroup G] [MeasurableNeg G] [MeasurableSub₂ G] (μ : Measure γ) {f : γ → G}
    (hf : Measurable f) :
    ((μ.prod μ).map fun z => f z.1 - f z.2).map Neg.neg =
      (μ.prod μ).map fun z => f z.1 - f z.2 := by
  -- The product with a measure that is not s-finite is zero.
  by_cases hμ : SFinite μ
  swap
  · simp [prod_eq_zero_of_not_sfinite hμ]
  rw [map_map measurable_neg (by fun_prop)]
  conv_lhs => rw [← prod_swap]
  rw [map_map (measurable_neg.comp (by fun_prop)) measurable_swap]
  congr 1
  funext z
  simp

/-- Negating the second coordinate exactly when the first satisfies a measurable predicate `p`
preserves the product of a measure with a negation-invariant measure, because every fibre
transformation preserves the second measure. No finiteness assumption is needed. -/
theorem measurePreserving_prod_skew_neg {α G : Type*} [MeasurableSpace α] [MeasurableSpace G]
    [Neg G] [MeasurableNeg G] {μ : Measure α} {ν : Measure G} {p : α → Prop} [DecidablePred p]
    (hp : MeasurableSet {x | p x}) (hν : ν.map (fun y : G ↦ -y) = ν) :
    MeasurePreserving (fun z : α × G ↦ (z.1, if p z.1 then -z.2 else z.2))
      (μ.prod ν) (μ.prod ν) := by
  have hmeas : Measurable fun z : α × G ↦ (z.1, if p z.1 then -z.2 else z.2) :=
    measurable_fst.prodMk (Measurable.ite (measurable_fst hp) measurable_snd.neg measurable_snd)
  refine ⟨hmeas, ?_⟩
  -- The product with a measure that is not s-finite is zero.
  by_cases hsf : SFinite ν
  swap
  · simp [prod_eq_zero_of_not_sfinite hsf]
  ext s hs
  rw [map_apply hmeas hs, prod_apply (hmeas hs), prod_apply hs]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : p x
  · have hset : Prod.mk x ⁻¹' (fun z : α × G ↦ (z.1, if p z.1 then -z.2 else z.2)) ⁻¹' s =
        (fun y : G ↦ -y) ⁻¹' (Prod.mk x ⁻¹' s) := by
      ext y
      simp [hx]
    rw [hset, ← Measure.map_apply measurable_neg (measurable_prodMk_left hs), hν]
  · congr 1 with y
    simp [hx]

/-- The quotient of independent coordinates, the numerator having a reflection-invariant law, has
the same law as the quotient by the absolute value of the denominator. Only the numerator's law
must be s-finite. -/
theorem map_div_prod_eq_map_div_abs {μ ν : Measure ℝ} [SFinite μ]
    (hμ : μ.map (fun x : ℝ ↦ -x) = μ) :
    ((μ.prod ν).map fun z : ℝ × ℝ ↦ z.1 / z.2) =
      (μ.prod ν).map fun z : ℝ × ℝ ↦ z.1 / |z.2| := by
  -- The product with a measure that is not s-finite is zero.
  by_cases hν : SFinite ν
  swap
  · simp [prod_eq_zero_of_not_sfinite hν]
  let twist : ℝ × ℝ → ℝ × ℝ := fun z ↦ (if z.2 < 0 then -z.1 else z.1, z.2)
  -- Conjugating the skew map by coordinate swaps reflects the numerator exactly when the
  -- denominator is negative.
  have htwist : MeasurePreserving twist (μ.prod ν) (μ.prod ν) :=
    measurePreserving_swap.comp
      ((measurePreserving_prod_skew_neg (measurableSet_lt measurable_id measurable_const)
        hμ).comp measurePreserving_swap)
  calc
    (μ.prod ν).map (fun z : ℝ × ℝ ↦ z.1 / z.2)
        = ((μ.prod ν).map twist).map (fun z : ℝ × ℝ ↦ z.1 / z.2) := by rw [htwist.map_eq]
    _ = (μ.prod ν).map fun z : ℝ × ℝ ↦ z.1 / |z.2| := by
      rw [map_map (by fun_prop) htwist.measurable]
      congr 1 with z
      obtain hz | hz := lt_or_ge z.2 0
      · simp [twist, hz, abs_of_neg hz, neg_div, div_neg]
      · simp [twist, hz.not_gt, abs_of_nonneg hz]

open scoped symmDiff in
/-- Swapping the coordinates of an approximant of a swap-invariant set does not change the
measure of the symmetric difference. -/
theorem measure_symmDiff_preimage_swap_of_preimage_swap_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u s : Set (X × X)} (hsymm : Prod.swap ⁻¹' s = s) :
    (μ.prod μ) ((Prod.swap ⁻¹' u) ∆ s) = (μ.prod μ) (u ∆ s) := by
  -- The product with a measure that is not s-finite is zero.
  by_cases hμ : SFinite μ
  swap
  · simp [prod_eq_zero_of_not_sfinite hμ]
  calc
    (μ.prod μ) ((Prod.swap ⁻¹' u) ∆ s) = (μ.prod μ) (Prod.swap ⁻¹' (u ∆ s)) := by
      rw [Set.preimage_symmDiff, hsymm]
    _ = (μ.prod μ) (u ∆ s) :=
      (measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage_emb
        MeasurableEquiv.prodComm.measurableEmbedding _

/-- If a randomization `f` realizes a nonzero finite law, its noise is a probability measure. -/
theorem isProbabilityMeasure_of_map_prod_eq {Ω β δ ξ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSpace δ] [MeasurableSpace ξ] {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {X : Ω → β} {Z : Ω → δ} (hZ : Measurable Z) (hX : Measurable X)
    {ρ : Measure ξ} {f : δ → ξ → β} (hf : Measurable (Function.uncurry f))
    (hfX : ((μ.map Z).prod ρ).map (fun p => (p.1, f p.1 p.2)) = μ.map fun ω => (Z ω, X ω)) :
    IsProbabilityMeasure ρ := by
  have h := congrArg (fun m => m Set.univ) hfX
  have hF : Measurable (fun p : δ × ξ => (p.1, f p.1 p.2)) := measurable_fst.prodMk hf
  simp only [Measure.map_apply hF MeasurableSet.univ, Set.preimage_univ,
    Measure.map_apply (hZ.prodMk hX) MeasurableSet.univ] at h
  have hμu : μ Set.univ ≠ 0 := by simpa using hμ
  by_cases hs : SFinite ρ
  · have hprod := Measure.prod_prod (μ := μ.map Z) (ν := ρ) Set.univ Set.univ
    rw [Set.univ_prod_univ, Measure.map_apply hZ MeasurableSet.univ, Set.preimage_univ] at hprod
    rw [hprod] at h
    refine ⟨(ENNReal.mul_right_inj hμu (measure_ne_top _ _)).1 ?_⟩
    rw [mul_one]
    exact h
  · rw [Measure.prod_eq_zero_of_not_sfinite hs, FunLike.coe_zero, Pi.zero_apply] at h
    exact absurd h.symm hμu

/-- **Swapping the output and the context of a swap-invariant coding.** Let `sw` be a measurable
involution preserving a measure `L`, and let `g` code a pair from a point of the base and a point
of a second space carrying a measure `ν`. If the joint law of the base point and the coded pair
under `L.prod ν` is invariant under `sw` on the base point and the swap of the pair, then coding at
the swapped base point and swapping the output gives the same joint law as the coding itself. -/
theorem map_prod_swap_apply_eq {Z Y β : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace β] {sw : Z → Z} (hsw : Measurable sw) (hsw₂ : ∀ z, sw (sw z) = z)
    {L : Measure Z} (hL : L.map sw = L) {ν : Measure Y} {g : Z → Y → β × β}
    (hg : Measurable (Function.uncurry g))
    (hJ : ((L.prod ν).map (fun p => (p.1, g p.1 p.2))).map (Prod.map sw Prod.swap) =
      (L.prod ν).map (fun p => (p.1, g p.1 p.2))) :
    (L.prod ν).map (fun p => (p.1, (g (sw p.1) p.2).swap)) =
      (L.prod ν).map (fun p => (p.1, g p.1 p.2)) := by
  -- A product with a measure that is not s-finite is zero.
  by_cases hν : SFinite ν
  swap
  · simp [prod_eq_zero_of_not_sfinite hν]
  have hg' : Measurable (Function.uncurry fun z s => (g (sw z) s).swap) :=
    measurable_swap.comp (hg.comp (hsw.prodMap measurable_id))
  have hfun : (fun p : Z × Y => (p.1, (g (sw p.1) p.2).swap)) ∘ Prod.map sw id =
      Prod.map sw Prod.swap ∘ fun p => (p.1, g p.1 p.2) := by
    funext p
    simp [hsw₂]
  have hF : Measurable fun p : Z × Y => (p.1, g p.1 p.2) := measurable_fst.prodMk hg
  have hF' : Measurable fun p : Z × Y => (p.1, (g (sw p.1) p.2).swap) :=
    measurable_fst.prodMk hg'
  conv_lhs => rw [← hL, ← Measure.map_id (μ := ν),
    Measure.map_prod_map _ _ hsw measurable_id,
    Measure.map_map hF' (hsw.prodMap measurable_id), hfun,
    ← Measure.map_map (hsw.prodMap measurable_swap) hF, hJ]

end MeasureTheory.Measure

namespace MeasureTheory

/-- A coupling `π` that moves almost every point by less than `r` and is carried in its second
marginal by a set `s` has no first-marginal mass at a point `a` lying at distance at least `r`
from every point of `s`. -/
theorem measure_fst_singleton_eq_zero_of_ae_edist_lt {α : Type*} [PseudoEMetricSpace α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {π : Measure (α × α)} {r : ℝ≥0∞}
    {s : Set α} {a : α} (hdist : ∀ᵐ z ∂π, edist z.1 z.2 < r) (hsnd : ∀ᵐ z ∂π, z.2 ∈ s)
    (ha : ∀ x ∈ s, r ≤ edist a x) : π.fst {a} = 0 := by
  rw [Measure.fst_apply (MeasurableSet.singleton _), measure_eq_zero_iff_ae_notMem]
  filter_upwards [hdist, hsnd] with z hzdist hzs hz
  exact (not_lt_of_ge (ha _ hzs)) ((Set.mem_singleton_iff.mp hz) ▸ hzdist)

end MeasureTheory

/-- Almost every section of an almost-everywhere measurable function on `μ.prod ν` is
almost-everywhere measurable. This is the counterpart for `AEMeasurable` of
`MeasureTheory.AEStronglyMeasurable.prodMk_left`. -/
theorem AEMeasurable.prodMk_left {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite ν] {f : α × β → γ} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEMeasurable (fun y ↦ f (x, y)) ν := by
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨_, hf.measurable_mk.comp measurable_prodMk_left, hx⟩

namespace MeasureTheory.Measure

variable {I A B : Type*} [MeasurableSpace I] [MeasurableSpace A] [MeasurableSpace B]

/-- An indexed family over a countable measurable space is a.e. measurable for a product measure
exactly when every component carried by the first measure is a.e. measurable. -/
theorem aemeasurable_uncurry_prod_iff [Countable I] [MeasurableSingletonClass I]
    (μ : Measure I) (ρ : Measure A) [SFinite ρ] {f : I → A → B} :
    AEMeasurable (Function.uncurry f) (μ.prod ρ) ↔
      ∀ i, μ {i} ≠ 0 → AEMeasurable (f i) ρ := by
  constructor
  · intro hf
    exact ae_iff_of_countable.1 hf.prodMk_left
  · intro hf
    rw [← Measure.sum_smul_dirac μ, Measure.prod_sum_left]
    apply AEMeasurable.sum_measure
    intro i
    rw [Measure.prod_smul_left]
    by_cases hi : μ {i} = 0
    · simp [hi]
    · apply AEMeasurable.smul_measure
      rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left i).aemeasurable_map_iff]
      simpa only [Function.comp_def, Function.uncurry_apply_pair] using hf i hi

/-- Mapping a product measure by an almost-everywhere measurable indexed family gives the bind of
the component pushforwards. -/
theorem map_uncurry_prod_eq_bind_map (μ : Measure I) (ρ : Measure A) [SFinite ρ]
    {f : I → A → B} (hf : AEMeasurable (Function.uncurry f) (μ.prod ρ)) :
    (μ.prod ρ).map (Function.uncurry f) = μ.bind (fun i ↦ ρ.map (f i)) := by
  rw [Measure.prod_eq_of_sfinite] at hf ⊢
  rw [Measure.map_bind Measurable.map_prodMk_left.aemeasurable hf]
  apply Measure.bind_congr_right
  filter_upwards [Measurable.map_prodMk_left.aemeasurable.ae_of_bind hf] with i hi
  rw [hi.map_map_of_aemeasurable measurable_prodMk_left.aemeasurable]
  simp only [Function.comp_def, Function.uncurry_apply_pair]

/-- Mapping a product by evaluation gives the bind of the coordinate pushforwards. -/
theorem map_eval_prod_eq_bind_map [Countable I] [MeasurableSingletonClass I]
    (μ : Measure I) (ρ : Measure (I → B)) [SFinite ρ] :
    (μ.prod ρ).map (fun z ↦ z.2 z.1) = μ.bind (fun i ↦ ρ.map (Function.eval i)) := by
  simpa only [Function.uncurry_def, Function.eval] using
    map_uncurry_prod_eq_bind_map μ ρ
      ((aemeasurable_uncurry_prod_iff μ ρ).2 fun i _ ↦
        (measurable_pi_apply i).aemeasurable)

/-- Mapping a mixing law times a finite product probability law by evaluation gives the bind of
the component laws. -/
theorem map_eval_prod_pi_eq_bind [Fintype I] [MeasurableSingletonClass I]
    (μ : Measure I) (K : I → Measure B) [∀ i, IsProbabilityMeasure (K i)] :
    (μ.prod (Measure.pi K)).map (fun z ↦ z.2 z.1) = μ.bind K := by
  rw [map_eval_prod_eq_bind_map]
  apply Measure.bind_congr_right
  exact ae_of_all _ fun i ↦ (measurePreserving_eval K i).map_eq

end MeasureTheory.Measure
