/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.EMetricSpace.Defs

/-!
# Marginal masses and sections of product measures

For a measure `π` on `α × β` with measurable singletons, the mass that the first marginal
`π.map Prod.fst` gives to a point `x` is the sum of the masses of the points `(x, y)` of the row
over `x`, when `β` is finite, and symmetrically for the second marginal. Mathlib records this for
the extended masses (`MeasureTheory.measure_preimage_fst_singleton_eq_sum`); this file states it
for the real masses `Measure.real`. A set of zero first-marginal mass carries no mass in any
rectangle over it (`MeasureTheory.Measure.measure_prod_eq_zero_of_fst_eq_zero`). The graph
`{z | z.2 = f z.1}` of a measurable function is null for `μ.prod ν` whenever `ν` gives no mass to
points (`MeasureTheory.Measure.prod_graph_eq_zero`).
For a probability measure `μ`, the pairs with a coordinate in a set `s` have `μ.prod μ`-measure
at most `2 * μ s` (`MeasureTheory.Measure.prod_self_union_le_two_mul`). Weighting by a function
of the first coordinate commutes with taking the first marginal (`fst_withDensity`).
Projecting a measurable restriction of a product weights the first factor by the masses of
its vertical sections (`map_fst_restrict_prod_eq_withDensity`).

If the pushforward of a product `(μ.map Z).prod ρ` along `(z, t) ↦ (z, f z t)` is the joint law of
`(Z, X)` for a nonzero finite `μ`, then `ρ` is a probability measure
(`MeasureTheory.Measure.isProbabilityMeasure_of_map_prod_eq`).

It also records that almost every section of an almost-everywhere measurable function on a
product `μ.prod ν` is almost-everywhere measurable (`AEMeasurable.prodMk_left`), the counterpart of
Mathlib's `MeasureTheory.AEStronglyMeasurable.prodMk_left`.

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
