/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Distance controlled by cumulative variation

Cumulative signed variation controls distances between values of a metric-valued function.
In particular, the function is constant on each fibre of cumulative variation, allowing an
arclength factorization even when the original curve has pauses.

The file also records that cumulative variation only depends on the function on `s`
(`variationOnFromTo.eq_of_eqOn`), and the antitone counterpart
`variationOnFromTo.comp_eq_of_antitoneOn` of Mathlib's `variationOnFromTo.comp_eq_of_monotoneOn`.
-/

public section

open Set

namespace variationOnFromTo

variable {α β E : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace E]
  [WeakPseudoEMetricSpace E]

/-- Cumulative signed variation only depends on the function on `s`. -/
protected theorem eq_of_eqOn {f f' : α → E} {s : Set α} (h : EqOn f f' s) :
    variationOnFromTo f s = variationOnFromTo f' s := by
  funext a b
  rcases le_total a b with hab | hba
  · rw [variationOnFromTo.eq_of_le _ _ hab, variationOnFromTo.eq_of_le _ _ hab,
      eVariationOn.eq_of_eqOn (h.mono inter_subset_left)]
  · rw [variationOnFromTo.eq_of_ge _ _ hba, variationOnFromTo.eq_of_ge _ _ hba,
      eVariationOn.eq_of_eqOn (h.mono inter_subset_left)]

/-- Composing with an antitone map reverses the endpoints of cumulative signed variation. -/
protected theorem comp_eq_of_antitoneOn (f : α → E) {t : Set β} (φ : β → α)
    (hφ : AntitoneOn φ t) {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    variationOnFromTo (f ∘ φ) t x y = variationOnFromTo f (φ '' t) (φ y) (φ x) := by
  rcases le_total x y with h | h
  · rw [variationOnFromTo.eq_of_le _ _ h, variationOnFromTo.eq_of_le _ _ (hφ hx hy h),
      eVariationOn.comp_inter_Icc_eq_of_antitoneOn f φ hφ hx hy]
  · rw [variationOnFromTo.eq_of_ge _ _ h, variationOnFromTo.eq_of_ge _ _ (hφ hy hx h),
      eVariationOn.comp_inter_Icc_eq_of_antitoneOn f φ hφ hy hx]

end variationOnFromTo

namespace LocallyBoundedVariationOn

variable {α X : Type*} [LinearOrder α] [PseudoMetricSpace X]
  {f : α → X} {s : Set α}

/-- Distances between values are bounded by the difference of cumulative signed variations. -/
theorem dist_le_abs_sub_variationOnFromTo (hf : LocallyBoundedVariationOn f s)
    {a x y : α} (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ |variationOnFromTo f s a x - variationOnFromTo f s a y| := by
  rw [variationOnFromTo.sub_right hf ha hx hy]
  rcases le_total x y with hxy | hyx
  · rw [variationOnFromTo.eq_of_ge _ _ hxy, abs_neg,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact (hf x y hx hy).dist_le ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  · rw [variationOnFromTo.eq_of_le _ _ hyx, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (hf y x hy hx).dist_le ⟨hx, hyx, le_rfl⟩ ⟨hy, le_rfl, hyx⟩

end LocallyBoundedVariationOn

namespace LocallyBoundedVariationOn

variable {α X : Type*} [LinearOrder α] [MetricSpace X]
  {f : α → X} {s : Set α}

/-- A metric-valued function with locally bounded variation factors through its cumulative
signed variation by a 1-Lipschitz map on the image of that variation. -/
theorem exists_lipschitzOnWith_comp_variationOnFromTo_eqOn
    (hf : LocallyBoundedVariationOn f s) {a : α} (ha : a ∈ s) :
    ∃ g : ℝ → X,
      LipschitzOnWith 1 g (variationOnFromTo f s a '' s) ∧
      EqOn (g ∘ variationOnFromTo f s a) f s := by
  let : Nonempty α := ⟨a⟩
  let v := variationOnFromTo f s a
  let ψ := v.invFunOn s
  have hψ : MapsTo ψ (v '' s) s := (surjOn_image v s).mapsTo_invFunOn
  have hvψ : RightInvOn ψ v (v '' s) := (surjOn_image v s).rightInvOn_invFunOn
  have hbound {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
      dist (f x) (f y) ≤ |v x - v y| :=
    hf.dist_le_abs_sub_variationOnFromTo ha hx hy
  refine ⟨f ∘ ψ, LipschitzOnWith.mk_one ?_, ?_⟩
  · intro u hu w hw
    simpa only [Function.comp_apply, hvψ hu, hvψ hw, Real.dist_eq] using
      hbound (hψ hu) (hψ hw)
  · intro x hx
    have hvx : v x ∈ v '' s := mem_image_of_mem v hx
    have hdist := hbound (hψ hvx) hx
    rw [hvψ hvx, sub_self, abs_zero] at hdist
    exact dist_le_zero.mp hdist

/-- Cumulative signed variation is strictly increasing on a set where the original function
is injective. -/
theorem strictMonoOn_variationOnFromTo (hf : LocallyBoundedVariationOn f s)
    {a : α} (ha : a ∈ s) (hinj : InjOn f s) :
    StrictMonoOn (variationOnFromTo f s a) s := by
  intro x hx y hy hxy
  refine lt_of_le_of_ne (variationOnFromTo.monotoneOn hf ha hx hy hxy.le) ?_
  intro heq
  have hdist := hf.dist_le_abs_sub_variationOnFromTo ha hx hy
  rw [heq, sub_self, abs_zero] at hdist
  exact hxy.ne (hinj hx hy (dist_le_zero.mp hdist))

end LocallyBoundedVariationOn

namespace LocallyBoundedVariationOn

variable {α X : Type*} [LinearOrder α] [DenselyOrdered α] [MetricSpace X]
  {f : α → X} {a b c : α}

/-- Injectivity on the interior of an interval makes cumulative variation strictly increasing
on the closed interval. Thus equal endpoint values do not obstruct the arclength coordinate. -/
theorem strictMonoOn_variationOnFromTo_of_injOn_Ioo
    (hf : LocallyBoundedVariationOn f (Icc a b)) (hc : c ∈ Icc a b)
    (hinj : InjOn f (Ioo a b)) :
    StrictMonoOn (variationOnFromTo f (Icc a b) c) (Icc a b) := by
  have hm := variationOnFromTo.monotoneOn hf hc
  intro x hx y hy hxy
  refine lt_of_le_of_ne (hm hx hy hxy.le) ?_
  intro heq
  -- A flat cumulative variation would identify two distinct interior values of the curve.
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  obtain ⟨v, huv, hvy⟩ := exists_between huy
  have hu : u ∈ Icc a b := ⟨hx.1.trans hxu.le, huy.le.trans hy.2⟩
  have hv : v ∈ Icc a b := ⟨hu.1.trans huv.le, hvy.le.trans hy.2⟩
  have heu : variationOnFromTo f (Icc a b) c u = variationOnFromTo f (Icc a b) c x :=
    le_antisymm ((hm hu hy huy.le).trans_eq heq.symm) (hm hx hu hxu.le)
  have hev : variationOnFromTo f (Icc a b) c v = variationOnFromTo f (Icc a b) c x :=
    le_antisymm ((hm hv hy hvy.le).trans_eq heq.symm)
      (hm hx hv (hxu.trans huv).le)
  have hd := hf.dist_le_abs_sub_variationOnFromTo hc hu hv
  rw [heu, hev, sub_self, abs_zero] at hd
  exact huv.ne (hinj ⟨hx.1.trans_lt hxu, huy.trans_le hy.2⟩
    ⟨hu.1.trans_lt huv, hvy.trans_le hy.2⟩ (dist_le_zero.mp hd))

end LocallyBoundedVariationOn
