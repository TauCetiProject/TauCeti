/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Distance controlled by cumulative variation

Cumulative signed variation controls distances between values of a metric-valued function.
In particular, the function is constant on each fibre of cumulative variation, allowing an
arclength factorization even when the original curve has pauses.
-/

public section

open Set

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
