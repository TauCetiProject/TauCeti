/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.EMetricSpace.VariationOnFromTo

/-!
# Continuous Jordan decomposition of locally bounded-variation paths

A continuous real-valued function of locally bounded variation is a difference of two
continuous nondecreasing functions. On the whole real line this uses variation on every compact
interval, not finite variation on a half-line or on the whole line. This decomposition allows
continuous finite-variation paths to be treated through continuous increasing integrators.

The construction is Mathlib's signed-variation decomposition
`LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'`, due to Sébastien Gouëzel,
with continuity supplied by the local continuity theorem for cumulative variation. The two
increasing parts have combined increments equal to the variation of the original path.
-/

public section

open Set

/-- A continuous locally bounded-variation real function has a continuous monotone decomposition
on its domain. The sum of the increments of the two parts is exactly the signed variation. -/
theorem LocallyBoundedVariationOn.exists_continuousOn_monotoneOn_sub_monotoneOn
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s) (hc : ContinuousOn f s) :
    ∃ p q : α → ℝ, ContinuousOn p s ∧ ContinuousOn q s ∧
      MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q ∧
      ∀ x ∈ s, ∀ y ∈ s, (p y - p x) + (q y - q x) = variationOnFromTo f s x y := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨f, 0, continuousOn_empty _, continuousOn_empty _,
      subsingleton_empty.monotoneOn _, subsingleton_empty.monotoneOn _,
      (sub_zero f).symm, by simp⟩
  obtain ⟨p, q, hp, hq, heq, hvar⟩ := hf.exists_monotoneOn_sub_monotoneOn'
  have hv : ContinuousOn (variationOnFromTo f s a) s :=
    fun x hx ↦ (hf.continuousWithinAt_variationOnFromTo_iff ha hx).mpr (hc x hx)
  have hpc : ContinuousOn p s := by
    apply ((((hv.add hc).add (continuousOn_const (c := p a))).add
        (continuousOn_const (c := q a))).div_const 2).congr
    intro y hy
    have hvy := hvar a ha y hy
    have hfy : f y = p y - q y := congrFun heq y
    simp only [Pi.add_apply]
    linarith
  refine ⟨p, q, hpc, ?_, hp, hq, heq, hvar⟩
  apply (hpc.sub hc).congr
  intro y _
  have hfy : f y = p y - q y := congrFun heq y
  simp only [Pi.sub_apply]
  linarith

namespace TauCeti

/-- On a subset of an ordered topological domain, continuous locally bounded-variation real
functions are exactly differences of continuous nondecreasing functions on that subset.
In particular, on all of `ℝ` local bounded variation is the two-sided condition on every
compact interval. -/
theorem continuousOn_and_locallyBoundedVariationOn_iff
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {f : α → ℝ} {s : Set α} :
    (ContinuousOn f s ∧ LocallyBoundedVariationOn f s) ↔
      ∃ p q : α → ℝ, ContinuousOn p s ∧ ContinuousOn q s ∧
        MonotoneOn p s ∧ MonotoneOn q s ∧ EqOn f (p - q) s := by
  constructor
  · rintro ⟨hc, hf⟩
    obtain ⟨p, q, hp, hq, hpm, hqm, heq, _⟩ :=
      hf.exists_continuousOn_monotoneOn_sub_monotoneOn hc
    exact ⟨p, q, hp, hq, hpm, hqm, fun y _ ↦ congrFun heq y⟩
  · rintro ⟨p, q, hp, hq, hpm, hqm, heq⟩
    refine ⟨(hp.sub hq).congr heq, ?_⟩
    intro a b ha hb
    change eVariationOn f (s ∩ Icc a b) ≠ ⊤
    rw [eVariationOn.congr (heq.mono inter_subset_left)]
    exact (hpm.locallyBoundedVariationOn.sub hqm.locallyBoundedVariationOn) a b ha hb

end TauCeti
