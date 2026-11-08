/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous extension from a closed interval

A function continuous on a nonempty closed interval `[a, b]` of a linear order with the order
topology agrees on `[a, b]` with a continuous function on the whole space: extend it by its
endpoint values with `Set.IccExtend`.

## Main results

* `ContinuousOn.exists_continuous_eqOn_Icc`: a function continuous on `[a, b]`, with `a ≤ b`,
  agrees on `[a, b]` with a continuous function.
-/

public section

open Set Filter
open scoped Topology

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [TopologicalSpace β] {a b : α} {f : α → β}

/-- A function continuous on a nonempty closed interval `[a, b]` agrees there with a continuous
function, namely its extension `Set.IccExtend` by the endpoint values. -/
theorem ContinuousOn.exists_continuous_eqOn_Icc (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) :
    ∃ g : α → β, Continuous g ∧ EqOn g f (Icc a b) :=
  ⟨IccExtend hab ((Icc a b).domRestrict f), hf.domRestrict.Icc_extend',
    fun _ hx ↦ IccExtend_of_mem _ _ hx⟩

/-- Constant extension is right-continuous wherever the original function is right-continuous
within the interval. Outside `[a,b)` no continuity assumption is needed. -/
theorem TauCeti.continuousWithinAt_IccExtend_Ici (hab : a ≤ b) {x : α}
    (hfr : x ∈ Ico a b → ContinuousWithinAt f (Icc x b) x) :
    ContinuousWithinAt (IccExtend hab (f ∘ Subtype.val)) (Ici x) x := by
  by_cases hxb : b ≤ x
  · have heq : EqOn (IccExtend hab (f ∘ Subtype.val)) (fun _ ↦ f b) (Ici x) := by
      intro y hy
      simp [IccExtend_of_right_le hab _ (hxb.trans hy)]
    exact continuousWithinAt_const.congr_of_mem heq (self_mem_Ici)
  · have hxb : x < b := lt_of_not_ge hxb
    by_cases hxa : x < a
    · have heq : IccExtend hab (f ∘ Subtype.val) =ᶠ[𝓝 x] fun _ ↦ f a := by
        filter_upwards [Iio_mem_nhds hxa] with y hy
        simp [IccExtend_of_le_left hab _ hy.le]
      exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt
    · have hax : a ≤ x := le_of_not_gt hxa
      have hproj : (projIcc a b hab x : α) = x := by
        simp [projIcc_of_mem hab ⟨hax, hxb.le⟩]
      have hc : Continuous (fun y : α ↦ (projIcc a b hab y : α)) :=
        continuous_subtype_val.comp continuous_projIcc
      exact (hfr ⟨hax, hxb⟩).comp_of_eq hc.continuousAt.continuousWithinAt
        (fun y hy ↦ ⟨by simpa only [coe_projIcc] using
          (le_max_of_le_right (le_min hxb.le hy) : x ≤ max a (min b y)),
          (projIcc a b hab y).property.2⟩) hproj
