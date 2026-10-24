/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Limits of total variation bounds

This file transfers eventual upper bounds on the total variations of a family of maps to a
`liminf` bound on the total variation of a pointwise limit. It also computes the variation of a
composition with an antitone map on an interval.

## Main results

* `TauCeti.eVariationOn_le_liminf_of_eventually_le`: an eventual bound on the total variations of
  a family of maps bounds the total variation of a pointwise limit by the `liminf` of the bounds.
* `eVariationOn.comp_inter_Icc_eq_of_antitoneOn`: the antitone counterpart of Mathlib's
  `eVariationOn.comp_inter_Icc_eq_of_monotoneOn`.
-/

public section

open Filter Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [LinearOrder α] {X : Type*}

section WeakPseudoEMetricSpace

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X]

/-- The metric variation of a path in a subtype is unchanged by applying its coercion. -/
@[simp] theorem eVariationOn_subtypeVal_comp {s : Set X} {f : α → s} {t : Set α} :
    eVariationOn f t = eVariationOn ((Subtype.val : s → X) ∘ f) t := by
  rfl

end WeakPseudoEMetricSpace

variable [PseudoEMetricSpace X]

/-- If the total variations of the maps `F i` on `s` are eventually bounded by `u i`, then the
total variation on `s` of a pointwise limit of the `F i` is at most `liminf u`. -/
theorem eVariationOn_le_liminf_of_eventually_le {ι : Type*} {l : Filter ι} {s : Set α}
    {f : α → X} {F : ι → α → X} {u : ι → ℝ≥0∞}
    (hu : ∀ᶠ i in l, eVariationOn (F i) s ≤ u i)
    (hf : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (nhds (f x))) :
    eVariationOn f s ≤ liminf u l := by
  rw [le_liminf_iff]
  intro v hv
  filter_upwards [eVariationOn.lowerSemicontinuous_aux hf hv, hu] with i hi hui
  exact hi.trans_le hui

end TauCeti

namespace eVariationOn

variable {α β E : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace E]
  [WeakPseudoEMetricSpace E]

/-- The variation of `f ∘ φ` on `t ∩ [x, y]` for an antitone `φ` is the variation of `f` on the
corresponding reversed interval of `φ '' t`. -/
theorem comp_inter_Icc_eq_of_antitoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t)
    {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    eVariationOn (f ∘ φ) (t ∩ Icc x y) = eVariationOn f (φ '' t ∩ Icc (φ y) (φ x)) := by
  rcases le_total x y with (h | h)
  · convert comp_eq_of_antitoneOn f φ (hφ.mono inter_subset_left)
    apply le_antisymm
    · rintro _ ⟨⟨u, us, rfl⟩, vφy, vφx⟩
      rcases le_total x u with (xu | ux)
      · rcases le_total u y with (uy | yu)
        · exact ⟨u, ⟨us, ⟨xu, uy⟩⟩, rfl⟩
        · rw [le_antisymm (hφ hy us yu) vφy]
          exact ⟨y, ⟨hy, ⟨h, le_rfl⟩⟩, rfl⟩
      · rw [le_antisymm vφx (hφ us hx ux)]
        exact ⟨x, ⟨hx, ⟨le_rfl, h⟩⟩, rfl⟩
    · rintro _ ⟨u, ⟨⟨hu, xu, uy⟩, rfl⟩⟩
      exact ⟨⟨u, hu, rfl⟩, ⟨hφ hu hy uy, hφ hx hu xu⟩⟩
  · rw [eVariationOn.subsingleton, eVariationOn.subsingleton]
    exacts [(subsingleton_Icc_of_ge (hφ hy hx h)).anti inter_subset_right,
      (subsingleton_Icc_of_ge h).anti inter_subset_right]

end eVariationOn
