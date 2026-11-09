/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Limits of total variation bounds

This file transfers eventual upper bounds on the total variations of a family of maps to a
`liminf` bound on the total variation of a pointwise limit. It also computes the variation of a
composition with an antitone map on an interval, proves stability of bounded variation under
subtraction, and shows that the variation is unchanged by postcomposition with a map that
preserves the distances between the values of the function.

## Main results

* `TauCeti.eVariationOn_le_liminf_of_eventually_le`: an eventual bound on the total variations of
  a family of maps bounds the total variation of a pointwise limit by the `liminf` of the bounds.
* `eVariationOn.comp_inter_Icc_eq_of_antitoneOn`: the antitone counterpart of Mathlib's
  `eVariationOn.comp_inter_Icc_eq_of_monotoneOn`.
* `eVariationOn.comp_eq_of_edist_eq`: postcomposition with a map preserving the distances between
  the values of a function does not change its variation.
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

/-- Postcomposing `f` with a map `g` that preserves the distances between the values of `f` on `s`
does not change the variation of `f` on `s`. -/
theorem comp_eq_of_edist_eq {F : Type*} [TopologicalSpace F] [WeakPseudoEMetricSpace F]
    {f : α → E} {g : E → F} {s : Set α}
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (g (f x)) (g (f y)) = edist (f x) (f y)) :
    eVariationOn (g ∘ f) s = eVariationOn f s := by
  refine iSup_congr fun p ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  exact h _ (p.2.2.2 _) _ (p.2.2.2 _)

open OrderDual in
/-- The variation of `f ∘ φ` on `t ∩ [x, y]` for an antitone `φ` is the variation of `f` on the
corresponding reversed interval of `φ '' t`. -/
theorem comp_inter_Icc_eq_of_antitoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t)
    {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    eVariationOn (f ∘ φ) (t ∩ Icc x y) = eVariationOn f (φ '' t ∩ Icc (φ y) (φ x)) := by
  have := comp_inter_Icc_eq_of_monotoneOn (f ∘ ofDual) (toDual ∘ φ) hφ.dual_right hx hy
  rwa [Function.comp_apply, Function.comp_apply, Icc_toDual, image_comp,
    Equiv.image_eq_preimage_symm, toDual_symm_eq, ← preimage_inter, comp_ofDual] at this

end eVariationOn

section Subtraction

variable {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]
  {f g : α → E} {s : Set α}

/-- The variation of a difference is at most the sum of the variations. -/
theorem eVariationOn.sub_le :
    eVariationOn (f - g) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [Pi.sub_apply, sub_eq_add_neg, edist_neg_neg] using
        edist_add_add_le (f (u (i + 1))) (-g (u (i + 1))) (f (u i)) (-g (u i))
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- The difference of two bounded-variation functions has bounded variation. -/
theorem BoundedVariationOn.sub (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f - g) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) eVariationOn.sub_le

/-- Local bounded variation is stable under subtraction. -/
theorem LocallyBoundedVariationOn.sub
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f - g) s :=
  fun a b ha hb ↦ (hf a b ha hb).sub (hg a b ha hb)

end Subtraction
