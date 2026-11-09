/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.IsLUB

/-!
# Limits of total variation bounds

This file transfers eventual upper bounds on the total variations of a family of maps to a
`liminf` bound on the total variation of a pointwise limit. It also computes the variation of a
composition with an antitone map on an interval, and shows that the variation is unchanged by
postcomposition with a map that preserves the distances between the values of the function.
Total variation on continuous maps is lower semicontinuous for the compact-open topology,
allowing measurable path-space applications. Total variation is also the supremum over finite
subsets, and nested finite subsets can recover it while containing prescribed finite sets.
The selection uses `IsLUB.exists_seq_monotone_tendsto` and `eVariationOn.mono`.

## Main results

* `ContinuousMap.lowerSemicontinuous_eVariationOn`: lower semicontinuity on continuous path space.
* `eVariationOn.eq_iSup_finset`: total variation as the supremum over finite subsets.
* `eVariationOn.exists_monotone_finset_tendsto`: nested finite subsets recovering total variation
  and containing any prescribed sequence of finite subsets.
* `TauCeti.eVariationOn_le_liminf_of_eventually_le`: an eventual bound on the total variations of
  a family of maps bounds the total variation of a pointwise limit by the `liminf` of the bounds.
* `eVariationOn.comp_inter_Icc_eq_of_antitoneOn`: the antitone counterpart of Mathlib's
  `eVariationOn.comp_inter_Icc_eq_of_monotoneOn`.
* `eVariationOn.comp_eq_of_edist_eq`: postcomposition with a map preserving the distances between
  the values of a function does not change its variation.
-/

public section

/-- Total variation is lower semicontinuous on continuous paths with the compact-open topology.
The variation is allowed to be infinite. -/
theorem ContinuousMap.lowerSemicontinuous_eVariationOn
    {α E : Type*} [LinearOrder α] [TopologicalSpace α] [PseudoEMetricSpace E] (s : Set α) :
    LowerSemicontinuous (fun f : C(α, E) => eVariationOn f s) := by
  intro f v hv
  exact eVariationOn.lowerSemicontinuous_aux
    (fun x _ => (continuous_eval_const x).continuousAt) hv

open Filter Set Topology
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

/-- Total variation is the supremum of the variation sums over finite subsets. -/
theorem eq_iSup_finset (f : α → E) (s : Set α) :
    eVariationOn f s =
      ⨆ p : {p : Finset α // (p : Set α) ⊆ s}, eVariationOn f (p : Set α) := by
  classical
  apply le_antisymm
  · refine iSup_le ?_
    rintro ⟨n, u, hu, hus⟩
    let p := (Finset.range (n + 1)).image u
    have hp : (p : Set α) ⊆ s := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hus i
    refine (sum_le_of_monotoneOn_Iic (hu.monotoneOn _) ?_).trans
      (le_iSup (fun p : {p : Finset α // (p : Set α) ⊆ s} =>
        eVariationOn f (p : Set α)) ⟨p, hp⟩)
    intro i hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  · exact iSup_le fun p => mono f p.property

/-- Finite variation sums approaching total variation can be chosen nested and containing
any prescribed sequence of finite subsets. This includes infinite total variation. -/
theorem exists_monotone_finset_tendsto (f : α → E) (s : Set α)
    (q : ℕ → Finset α) (hq : ∀ n, (q n : Set α) ⊆ s) :
    ∃ p : ℕ → Finset α, Monotone p ∧ (∀ n, (p n : Set α) ⊆ s) ∧
      (∀ n, q n ⊆ p n) ∧
      Tendsto (fun n => eVariationOn f (p n : Set α)) atTop (𝓝 (eVariationOn f s)) := by
  classical
  let v (p : {p : Finset α // (p : Set α) ⊆ s}) := eVariationOn f (p : Set α)
  have hsup : IsLUB (range v) (eVariationOn f s) := by
    rw [eq_iSup_finset]
    exact isLUB_iSup
  obtain ⟨w, -, -, hw, hwr⟩ := hsup.exists_seq_monotone_tendsto
    ⟨v ⟨∅, by simp⟩, mem_range_self _⟩
  choose u hu using hwr
  let p (n : ℕ) := (Finset.range (n + 1)).biUnion (fun i => (u i).val ∪ q i)
  have hsub (n) : (p n : Set α) ⊆ s := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hx
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (u i).property hi
    · exact hq i hi
  have hu_le (n) : (u n).val ⊆ p n := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨n, by simp, Finset.mem_union_left _ hx⟩
  refine ⟨p, ?_, hsub, ?_, ?_⟩
  · intro m n hmn
    exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono (by omega))
  · intro n x hx
    exact Finset.mem_biUnion.mpr ⟨n, by simp, Finset.mem_union_right _ hx⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hw tendsto_const_nhds
    · intro n
      rw [← hu n]
      exact mono f (hu_le n)
    · intro n
      exact mono f (hsub n)

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
