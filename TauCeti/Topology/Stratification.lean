/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.NAry
public import Mathlib.Topology.LocallyClosed

/-!
# Finite locally closed stratifications

A finite locally closed stratification of a topological space `X` is a finite set of pairwise
disjoint locally closed subsets of `X`, its strata, whose union is `X`. Constructible étale
sheaves on a Noetherian scheme are those whose restrictions to the strata of some such
stratification are finite locally constant (SGA 4, Exposé IX, §2; Stacks, Section 59.71), so
these stratifications are the combinatorial carrier of constructibility.

## Main declarations

* `FiniteStratification X`: finite locally closed stratifications of `X`, with
  `FiniteStratification.exists_unique_mem` (every point lies in exactly one stratum).
* `FiniteStratification.Refines S T`: every stratum of `S` lies in a stratum of `T`; a preorder.
* `FiniteStratification.top X`: the stratification with the single stratum `X`, refined by every
  stratification.
* `FiniteStratification.inf S T`: the common refinement, whose strata are the intersections of a
  stratum of `S` with a stratum of `T`. It refines both, and every common refinement of `S` and
  `T` refines it (`FiniteStratification.refines_inf_iff`).
* `FiniteStratification.comap f hf S`: the pullback along a continuous map, whose strata are the
  preimages of the strata of `S`. It is monotone for refinement and commutes with `inf`; on a
  subspace it is the restriction of the stratification.

Strata may be empty: the definitions do not require nonemptiness, so pulling back and taking
intersections need no case distinction.
-/

public section

open Set

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (X) in
/-- A finite locally closed stratification of a topological space: a finite set of pairwise
disjoint locally closed subsets, its strata, whose union is the whole space (SGA 4, Exposé IX,
§2). Strata may be empty. -/
@[ext]
structure FiniteStratification where
  /-- The strata. -/
  strata : Finset (Set X)
  /-- Every stratum is locally closed. -/
  isLocallyClosed : ∀ s ∈ strata, IsLocallyClosed s
  /-- Distinct strata are disjoint. -/
  pairwiseDisjoint : (strata : Set (Set X)).PairwiseDisjoint id
  /-- The strata cover the space. -/
  sUnion_eq : ⋃₀ (strata : Set (Set X)) = univ

namespace FiniteStratification

variable (S T U : FiniteStratification X)

/-- Every point lies in some stratum. -/
lemma exists_mem (x : X) : ∃ s ∈ S.strata, x ∈ s := by
  have hx : x ∈ ⋃₀ (S.strata : Set (Set X)) := S.sUnion_eq ▸ mem_univ x
  simpa using hx

/-- Two strata containing a common point are equal. -/
lemma eq_of_mem {s t : Set X} (hs : s ∈ S.strata) (ht : t ∈ S.strata) {x : X} (hxs : x ∈ s)
    (hxt : x ∈ t) : s = t := by
  by_contra hst
  exact Set.disjoint_left.1 (S.pairwiseDisjoint hs ht hst) hxs hxt

/-- Every point lies in exactly one stratum. -/
lemma exists_unique_mem (x : X) : ∃! s, s ∈ S.strata ∧ x ∈ s := by
  obtain ⟨s, hs, hx⟩ := S.exists_mem x
  exact ⟨s, ⟨hs, hx⟩, fun t ⟨ht, hxt⟩ ↦ S.eq_of_mem ht hs hxt hx⟩

/-- `S` refines `T` when every stratum of `S` lies in some stratum of `T`. -/
def Refines : Prop :=
  ∀ s ∈ S.strata, ∃ t ∈ T.strata, s ⊆ t

variable {S T U}

lemma Refines.refl : S.Refines S := fun s hs ↦ ⟨s, hs, subset_rfl⟩

lemma Refines.trans (hST : S.Refines T) (hTU : T.Refines U) : S.Refines U := fun s hs ↦ by
  obtain ⟨t, ht, hst⟩ := hST s hs
  obtain ⟨u, hu, htu⟩ := hTU t ht
  exact ⟨u, hu, hst.trans htu⟩

/-- If `S` refines `T`, each stratum of `T` is the union of the strata of `S` inside it. -/
lemma Refines.eq_sUnion (hST : S.Refines T) {t : Set X} (ht : t ∈ T.strata) :
    t = ⋃₀ {s ∈ (S.strata : Set (Set X)) | s ⊆ t} := by
  refine Subset.antisymm (fun x hxt ↦ ?_) (sUnion_subset fun s hs ↦ hs.2)
  obtain ⟨s, hs, hxs⟩ := S.exists_mem x
  obtain ⟨t', ht', hst'⟩ := hST s hs
  obtain rfl := T.eq_of_mem ht ht' hxt (hst' hxs)
  exact ⟨s, ⟨hs, hst'⟩, hxs⟩

variable (X) in
/-- The stratification with the single stratum `X`. -/
def top : FiniteStratification X where
  strata := {univ}
  isLocallyClosed s hs := by
    rw [Finset.mem_singleton.1 hs]
    exact isClosed_univ.isLocallyClosed
  pairwiseDisjoint := by
    simp only [Finset.coe_singleton, pairwiseDisjoint_singleton]
  sUnion_eq := by simp

@[simp]
lemma strata_top : (top X).strata = {univ} :=
  (rfl)

/-- Every stratification refines the stratification with a single stratum. -/
lemma refines_top (S : FiniteStratification X) : S.Refines (top X) :=
  fun s _ ↦ ⟨univ, Finset.mem_singleton_self _, subset_univ s⟩

open Classical in
/-- The common refinement of two stratifications: its strata are the intersections of a stratum
of `S` with a stratum of `T`. -/
noncomputable def inf (S T : FiniteStratification X) : FiniteStratification X where
  strata := Finset.image₂ (· ∩ ·) S.strata T.strata
  isLocallyClosed u hu := by
    obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_image₂.1 hu
    exact (S.isLocallyClosed s hs).inter (T.isLocallyClosed t ht)
  pairwiseDisjoint := by
    rintro _ hu _ hu' huu'
    obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_image₂.1 hu
    obtain ⟨s', hs', t', ht', rfl⟩ := Finset.mem_image₂.1 hu'
    refine Set.disjoint_left.2 fun x hx hx' ↦ huu' ?_
    rw [S.eq_of_mem hs hs' hx.1 hx'.1, T.eq_of_mem ht ht' hx.2 hx'.2]
  sUnion_eq := by
    refine eq_univ_of_forall fun x ↦ ?_
    obtain ⟨s, hs, hxs⟩ := S.exists_mem x
    obtain ⟨t, ht, hxt⟩ := T.exists_mem x
    exact ⟨s ∩ t, Finset.mem_coe.2 (Finset.mem_image₂_of_mem hs ht), hxs, hxt⟩

lemma mem_inf_strata {S T : FiniteStratification X} {u : Set X} :
    u ∈ (S.inf T).strata ↔ ∃ s ∈ S.strata, ∃ t ∈ T.strata, s ∩ t = u := by
  classical
  simp [inf, Finset.mem_image₂]

/-- The common refinement refines the first stratification. -/
lemma inf_refines_left (S T : FiniteStratification X) : (S.inf T).Refines S := fun u hu ↦ by
  obtain ⟨s, hs, t, -, rfl⟩ := mem_inf_strata.1 hu
  exact ⟨s, hs, inter_subset_left⟩

/-- The common refinement refines the second stratification. -/
lemma inf_refines_right (S T : FiniteStratification X) : (S.inf T).Refines T := fun u hu ↦ by
  obtain ⟨-, -, t, ht, rfl⟩ := mem_inf_strata.1 hu
  exact ⟨t, ht, inter_subset_right⟩

/-- A stratification refines the common refinement of `S` and `T` exactly when it refines both. -/
lemma refines_inf_iff : U.Refines (S.inf T) ↔ U.Refines S ∧ U.Refines T := by
  refine ⟨fun h ↦ ⟨h.trans (inf_refines_left S T), h.trans (inf_refines_right S T)⟩, ?_⟩
  rintro ⟨hS, hT⟩ u hu
  obtain ⟨s, hs, hus⟩ := hS u hu
  obtain ⟨t, ht, hut⟩ := hT u hu
  exact ⟨s ∩ t, mem_inf_strata.2 ⟨s, hs, t, ht, rfl⟩, subset_inter hus hut⟩

open Classical in
/-- The pullback of a stratification along a continuous map: its strata are the preimages of the
strata. For the inclusion of a subspace it is the restriction of the stratification. -/
noncomputable def comap (f : Y → X) (hf : Continuous f) (S : FiniteStratification X) :
    FiniteStratification Y where
  strata := S.strata.image (f ⁻¹' ·)
  isLocallyClosed u hu := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
    exact (S.isLocallyClosed s hs).preimage hf
  pairwiseDisjoint := by
    rintro _ hu _ hu' huu'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hu'
    refine Set.disjoint_left.2 fun y hy hy' ↦ huu' ?_
    rw [S.eq_of_mem hs hs' hy hy']
  sUnion_eq := by
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨s, hs, hys⟩ := S.exists_mem (f y)
    exact ⟨f ⁻¹' s, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hs), hys⟩

lemma mem_comap_strata {f : Y → X} {hf : Continuous f} {u : Set Y} :
    u ∈ (S.comap f hf).strata ↔ ∃ s ∈ S.strata, f ⁻¹' s = u := by
  classical
  simp [comap, Finset.mem_image]

/-- Pullback preserves refinement. -/
lemma Refines.comap (hST : S.Refines T) (f : Y → X) (hf : Continuous f) :
    (S.comap f hf).Refines (T.comap f hf) := fun u hu ↦ by
  obtain ⟨s, hs, rfl⟩ := mem_comap_strata.1 hu
  obtain ⟨t, ht, hst⟩ := hST s hs
  exact ⟨f ⁻¹' t, mem_comap_strata.2 ⟨t, ht, rfl⟩, preimage_mono hst⟩

/-- Pulling back the single-stratum stratification gives the single-stratum stratification. -/
@[simp]
lemma comap_top (f : Y → X) (hf : Continuous f) : (top X).comap f hf = top Y := by
  classical
  ext1
  simp [comap, top]

/-- Pullback commutes with common refinement. -/
lemma comap_inf (f : Y → X) (hf : Continuous f) (S T : FiniteStratification X) :
    (S.inf T).comap f hf = (S.comap f hf).inf (T.comap f hf) := by
  ext1
  ext u
  simp only [mem_comap_strata, mem_inf_strata]
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨f ⁻¹' s, ⟨s, hs, rfl⟩, f ⁻¹' t, ⟨t, ht, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨s ∩ t, ⟨s, hs, t, ht, rfl⟩, rfl⟩

/-- Pulling back along the identity does nothing. -/
@[simp]
lemma comap_id (S : FiniteStratification X) : S.comap id continuous_id = S := by
  classical
  ext1
  simp [comap]

/-- Pullback is functorial. -/
lemma comap_comp (g : Z → Y) (hg : Continuous g) (f : Y → X) (hf : Continuous f)
    (S : FiniteStratification X) :
    S.comap (f ∘ g) (hf.comp hg) = (S.comap f hf).comap g hg := by
  ext1
  ext u
  simp only [mem_comap_strata]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨f ⁻¹' s, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩

end FiniteStratification
