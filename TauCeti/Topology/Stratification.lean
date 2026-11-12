/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Topology.LocallyClosed

/-!
# Finite locally closed stratifications

A finite locally closed stratification of a topological space `X` is a finite partition of `X`
into nonempty locally closed subsets, its strata. Constructible étale sheaves on a Noetherian
scheme are those whose restrictions to the strata of some such stratification are finite locally
constant (SGA 4, Exposé IX, §2; Stacks, Section 59.71), so these stratifications are the
combinatorial carrier of constructibility.

A stratification is a `Finpartition (univ : Set X)` whose parts are locally closed. Refinement,
the single-stratum stratification and common refinement are inherited from the order on
`Finpartition`: the parts of a finite partition by locally closed sets stay locally closed under
`⊓`, and the single part `univ` is closed.

## Main declarations

* `TauCeti.FiniteStratification X`: finite locally closed stratifications of `X`, with
  `FiniteStratification.exists_unique_mem` (every point lies in exactly one stratum).
* The `PartialOrder`, `OrderTop` and `SemilatticeInf` instances: `S ≤ T` when every stratum of `S`
  lies in a stratum of `T`, `⊤` has the single stratum `X` (when `X` is nonempty), and `S ⊓ T` is
  the common refinement, whose strata are the nonempty intersections of a stratum of `S` with a
  stratum of `T`.
* `FiniteStratification.comap f hf S`: the pullback along a continuous map, whose strata are the
  nonempty preimages of the strata of `S`. It is monotone and commutes with `⊤` and `⊓`.
-/

public section

open Set

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (X) in
/-- A finite locally closed stratification of a topological space: a finite partition of the
whole space into nonempty locally closed subsets, its strata (SGA 4, Exposé IX, §2). -/
structure FiniteStratification extends Finpartition (univ : Set X) where
  /-- Every stratum is locally closed. -/
  isLocallyClosed : ∀ s ∈ parts, IsLocallyClosed s

namespace FiniteStratification

lemma toFinpartition_injective :
    Function.Injective (toFinpartition : FiniteStratification X → Finpartition univ) := by
  rintro ⟨S, hS⟩ ⟨T, hT⟩ rfl
  rfl

@[ext]
lemma ext {S T : FiniteStratification X} (h : S.parts = T.parts) : S = T :=
  toFinpartition_injective (Finpartition.ext h)

variable (S T : FiniteStratification X)

/-- Every point lies in some stratum. -/
lemma exists_mem (x : X) : ∃ s ∈ S.parts, x ∈ s := by
  have hx : x ∈ S.parts.sup id := by rw [S.sup_parts]; exact mem_univ x
  simpa [Finset.sup_set_eq_biUnion] using hx

/-- Two strata containing a common point are equal. -/
lemma eq_of_mem {s t : Set X} (hs : s ∈ S.parts) (ht : t ∈ S.parts) {x : X} (hxs : x ∈ s)
    (hxt : x ∈ t) : s = t :=
  S.disjoint.elim_set hs ht x hxs hxt

/-- Every point lies in exactly one stratum. -/
lemma exists_unique_mem (x : X) : ∃! s, s ∈ S.parts ∧ x ∈ s := by
  obtain ⟨s, hs, hx⟩ := S.exists_mem x
  exact ⟨s, ⟨hs, hx⟩, fun t ⟨ht, hxt⟩ ↦ S.eq_of_mem ht hs hxt hx⟩

/-- Refinement: `S ≤ T` when every stratum of `S` lies in some stratum of `T`. -/
instance : PartialOrder (FiniteStratification X) :=
  PartialOrder.lift toFinpartition toFinpartition_injective

variable {S T}

lemma toFinpartition_le_toFinpartition : S.toFinpartition ≤ T.toFinpartition ↔ S ≤ T :=
  Iff.rfl

lemma le_def : S ≤ T ↔ ∀ s ∈ S.parts, ∃ t ∈ T.parts, s ⊆ t :=
  Iff.rfl

/-- If `S` refines `T`, each stratum of `T` is the union of the strata of `S` inside it. -/
lemma eq_sUnion_of_le (hST : S ≤ T) {t : Set X} (ht : t ∈ T.parts) :
    t = ⋃₀ {s ∈ (S.parts : Set (Set X)) | s ⊆ t} := by
  refine Subset.antisymm (fun x hxt ↦ ?_) (sUnion_subset fun s hs ↦ hs.2)
  obtain ⟨s, hs, hxs⟩ := S.exists_mem x
  obtain ⟨t', ht', hst'⟩ := le_def.1 hST s hs
  obtain rfl := T.eq_of_mem ht ht' hxt (hst' hxs)
  exact ⟨s, ⟨hs, hst'⟩, hxs⟩

open Classical in
/-- The stratification with the single stratum `X` (no strata when `X` is empty). -/
noncomputable instance : OrderTop (FiniteStratification X) where
  top :=
    { toFinpartition := ⊤
      isLocallyClosed s hs := by
        rw [Finset.mem_singleton.1 (Finpartition.parts_top_subset _ hs)]
        exact isClosed_univ.isLocallyClosed }
  le_top S := le_top (a := S.toFinpartition)

@[simp]
lemma mem_top_parts {s : Set X} :
    s ∈ (⊤ : FiniteStratification X).parts ↔ s.Nonempty ∧ s = univ := by
  classical
  refine ⟨fun hs ↦ ⟨nonempty_iff_ne_empty.2 (Finpartition.ne_bot _ hs),
    Finset.mem_singleton.1 (Finpartition.parts_top_subset _ hs)⟩, ?_⟩
  rintro ⟨⟨x, -⟩, rfl⟩
  obtain ⟨t, ht, -⟩ := (⊤ : FiniteStratification X).exists_mem x
  obtain rfl := Finset.mem_singleton.1 (Finpartition.parts_top_subset _ ht)
  exact ht

open Classical in
/-- The common refinement of two stratifications: its strata are the nonempty intersections of a
stratum of `S` with a stratum of `T`. -/
noncomputable instance : Min (FiniteStratification X) where
  min S T :=
    { toFinpartition := S.toFinpartition ⊓ T.toFinpartition
      isLocallyClosed u hu := by
        obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hu)
        obtain ⟨hs, ht⟩ := Finset.mem_product.1 hst
        exact (S.isLocallyClosed s hs).inter (T.isLocallyClosed t ht) }

open Classical in
lemma toFinpartition_inf (S T : FiniteStratification X) :
    (S ⊓ T).toFinpartition = S.toFinpartition ⊓ T.toFinpartition :=
  rfl

@[simp]
lemma mem_inf_parts {u : Set X} :
    u ∈ (S ⊓ T).parts ↔ u.Nonempty ∧ ∃ s ∈ S.parts, ∃ t ∈ T.parts, s ∩ t = u := by
  classical
  rw [toFinpartition_inf, Finpartition.parts_inf, Finset.mem_erase, Finset.mem_image,
    ← nonempty_iff_ne_empty.symm.eq]
  simp only [Finset.mem_product, Prod.exists]
  exact and_congr_right' ⟨fun ⟨s, t, ⟨hs, ht⟩, h⟩ ↦ ⟨s, hs, t, ht, h⟩,
    fun ⟨s, hs, t, ht, h⟩ ↦ ⟨s, t, ⟨hs, ht⟩, h⟩⟩

/-- Common refinement is the meet for refinement. -/
noncomputable instance : SemilatticeInf (FiniteStratification X) where
  inf := min
  inf_le_left S T := inf_le_left (a := S.toFinpartition) (b := T.toFinpartition)
  inf_le_right S T := inf_le_right (a := S.toFinpartition) (b := T.toFinpartition)
  le_inf _ _ _ := le_inf (α := Finpartition (univ : Set X))

open Classical in
/-- The pullback of a stratification along a continuous map: its strata are the nonempty
preimages of the strata. -/
noncomputable def comap (f : Y → X) (hf : Continuous f) (S : FiniteStratification X) :
    FiniteStratification Y where
  toFinpartition := Finpartition.ofErase (S.parts.image (f ⁻¹' ·))
    (Finset.supIndep_iff_pairwiseDisjoint.2 <| by
      rintro _ hu _ hu' huu'
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hu'
      refine Set.disjoint_left.2 fun y hy hy' ↦ huu' ?_
      rw [S.eq_of_mem hs hs' hy hy'])
    (by
      refine eq_univ_of_forall fun y ↦ ?_
      obtain ⟨s, hs, hys⟩ := S.exists_mem (f y)
      simp only [Finset.sup_set_eq_biUnion, Finset.mem_image, mem_iUnion]
      exact ⟨f ⁻¹' s, ⟨s, hs, rfl⟩, hys⟩)
  isLocallyClosed u hu := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hu)
    exact (S.isLocallyClosed s hs).preimage hf

@[simp]
lemma mem_comap_parts {f : Y → X} {hf : Continuous f} {u : Set Y} :
    u ∈ (S.comap f hf).parts ↔ u.Nonempty ∧ ∃ s ∈ S.parts, f ⁻¹' s = u := by
  classical
  simp [comap, nonempty_iff_ne_empty]

/-- Pullback preserves refinement. -/
@[gcongr]
lemma comap_mono (hST : S ≤ T) (f : Y → X) (hf : Continuous f) :
    S.comap f hf ≤ T.comap f hf := le_def.2 fun u hu ↦ by
  obtain ⟨hne, s, hs, rfl⟩ := mem_comap_parts.1 hu
  obtain ⟨t, ht, hst⟩ := le_def.1 hST s hs
  exact ⟨f ⁻¹' t, mem_comap_parts.2 ⟨hne.mono (preimage_mono hst), t, ht, rfl⟩, preimage_mono hst⟩

/-- Pulling back the single-stratum stratification gives the single-stratum stratification. -/
@[simp]
lemma comap_top (f : Y → X) (hf : Continuous f) :
    (⊤ : FiniteStratification X).comap f hf = ⊤ := by
  ext u
  simp only [mem_comap_parts, mem_top_parts]
  constructor
  · rintro ⟨hne, _, ⟨-, rfl⟩, rfl⟩
    exact ⟨hne, preimage_univ⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨⟨y, hy⟩, univ, ⟨⟨f y, mem_univ _⟩, rfl⟩, preimage_univ⟩

/-- Pullback commutes with common refinement. -/
lemma comap_inf (f : Y → X) (hf : Continuous f) (S T : FiniteStratification X) :
    (S ⊓ T).comap f hf = S.comap f hf ⊓ T.comap f hf := by
  ext u
  simp only [mem_comap_parts, mem_inf_parts]
  constructor
  · rintro ⟨hne, _, ⟨-, s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨hne, f ⁻¹' s, ⟨hne.mono (preimage_mono inter_subset_left), s, hs, rfl⟩, f ⁻¹' t,
      ⟨hne.mono (preimage_mono inter_subset_right), t, ht, rfl⟩, rfl⟩
  · rintro ⟨hne, _, ⟨-, s, hs, rfl⟩, _, ⟨-, t, ht, rfl⟩, rfl⟩
    exact ⟨hne, s ∩ t, ⟨(hne.image f).mono (image_preimage_subset f _), s, hs, t, ht, rfl⟩, rfl⟩

/-- Pulling back along the identity does nothing. -/
@[simp]
lemma comap_id (S : FiniteStratification X) : S.comap id continuous_id = S := by
  ext u
  simp only [mem_comap_parts, preimage_id_eq, id_eq, exists_eq_right]
  exact ⟨And.right, fun hu ↦ ⟨nonempty_iff_ne_empty.2 (S.ne_bot hu), hu⟩⟩

/-- Pullback is functorial. -/
lemma comap_comp (g : Z → Y) (hg : Continuous g) (f : Y → X) (hf : Continuous f)
    (S : FiniteStratification X) :
    S.comap (f ∘ g) (hf.comp hg) = (S.comap f hf).comap g hg := by
  ext u
  simp only [mem_comap_parts]
  constructor
  · rintro ⟨hne, s, hs, rfl⟩
    exact ⟨hne, f ⁻¹' s, ⟨(hne.image g).mono (image_preimage_subset g _), s, hs, rfl⟩, rfl⟩
  · rintro ⟨hne, _, ⟨-, s, hs, rfl⟩, rfl⟩
    exact ⟨hne, s, hs, rfl⟩

end FiniteStratification

end TauCeti
