/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Topology.LocallyClosed
import TauCeti.Order.Partition.Finpartition

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
  `FiniteStratification.existsUnique_mem` (every point lies in exactly one stratum).
* `FiniteStratification.ofErase`: the stratification given by a finite family of pairwise disjoint
  locally closed sets covering `X`, with the empty set discarded.
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

@[simp]
lemma toFinpartition_inj {S T : FiniteStratification X} :
    S.toFinpartition = T.toFinpartition ↔ S = T :=
  toFinpartition_injective.eq_iff

@[ext]
lemma ext {S T : FiniteStratification X} (h : S.parts = T.parts) : S = T :=
  toFinpartition_injective (Finpartition.ext h)

variable (S T : FiniteStratification X)

@[simp, grind .]
lemma empty_notMem_parts : ∅ ∉ S.parts :=
  S.bot_notMem

@[grind →]
lemma nonempty_of_mem_parts {s : Set X} (hs : s ∈ S.parts) : s.Nonempty :=
  S.toFinpartition.nonempty_of_mem_parts_set hs

/-- The strata cover the whole space. -/
lemma sUnion_parts : ⋃₀ (S.parts : Set (Set X)) = univ :=
  S.toFinpartition.sUnion_parts

/-- Every point lies in some stratum. -/
lemma exists_mem (x : X) : ∃ s ∈ S.parts, x ∈ s :=
  S.toFinpartition.exists_mem_set (mem_univ x)

/-- Two strata containing a common point are equal. -/
@[grind →]
lemma eq_of_mem_parts {s t : Set X} (hs : s ∈ S.parts) (ht : t ∈ S.parts) {x : X} (hxs : x ∈ s)
    (hxt : x ∈ t) : s = t :=
  S.toFinpartition.eq_of_mem_parts_set hs ht hxs hxt

/-- Every point lies in exactly one stratum. -/
lemma existsUnique_mem (x : X) : ∃! s, s ∈ S.parts ∧ x ∈ s :=
  S.toFinpartition.existsUnique_mem_set (mem_univ x)

/-- Refinement: `S ≤ T` when every stratum of `S` lies in some stratum of `T`. -/
instance : PartialOrder (FiniteStratification X) :=
  PartialOrder.lift toFinpartition toFinpartition_injective

variable {S T}

@[simp]
lemma toFinpartition_le_toFinpartition : S.toFinpartition ≤ T.toFinpartition ↔ S ≤ T :=
  Iff.rfl

@[simp]
lemma toFinpartition_lt_toFinpartition : S.toFinpartition < T.toFinpartition ↔ S < T :=
  Iff.rfl

lemma le_def : S ≤ T ↔ ∀ s ∈ S.parts, ∃ t ∈ T.parts, s ⊆ t :=
  Iff.rfl

/-- If `S` refines `T`, each stratum of `T` is the union of the strata of `S` inside it. -/
lemma eq_sUnion_of_le (hST : S ≤ T) {t : Set X} (ht : t ∈ T.parts) :
    t = ⋃₀ {s ∈ (S.parts : Set (Set X)) | s ⊆ t} :=
  Finpartition.eq_sUnion_of_le (toFinpartition_le_toFinpartition.2 hST) ht

open Classical in
/-- The stratification with the single stratum `X` (no strata when `X` is empty). -/
noncomputable instance : OrderTop (FiniteStratification X) where
  top :=
    { toFinpartition := ⊤
      isLocallyClosed s hs := by
        rw [Finset.mem_singleton.1 (Finpartition.parts_top_subset _ hs)]
        exact isClosed_univ.isLocallyClosed }
  le_top S := le_top (a := S.toFinpartition)

lemma toFinpartition_top [h : Decidable ((univ : Set X) = ⊥)] :
    (⊤ : FiniteStratification X).toFinpartition = ⊤ := by
  obtain rfl : h = Classical.propDecidable _ := Subsingleton.elim _ _
  rfl

@[simp, grind =]
lemma mem_top_parts {s : Set X} :
    s ∈ (⊤ : FiniteStratification X).parts ↔ Nonempty X ∧ s = univ := by
  classical
  refine ⟨fun hs ↦ ⟨(nonempty_of_mem_parts _ hs).to_type,
    Finset.mem_singleton.1 (Finpartition.parts_top_subset _ hs)⟩, ?_⟩
  rintro ⟨⟨x⟩, rfl⟩
  obtain ⟨t, ht, -⟩ := (⊤ : FiniteStratification X).exists_mem x
  obtain rfl := Finset.mem_singleton.1 (Finpartition.parts_top_subset _ ht)
  exact ht

@[simp]
lemma parts_top [h : Nonempty X] : (⊤ : FiniteStratification X).parts = {univ} := by
  ext s
  rw [mem_top_parts, Finset.mem_singleton, and_iff_right h]

noncomputable instance : Inhabited (FiniteStratification X) :=
  ⟨⊤⟩

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

lemma toFinpartition_inf [h : DecidableEq (Set X)] (S T : FiniteStratification X) :
    (S ⊓ T).toFinpartition = S.toFinpartition ⊓ T.toFinpartition := by
  obtain rfl : h = fun s t ↦ Classical.propDecidable (s = t) := Subsingleton.elim _ _
  rfl

@[simp, grind =]
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
/-- The stratification whose strata are the nonempty members of a finite family of pairwise
disjoint locally closed sets covering `X`. -/
noncomputable def ofErase (parts : Finset (Set X))
    (disjoint : (parts : Set (Set X)).PairwiseDisjoint id)
    (sUnion_parts : ⋃₀ (parts : Set (Set X)) = univ)
    (isLocallyClosed : ∀ s ∈ parts, IsLocallyClosed s) : FiniteStratification X where
  toFinpartition := Finpartition.ofErase parts disjoint.supIndep
    ((Finset.sup_id_set_eq_sUnion parts).trans sUnion_parts)
  isLocallyClosed s hs := isLocallyClosed s (Finset.mem_of_mem_erase hs)

@[simp, grind =]
lemma mem_ofErase_parts {parts : Finset (Set X)}
    {disjoint : (parts : Set (Set X)).PairwiseDisjoint id}
    {sUnion_parts : ⋃₀ (parts : Set (Set X)) = univ}
    {isLocallyClosed : ∀ s ∈ parts, IsLocallyClosed s} {s : Set X} :
    s ∈ (ofErase parts disjoint sUnion_parts isLocallyClosed).parts ↔ s.Nonempty ∧ s ∈ parts := by
  classical
  simp [ofErase, nonempty_iff_ne_empty]

/-- The pullback of a stratification along a continuous map: its strata are the nonempty
preimages of the strata. -/
noncomputable def comap (f : Y → X) (hf : Continuous f) (S : FiniteStratification X) :
    FiniteStratification Y :=
  ofErase (S.parts.image (f ⁻¹' ·))
    (by
      rintro _ hu _ hu' huu'
      obtain ⟨s, hs, rfl⟩ := Finset.mem_coe.1 hu |> Finset.mem_image.1
      obtain ⟨s', hs', rfl⟩ := Finset.mem_coe.1 hu' |> Finset.mem_image.1
      refine Set.disjoint_left.2 fun y hy hy' ↦ huu' ?_
      rw [S.eq_of_mem_parts hs hs' hy hy'])
    (by
      refine eq_univ_of_forall fun y ↦ ?_
      obtain ⟨s, hs, hys⟩ := S.exists_mem (f y)
      simp only [Finset.coe_image, sUnion_image, mem_iUnion]
      exact ⟨s, hs, hys⟩)
    (by
      simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun s hs ↦ (S.isLocallyClosed s hs).preimage hf)

@[simp, grind =]
lemma mem_comap_parts {f : Y → X} {hf : Continuous f} {u : Set Y} :
    u ∈ (S.comap f hf).parts ↔ u.Nonempty ∧ ∃ s ∈ S.parts, f ⁻¹' s = u :=
  mem_ofErase_parts.trans (and_congr_right' Finset.mem_image)

/-- Pullback preserves refinement. -/
@[gcongr]
lemma comap_mono (hST : S ≤ T) (f : Y → X) (hf : Continuous f) :
    S.comap f hf ≤ T.comap f hf := le_def.2 fun u hu ↦ by
  obtain ⟨hne, s, hs, rfl⟩ := mem_comap_parts.1 hu
  obtain ⟨t, ht, hst⟩ := le_def.1 hST s hs
  exact ⟨f ⁻¹' t, mem_comap_parts.2 ⟨hne.mono (preimage_mono hst), t, ht, rfl⟩, preimage_mono hst⟩

/-- Pulling back the single-stratum stratification gives the single-stratum stratification. -/
@[simp, grind =]
lemma comap_top (f : Y → X) (hf : Continuous f) :
    (⊤ : FiniteStratification X).comap f hf = ⊤ := by
  ext u
  simp only [mem_comap_parts, mem_top_parts]
  constructor
  · rintro ⟨⟨y, -⟩, _, ⟨-, rfl⟩, rfl⟩
    exact ⟨⟨y⟩, preimage_univ⟩
  · rintro ⟨⟨y⟩, rfl⟩
    exact ⟨⟨y, mem_univ y⟩, univ, ⟨⟨f y⟩, rfl⟩, preimage_univ⟩

/-- Pullback commutes with common refinement. -/
@[grind =]
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
@[simp, grind =]
lemma comap_id (S : FiniteStratification X) : S.comap id continuous_id = S := by
  ext u
  simp only [mem_comap_parts, preimage_id_eq, id_eq, exists_eq_right]
  exact ⟨And.right, fun hu ↦ ⟨S.nonempty_of_mem_parts hu, hu⟩⟩

/-- Pulling back along the identity, written as a lambda, does nothing. -/
@[simp, grind =]
lemma comap_id' (S : FiniteStratification X) : S.comap (fun x ↦ x) continuous_id' = S :=
  S.comap_id

/-- Pullback is functorial. -/
@[grind _=_]
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
