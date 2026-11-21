/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Images and preimages of compact sets

The preimage of a compact set under a proper map is compact
(`IsProperMap.isCompact_preimage`). This file packages that as the map
`TopologicalSpace.Compacts.comap f hf : Compacts β → Compacts α` for a proper map `f : α → β`,
monotone and functorial in `f`, preserving `⊥`, `⊔` and `⊓`. It is the operation through which
the cohomology with compact supports of a space, a colimit over its compact subsets, is
contravariant in proper maps. When the target is locally compact, the preimages of the compact
neighbourhoods of `K` are cofinal among the compact neighbourhoods of `f⁻¹(K)`
(`TopologicalSpace.Compacts.exists_comap_le_of_mem_compactNhds`). It also
records that Mathlib's image `TopologicalSpace.Compacts.map` is monotone, which makes cohomology
with compact supports covariant in open embeddings. A compact set lies in one member of a
directed open cover (`TopologicalSpace.Compacts.exists_subset_of_iSup_eq_top`). A compact set
whose interior contains `K` is a compact neighbourhood of `K`
(`TopologicalSpace.Compacts.compactNhdsOfSubsetInterior`), and open sets containing two compact sets
together contain their union (`TopologicalSpace.Compacts.coe_sup_subset_coe_sup`). In a
Hausdorff space, viewing a compact set as a closed set is monotone, and so a functor
(`TopologicalSpace.Compacts.toClosedsFunctor`). Inducing maps
also pull back compact sets contained in their range (`IsInducing.preimageCompacts`).
-/

public section

open Set

namespace TopologicalSpace.Compacts

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- The preimage of a compact set under a proper map, as a compact set. -/
protected def comap (f : α → β) (hf : IsProperMap f) (K : Compacts β) : Compacts α :=
  ⟨f ⁻¹' K, hf.isCompact_preimage K.isCompact⟩

@[simp, norm_cast]
lemma coe_comap (f : α → β) (hf : IsProperMap f) (K : Compacts β) :
    (Compacts.comap f hf K : Set α) = f ⁻¹' K :=
  (rfl)

@[simp]
lemma mem_comap {f : α → β} {hf : IsProperMap f} {K : Compacts β} {x : α} :
    x ∈ Compacts.comap f hf K ↔ f x ∈ K :=
  Iff.rfl

lemma comap_mono (f : α → β) (hf : IsProperMap f) : Monotone (Compacts.comap f hf) :=
  fun _ _ h ↦ preimage_mono h

@[simp]
lemma comap_id (K : Compacts α) : Compacts.comap id isProperMap_id K = K :=
  (rfl)

lemma comap_comp (f : α → β) (g : β → γ) (hf : IsProperMap f) (hg : IsProperMap g)
    (K : Compacts γ) :
    Compacts.comap (g ∘ f) (hg.comp hf) K = Compacts.comap f hf (Compacts.comap g hg K) :=
  (rfl)

@[simp]
lemma comap_bot (f : α → β) (hf : IsProperMap f) : Compacts.comap f hf ⊥ = ⊥ :=
  Compacts.ext preimage_empty

@[simp]
lemma comap_sup (f : α → β) (hf : IsProperMap f) (K L : Compacts β) :
    Compacts.comap f hf (K ⊔ L) = Compacts.comap f hf K ⊔ Compacts.comap f hf L :=
  Compacts.ext preimage_union

@[simp]
lemma comap_inf [T2Space α] [T2Space β] (f : α → β) (hf : IsProperMap f) (K L : Compacts β) :
    Compacts.comap f hf (K ⊓ L) = Compacts.comap f hf K ⊓ Compacts.comap f hf L :=
  Compacts.ext preimage_inter

/-- The preimage of a compact neighbourhood of `K` under a proper map is a compact neighbourhood
of the preimage of `K`. -/
lemma comap_mem_compactNhds (f : α → β) (hf : IsProperMap f) {K L : Compacts β}
    (hL : L ∈ K.compactNhds) : Compacts.comap f hf L ∈ (Compacts.comap f hf K).compactNhds :=
  fun x ↦ hf.continuous.continuousAt.preimage_mem_nhds (hL ⟨f x, x.property⟩)

/-- For a proper map `f` into a locally compact space, the preimages of the compact
neighbourhoods of `K` are cofinal among the compact neighbourhoods of `f⁻¹(K)`: every compact
neighbourhood of `f⁻¹(K)` contains the preimage of a compact neighbourhood of `K`. -/
lemma exists_comap_le_of_mem_compactNhds [LocallyCompactSpace β] (f : α → β)
    (hf : IsProperMap f) {K : Compacts β} {L' : Compacts α}
    (hL' : L' ∈ (Compacts.comap f hf K).compactNhds) :
    ∃ L ∈ K.compactNhds, Compacts.comap f hf L ≤ L' := by
  obtain ⟨U, hKU, hUL'⟩ := exists_open_set_nhds_of_mem_compactsNhds hL'
  have hK : (K : Set β) ⊆ (f '' (U : Set α)ᶜ)ᶜ := by
    rintro _ hy ⟨x, hx, rfl⟩
    exact hx (hKU hy)
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between K.isCompact
    (hf.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl hK
  refine ⟨⟨L, hL⟩, fun y ↦ mem_interior_iff_mem_nhds.mp (hKL y.property), fun x hx ↦ hUL' ?_⟩
  by_contra hxU
  exact hLU hx ⟨x, hxU, rfl⟩

/-- The image of compact sets under a continuous map is monotone. -/
lemma map_mono (f : α → β) (hf : Continuous f) : Monotone (Compacts.map f hf) :=
  fun _ _ h ↦ image_mono h

/-- A compact set lies in one member of a directed family of open sets covering the space. -/
lemma exists_subset_of_iSup_eq_top {ι : Type*} [Nonempty ι] {U : ι → Opens α}
    (hU : Directed (· ≤ ·) U) (hcover : ⨆ i, U i = ⊤) (K : Compacts α) :
    ∃ i, (K : Set α) ⊆ U i :=
  K.isCompact.elim_directed_cover (fun i ↦ (U i : Set α)) (fun i ↦ (U i).isOpen)
    (fun x _ ↦ by simp [← Opens.coe_iSup, hcover]) (hU.mono_comp _ fun _ _ h ↦ h)

/-- A compact set `L` whose interior contains `K`, as a compact neighbourhood of `K`. The body is
exposed, as for Mathlib's `compactNhdsMkOfOpens`, so that the underlying compact set is `L` by
definition. -/
@[expose] def compactNhdsOfSubsetInterior {K : Compacts α} (L : Compacts α)
    (h : (K : Set α) ⊆ interior L) : K.compactNhds :=
  compactNhdsMkOfOpens L ⟨interior L, isOpen_interior⟩ h interior_subset

@[simp]
lemma coe_compactNhdsOfSubsetInterior {K : Compacts α} (L : Compacts α)
    (h : (K : Set α) ⊆ interior L) : (compactNhdsOfSubsetInterior L h : Compacts α) = L :=
  (rfl)

/-- An open set containing `K` and an open set containing `L` together contain `K ⊔ L`. -/
lemma coe_sup_subset_coe_sup {K L : Compacts α} {U V : Opens α} (hK : (K : Set α) ⊆ U)
    (hL : (L : Set α) ⊆ V) : ((K ⊔ L : Compacts α) : Set α) ⊆ (U ⊔ V : Opens α) := by
  rw [coe_sup, Opens.coe_sup]
  exact union_subset_union hK hL

lemma toCloseds_mono [T2Space α] : Monotone (Compacts.toCloseds (α := α)) :=
  fun _ _ h ↦ h

@[simp]
lemma toCloseds_top [T2Space α] [CompactSpace α] : (⊤ : Compacts α).toCloseds = ⊤ :=
  Closeds.ext (by simp)

open CategoryTheory in
variable (α) in
/-- A compact subset of a Hausdorff space as a closed subset, functorially for inclusions. -/
abbrev toClosedsFunctor [T2Space α] : Compacts α ⥤ Closeds α :=
  toCloseds_mono.functor

end TopologicalSpace.Compacts

namespace Topology.IsInducing

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

/-- The compact preimage of a compact set contained in the range of an inducing map.
Its carrier is definitionally the preimage, as for `Compacts.compactNhdsOfSubsetInterior`. -/
@[expose, simps] def preimageCompacts (hf : IsInducing f) {S : Set β} (hS : IsCompact S)
    (hSf : S ⊆ Set.range f) : TopologicalSpace.Compacts α :=
  ⟨f ⁻¹' S, hf.isCompact_preimage' hS hSf⟩

lemma subset_map_preimageCompacts (hf : IsInducing f) {S : Set β} (hS : IsCompact S)
    (hSf : S ⊆ Set.range f) :
    S ⊆ ((hf.preimageCompacts hS hSf).map f hf.continuous : Set β) :=
  (Set.image_preimage_eq_of_subset hSf).ge

end Topology.IsInducing
