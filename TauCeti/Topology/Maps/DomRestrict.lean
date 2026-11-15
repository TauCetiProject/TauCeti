/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Topology.Maps.LocalSections

/-!
# Openness of domain restrictions and projections of subsets

For a map `f : X → Y` and a subset `s ⊆ X`, `IsOpenMap (s.domRestrict f)` states that restricting
`f` to `s` (with the subspace topology) yields an open map into `Y`. In particular, when `f` is a
coordinate projection such as `Prod.fst : X × Z → X` or `Fin.tail : (Fin (n + 1) → Z) → Fin n → Z`,
this is Łojasiewicz's *property (P)*: every relatively open part of `s` has open projection in the
base, and in particular `f '' s` itself is open (`h.isOpen_range` via `Set.range_domRestrict`).

Unlike openness of the single image `f '' s`, openness of `s.domRestrict f` is local on `s` and
closed under the set-theoretic operations used to assemble stratified families over a base:

* `TauCeti.isOpenMap_domRestrict_iff`: `s.domRestrict f` is open if and only if `f '' (s ∩ U)` is
  open for every ambient open set `U ⊆ X`.
* `IsOpenMap.domRestrict_inter`, `TauCeti.isOpenMap_iUnion_domRestrict`,
  `TauCeti.isOpenMap_sUnion_domRestrict`, `IsOpenMap.domRestrict_union`: stability under
  intersection with ambient open sets and under arbitrary and binary unions.
* `TauCeti.isOpenMap_domRestrict_of_local_sections`: a local-section criterion on `s`, extending
  `IsOpenMap.of_local_sections` without requiring global values of the local section to stay in `s`.
* `IsOpen.isOpenMap_graphOn_domRestrict_fst`, `IsOpen.isOpenMap_domRestrict_tail_graph`: the graph
  of a continuous function on an open base set has open projection, in both product and cylinder
  (`Fin.tail`) coordinates.
* `IsOpenMap.domRestrict_fst_preimage_prodMap_id`,
  `Homeomorph.isOpenMap_preimage_prodMap_domRestrict_fst_iff`,
  `TauCeti.isOpenMap_domRestrict_tail_preimage_iff`: base change of open first-coordinate
  projections along continuous maps of the base, invariance under product homeomorphisms, and
  comparison between `Prod.fst` and `Fin.tail`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1 (property (P)).
-/

public section

open Filter Function Set Topology

namespace TauCeti

section General

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The restriction of `f` to `s` is an open map if and only if `f '' (s ∩ U)` is open for every
open set `U ⊆ X`. -/
theorem isOpenMap_domRestrict_iff {s : Set X} {f : X → Y} :
    IsOpenMap (s.domRestrict f) ↔ ∀ U, IsOpen U → IsOpen (f '' (s ∩ U)) := by
  constructor
  · intro hf U hU
    rw [inter_comm, ← image_domRestrict]
    exact hf _ (hU.preimage continuous_subtype_val)
  · intro h V hV
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hV
    rw [image_domRestrict, inter_comm]
    exact h U hU

/-- Openness of domain restrictions is preserved under arbitrary indexed unions. -/
theorem isOpenMap_iUnion_domRestrict {ι : Sort*} {S : ι → Set X} {f : X → Y}
    (h : ∀ i, IsOpenMap ((S i).domRestrict f)) :
    IsOpenMap ((⋃ i, S i).domRestrict f) := by
  refine isOpenMap_domRestrict_iff.2 fun U hU ↦ ?_
  rw [iUnion_inter, image_iUnion]
  exact isOpen_iUnion fun i ↦ isOpenMap_domRestrict_iff.1 (h i) U hU

/-- Openness of domain restrictions is preserved under arbitrary unions of families of sets. -/
theorem isOpenMap_sUnion_domRestrict {𝒜 : Set (Set X)} {f : X → Y}
    (h : ∀ s ∈ 𝒜, IsOpenMap (s.domRestrict f)) :
    IsOpenMap ((⋃₀ 𝒜).domRestrict f) := by
  rw [sUnion_eq_biUnion]
  exact isOpenMap_iUnion_domRestrict fun s ↦ isOpenMap_iUnion_domRestrict (h s)

end General

/-- Cylinder coordinates `(Fin (n + 1) → Z) ≃ₜ (Fin n → Z) × Z` placing `Fin.tail` first and
coordinate `0` second. -/
private def tailHeadHomeomorph (n : ℕ) (Z : Type*) [TopologicalSpace Z] :
    (Fin (n + 1) → Z) ≃ₜ (Fin n → Z) × Z where
  toFun v := (Fin.tail v, v 0)
  invFun p := Fin.cons p.2 p.1
  left_inv v := Fin.cons_self_tail v
  right_inv p := by simp
  continuous_toFun := (continuous_pi fun i ↦ continuous_apply i.succ).prodMk (continuous_apply 0)
  continuous_invFun := continuous_snd.finCons (A := fun _ ↦ Z) continuous_fst

/-- Pulling back a subset of `(Fin n → Z) × Z` to `Fin (n + 1) → Z` via `v ↦ (Fin.tail v, v 0)`
turns openness of `Prod.fst` into openness of `Fin.tail`. -/
theorem isOpenMap_domRestrict_tail_preimage_iff {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    {s : Set ((Fin n → Z) × Z)} :
    IsOpenMap ({v : Fin (n + 1) → Z | (Fin.tail v, v 0) ∈ s}.domRestrict Fin.tail) ↔
      IsOpenMap (s.domRestrict Prod.fst) := by
  let e := tailHeadHomeomorph n Z
  have he_symm (p : (Fin n → Z) × Z) : e.symm p = Fin.cons p.2 p.1 := rfl
  rw [isOpenMap_domRestrict_iff, isOpenMap_domRestrict_iff]
  constructor
  · intro h U hU
    have hpre :
        Fin.tail '' ({v : Fin (n + 1) → Z | (Fin.tail v, v 0) ∈ s} ∩ e ⁻¹' U) =
          Prod.fst '' (s ∩ U) := by
      ext x
      constructor
      · rintro ⟨v, ⟨hvs, hvU⟩, rfl⟩
        exact ⟨e v, ⟨hvs, hvU⟩, rfl⟩
      · rintro ⟨⟨x, t⟩, ⟨hxs, hxU⟩, rfl⟩
        refine ⟨e.symm (x, t), ?_, by simp [he_symm]⟩
        rw [mem_inter_iff, mem_ofPred_eq, mem_preimage, e.apply_symm_apply]
        exact ⟨by simpa [he_symm] using hxs, hxU⟩
    rw [← hpre]
    exact h _ (hU.preimage e.continuous)
  · intro h V hV
    have himg :
        Fin.tail '' ({v : Fin (n + 1) → Z | (Fin.tail v, v 0) ∈ s} ∩ V) =
          Prod.fst '' (s ∩ e '' V) := by
      ext x
      constructor
      · rintro ⟨v, ⟨hvs, hvV⟩, rfl⟩
        exact ⟨e v, ⟨hvs, mem_image_of_mem e hvV⟩, rfl⟩
      · rintro ⟨_, ⟨hp, v, hvV, rfl⟩, rfl⟩
        exact ⟨v, ⟨hp, hvV⟩, rfl⟩
    rw [himg]
    exact h _ (e.isOpenMap V hV)

/-- A subset `ψ ⊆ Fin (n + 1) → Z` has open `Fin.tail` projection if and only if its image in
`(Fin n → Z) × Z` under `v ↦ (Fin.tail v, v 0)` has open `Prod.fst` projection. -/
theorem isOpenMap_domRestrict_tail_iff {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    {ψ : Set (Fin (n + 1) → Z)} :
    IsOpenMap (ψ.domRestrict Fin.tail) ↔
      IsOpenMap (((fun v : Fin (n + 1) → Z ↦ (Fin.tail v, v 0)) '' ψ).domRestrict Prod.fst) := by
  have hinj : Injective (fun w : Fin (n + 1) → Z ↦ (Fin.tail w, w 0)) :=
    LeftInverse.injective (g := fun p ↦ Fin.cons p.2 p.1) fun w ↦ Fin.cons_self_tail w
  have hpre : {v : Fin (n + 1) → Z |
      (Fin.tail v, v 0) ∈ (fun w : Fin (n + 1) → Z ↦ (Fin.tail w, w 0)) '' ψ} = ψ :=
    preimage_image_eq ψ hinj
  have hiff := isOpenMap_domRestrict_tail_preimage_iff
    (s := (fun v : Fin (n + 1) → Z ↦ (Fin.tail v, v 0)) '' ψ)
  rwa [hpre] at hiff

end TauCeti

section RootNamespaces

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Intersecting a set with an ambient open set preserves openness of its restricted map. -/
theorem IsOpenMap.domRestrict_inter {s U : Set X} {f : X → Y} (hs : IsOpenMap (s.domRestrict f))
    (hU : IsOpen U) : IsOpenMap ((s ∩ U).domRestrict f) := by
  refine TauCeti.isOpenMap_domRestrict_iff.2 fun V hV ↦ ?_
  rw [inter_assoc]
  exact TauCeti.isOpenMap_domRestrict_iff.1 hs (U ∩ V) (hU.inter hV)

/-- Openness of domain restrictions is preserved under binary unions. -/
theorem IsOpenMap.domRestrict_union {s t : Set X} {f : X → Y} (hs : IsOpenMap (s.domRestrict f))
    (ht : IsOpenMap (t.domRestrict f)) : IsOpenMap ((s ∪ t).domRestrict f) := by
  rw [union_eq_iUnion]
  exact TauCeti.isOpenMap_iUnion_domRestrict (Bool.rec ht hs)

/-- If every point `x ∈ s` admits a map `σ : Y → X` continuous at `f x` with `σ (f x) = x` that
locally lands in `s` as a section of `f`, then `s.domRestrict f` is an open map. -/
theorem TauCeti.isOpenMap_domRestrict_of_local_sections {s : Set X} {f : X → Y}
    (h : ∀ x ∈ s, ∃ σ : Y → X, ContinuousAt σ (f x) ∧ σ (f x) = x ∧
      ∀ᶠ y in 𝓝 (f x), σ y ∈ s ∧ f (σ y) = y) :
    IsOpenMap (s.domRestrict f) := by
  classical
  refine IsOpenMap.of_local_sections fun ⟨x, hx⟩ ↦ ?_
  obtain ⟨σ, hσc, hσx, hσs⟩ := h x hx
  let τ : Y → s := fun y ↦ if hy : σ y ∈ s then ⟨σ y, hy⟩ else ⟨x, hx⟩
  have hτ_val : Subtype.val ∘ τ =ᶠ[𝓝 (f x)] σ :=
    hσs.mono fun y hy ↦ by simp [τ, hy.1]
  refine ⟨τ, IsInducing.subtypeVal.continuousAt_iff.2 (hσc.congr hτ_val.symm), ?_, ?_⟩
  · apply Subtype.ext
    simp [τ, hσx, hx]
  · exact hσs.mono fun y hy ↦ by simp [τ, hy.1, hy.2]

/-- The graph of a continuous function over an open set has open first-coordinate projection. -/
theorem IsOpen.isOpenMap_graphOn_domRestrict_fst {s : Set X} (hs : IsOpen s) {φ : X → Z}
    (hφ : ContinuousOn φ s) : IsOpenMap ((s.graphOn φ).domRestrict Prod.fst) := by
  refine TauCeti.isOpenMap_domRestrict_of_local_sections ?_
  rintro ⟨x, z⟩ hxz
  obtain ⟨hxs, hz⟩ := mem_graphOn.1 hxz
  refine ⟨fun y ↦ (y, φ y), continuousAt_id.prodMk (hφ.continuousAt (hs.mem_nhds hxs)),
    Prod.ext rfl hz, ?_⟩
  filter_upwards [hs.mem_nhds hxs] with y hy
  exact ⟨mem_graphOn.2 ⟨hy, rfl⟩, rfl⟩

/-- In cylinder coordinates on `Fin (n + 1) → Z`, the graph
`{v | Fin.tail v ∈ s ∧ v 0 = φ (Fin.tail v)}` of a continuous function over an open base set
`s ⊆ Fin n → Z` has open `Fin.tail` projection. -/
theorem IsOpen.isOpenMap_domRestrict_tail_graph {n : ℕ} {s : Set (Fin n → Z)} (hs : IsOpen s)
    {φ : (Fin n → Z) → Z} (hφ : ContinuousOn φ s) :
    IsOpenMap
      ({v : Fin (n + 1) → Z | Fin.tail v ∈ s ∧ v 0 = φ (Fin.tail v)}.domRestrict Fin.tail) := by
  have hset : {v : Fin (n + 1) → Z | Fin.tail v ∈ s ∧ v 0 = φ (Fin.tail v)} =
      {v : Fin (n + 1) → Z | (Fin.tail v, v 0) ∈ s.graphOn φ} := by
    ext v
    simp [mem_graphOn, eq_comm]
  rw [hset]
  exact TauCeti.isOpenMap_domRestrict_tail_preimage_iff.2 (hs.isOpenMap_graphOn_domRestrict_fst hφ)

/-- **Base change of open projections.** Pulling back a subset `s ⊆ X × Z` with open first
projection along a continuous map `g : Y → X` of the base gives a subset of `Y × Z` with open first
projection. -/
theorem IsOpenMap.domRestrict_fst_preimage_prodMap_id {s : Set (X × Z)}
    (hs : IsOpenMap (s.domRestrict Prod.fst)) {g : Y → X} (hg : Continuous g) :
    IsOpenMap ((Prod.map g id ⁻¹' s).domRestrict Prod.fst) := by
  refine TauCeti.isOpenMap_domRestrict_iff.2 fun W hW ↦ isOpen_iff_mem_nhds.2 ?_
  rintro y ⟨⟨y, z⟩, ⟨hyz, hw⟩, rfl⟩
  obtain ⟨U, V, hU, hV, hyU, hzV, hUV⟩ := isOpen_prod_iff.1 hW y z hw
  have hO : IsOpen (Prod.fst '' (s ∩ univ ×ˢ V)) :=
    TauCeti.isOpenMap_domRestrict_iff.1 hs (univ ×ˢ V) (isOpen_univ.prod hV)
  have hyO : g y ∈ Prod.fst '' (s ∩ univ ×ˢ V) := ⟨(g y, z), ⟨hyz, trivial, hzV⟩, rfl⟩
  filter_upwards [hU.mem_nhds hyU, (hO.preimage hg).mem_nhds hyO] with y' hy'U hy'O
  obtain ⟨⟨_, z'⟩, ⟨hz's, -, hz'V⟩, rfl⟩ := hy'O
  exact ⟨(y', z'), ⟨hz's, hUV ⟨hy'U, hz'V⟩⟩, rfl⟩

/-- Pulling back a set with open first-coordinate projection along a product of homeomorphisms
preserves openness of the first-coordinate projection. -/
theorem IsOpenMap.domRestrict_fst_preimage_prodCongr {X' Z' : Type*}
    [TopologicalSpace X'] [TopologicalSpace Z'] {s : Set (X × Z)}
    (hs : IsOpenMap (s.domRestrict Prod.fst)) (e₁ : X' ≃ₜ X) (e₂ : Z' ≃ₜ Z) :
    IsOpenMap ((e₁.prodCongr e₂ ⁻¹' s).domRestrict Prod.fst) := by
  refine TauCeti.isOpenMap_domRestrict_iff.2 fun W hW ↦ ?_
  have himg : Prod.fst '' (e₁.prodCongr e₂ ⁻¹' s ∩ W) =
      e₁.symm '' (Prod.fst '' (s ∩ e₁.prodCongr e₂ '' W)) := by
    ext a
    constructor
    · rintro ⟨⟨a, c⟩, ⟨hac, hw⟩, rfl⟩
      exact ⟨e₁ a, ⟨(e₁ a, e₂ c), ⟨hac, mem_image_of_mem _ hw⟩, rfl⟩, e₁.symm_apply_apply a⟩
    · rintro ⟨_, ⟨⟨b, d⟩, ⟨hbd, ⟨a', c'⟩, hw, hab⟩, rfl⟩, rfl⟩
      obtain ⟨rfl, rfl⟩ : e₁ a' = b ∧ e₂ c' = d := Prod.mk.inj hab
      exact ⟨(a', c'), ⟨hbd, hw⟩, (e₁.symm_apply_apply a').symm⟩
  rw [himg]
  exact e₁.symm.isOpenMap _
    (TauCeti.isOpenMap_domRestrict_iff.1 hs _ ((e₁.prodCongr e₂).isOpenMap W hW))

/-- Openness of the restricted first-coordinate projection is invariant under preimage by a product
of homeomorphisms. -/
@[simp]
theorem Homeomorph.isOpenMap_preimage_prodMap_domRestrict_fst_iff {X' Z' : Type*}
    [TopologicalSpace X'] [TopologicalSpace Z'] (e₁ : X' ≃ₜ X) (e₂ : Z' ≃ₜ Z) {s : Set (X × Z)} :
    IsOpenMap ((Prod.map e₁ e₂ ⁻¹' s).domRestrict Prod.fst) ↔
      IsOpenMap (s.domRestrict Prod.fst) := by
  rw [← Homeomorph.coe_prodCongr]
  refine ⟨fun h ↦ ?_, fun h ↦ h.domRestrict_fst_preimage_prodCongr e₁ e₂⟩
  have h' := h.domRestrict_fst_preimage_prodCongr e₁.symm e₂.symm
  have hpre : e₁.symm.prodCongr e₂.symm ⁻¹' (e₁.prodCongr e₂ ⁻¹' s) = s := by
    ext ⟨a, c⟩
    simp
  rwa [hpre] at h'

end RootNamespaces

end
