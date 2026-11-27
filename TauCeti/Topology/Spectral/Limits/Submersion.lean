/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.ConcreteCategory.Basic
public import TauCeti.Topology.Spectral.Limits.Descent
public import TauCeti.Topology.Spectral.Limits.Detection
public import TauCeti.Topology.Spectral.Limits.Maps
public import TauCeti.Topology.Spectral.Submersion

/-!
# Cofiltered limits of spectral submersions

Let `η : F ⟶ G` be a natural transformation between cofiltered diagrams of spectral spaces with
spectral transition maps. If every component `η j` is a spectral submersion, then so is the induced
map `lim F → lim G` of limits. Spectral submersions are therefore stable under cofiltered limits,
which is what lets them be used for presentations of spectral spaces by limits.

The proof works with arbitrary limiting cones and proceeds by compactness of the constructible
topology, in three steps.

* The limit map is spectral because each of its coordinates is.
* It is surjective: its image is pro-constructible, so a point outside it has a constructible
  neighbourhood missing the image. That neighbourhood comes from a constructible set `W` at some
  stage `j`, and the constructible set `η j ⁻¹' W` misses the image of the limit of `F`. It
  therefore misses the image of a later stage `k`, which contradicts the surjectivity of `η k`.
* It detects quasi-compact openness: if the preimage of `U` is quasi-compact open, then `U` is
  constructible, so `U` comes from a constructible set `W` at some stage and its preimage comes
  from a quasi-compact open `V` at some stage. The constructible sets `V` and `η k ⁻¹' W` have the
  same preimage in the limit, so they agree at some later stage, where `η` is a spectral
  submersion. Hence `W` is open there, and so is `U`.

The ordinary quotient-map property is not preserved by cofiltered limits ([Arc] Remark 2.18), so
the conclusion cannot be strengthened to `Topology.IsQuotientMap`.

## Main results

* `TopCat.isSpectralSubmersion_isLimitMap` — the map `hd.map c η` between limiting cones induced
  by a levelwise spectral submersion `η` is a spectral submersion;
  `TopCat.isSpectralSubmersion_limMap` is the same statement for `CategoryTheory.Limits.limMap η`.
* `TopCat.isSpectralMap_isLimitMap`, `TopCat.isLimitMap_surjective` — the induced map is spectral
  when `η` is levelwise spectral, and, for cofiltered diagrams, surjective when `η` is levelwise
  surjective and spectral.

## References

* [Arc] B. Bhatt, A. Mathew, *The arc-topology*, Forum Math. Pi 9 (2021), §2, Lemma 2.17 and
  Remark 2.18.
-/

public section

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace TopCat

universe v u w

section Spectral

variable {J : Type v} [Category.{w} J]
  (F G : J ⥤ TopCat.{max v u}) [∀ j, SpectralSpace (F.obj j)] [∀ j, SpectralSpace (G.obj j)]
  (η : F ⟶ G)
  (hF : ∀ {i j} (f : i ⟶ j), IsSpectralMap (F.map f))
  (hG : ∀ {i j} (f : i ⟶ j), IsSpectralMap (G.map f))
  (c : Cone F) (hc : IsLimit c) {d : Cone G} (hd : IsLimit d)

include hF hG hc

/-- The map `hd.map c η` between limits of diagrams of spectral spaces with spectral transition
maps, induced by a natural transformation `η` with spectral components, is spectral. No
filteredness is needed. -/
theorem isSpectralMap_isLimitMap (hη : ∀ j, IsSpectralMap (η.app j)) :
    IsSpectralMap (hd.map c η) := by
  have := spectralSpace_of_isLimit F hF c hc
  refine (isSpectralMap_of_isLimit_iff G hG d hd _).2 fun j ↦ ?_
  have : d.π.app j ∘ hd.map c η = η.app j ∘ c.π.app j := funext (IsLimit.map_π_apply c hd η j)
  rw [this]
  exact (hη j).comp (isSpectralMap_of_isLimit_π F hF c hc j)

end Spectral

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
  (F G : J ⥤ TopCat.{max v u}) [∀ j, SpectralSpace (F.obj j)] [∀ j, SpectralSpace (G.obj j)]
  (η : F ⟶ G)
  (hF : ∀ {i j} (f : i ⟶ j), IsSpectralMap (F.map f))
  (hG : ∀ {i j} (f : i ⟶ j), IsSpectralMap (G.map f))
  (hη : ∀ j, TauCeti.IsSpectralSubmersion (η.app j))

section Compatible

variable (c : Cone F) (hc : IsLimit c) {d : Cone G} (hd : IsLimit d)

include hF hG hc

/-- A cofiltered limit of surjective spectral maps between spectral spaces with spectral
transition maps is surjective: if the components of `η` are surjective spectral maps, then the
induced map `hd.map c η` of limits is surjective. It is also spectral by
`isSpectralMap_isLimitMap`. -/
theorem isLimitMap_surjective (hη : ∀ j, IsSpectralMap (η.app j))
    (hη' : ∀ j, Function.Surjective (η.app j)) : Function.Surjective (hd.map c η) := by
  have := spectralSpace_of_isLimit F hF c hc
  have := spectralSpace_of_isLimit G hG d hd
  set φ := hd.map c η
  intro y
  by_contra hy
  -- The image of `φ` is pro-constructible, so a constructible neighbourhood of `y` misses it.
  have himage : TauCeti.IsProConstructible (range φ) := by
    simpa only [image_univ] using TauCeti.isProConstructible_univ.image
      (isSpectralMap_isLimitMap F G η hF hG c hc hd hη)
  obtain ⟨_, hV, hyV, hVφ⟩ :=
    @IsTopologicalBasis.exists_subset_of_mem_open d.pt (constructibleTopology d.pt) _
      (TauCeti.isTopologicalBasis_constructibleTopology d.pt) y _ hy
      (TauCeti.isProConstructible_iff_isClosed.1 himage).isOpen_compl
  obtain ⟨j, W, hW, rfl⟩ := exists_isConstructible_preimage_of_isLimit G hG d hd hV
  -- Hence `η j ⁻¹' W` misses the image of the limit of `F`, and so that of some stage `k`.
  have hempty : c.π.app j ⁻¹' (η.app j ⁻¹' W) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx ↦ hVφ
      (mem_preimage.2 (by rwa [IsLimit.map_π_apply]))
      (mem_range_self x)
  obtain ⟨k, f, hf⟩ := exists_preimage_eq_empty_of_isProConstructible F hF c hc
    ((hη j).isConstructible_preimage hW).isProConstructible hempty
  -- But `η k` is surjective, and a preimage of the `k`-th coordinate of `y` lies in that set.
  obtain ⟨x, hx⟩ := hη' k (d.π.app k y)
  have hmem : x ∈ F.map f ⁻¹' (η.app j ⁻¹' W) := by
    simpa only [mem_preimage, NatTrans.naturality_apply, hx, Cone.w_apply] using hyV
  rw [hf] at hmem
  exact hmem

include hη

/-- **Cofiltered limits of spectral submersions.** Let `η : F ⟶ G` be a natural transformation
between cofiltered diagrams of spectral spaces with spectral transition maps, each of whose
components is a spectral submersion. Then the induced map `hd.map c η` from a limit of `F` to a
limit of `G` is a spectral submersion. -/
theorem isSpectralSubmersion_isLimitMap : TauCeti.IsSpectralSubmersion (hd.map c η) := by
  have := spectralSpace_of_isLimit F hF c hc
  have := spectralSpace_of_isLimit G hG d hd
  have hspec := isSpectralMap_isLimitMap F G η hF hG c hc hd fun j ↦ (hη j).isSpectralMap
  have hsurj := isLimitMap_surjective F G η hF hG c hc hd (fun j ↦ (hη j).isSpectralMap)
    fun j ↦ (hη j).surjective
  refine ⟨hsurj, hspec, fun U hUo hUc ↦ ?_⟩
  -- `U` is constructible, so it comes from a constructible `W` at a stage `j`; its preimage
  -- comes from a quasi-compact open `V` at a stage `i`. Pass to a common stage below both.
  have hU : IsConstructible U := TauCeti.isClopen_constructibleTopology_iff_isConstructible.1
    (hspec.isClopen_constructibleTopology_of_isOpen_preimage hsurj hUo hUc)
  obtain ⟨j, W, hW, rfl⟩ := exists_isConstructible_preimage_of_isLimit G hG d hd hU
  obtain ⟨i, V, hVo, hVc, hV⟩ := exists_isOpen_isCompact_preimage_of_isLimit F hF c hc hUo hUc
  let a : IsCofiltered.min i j ⟶ i := IsCofiltered.minToLeft i j
  let b : IsCofiltered.min i j ⟶ j := IsCofiltered.minToRight i j
  set s : Set (F.obj (IsCofiltered.min i j)) := F.map a ⁻¹' V
  set t : Set (F.obj (IsCofiltered.min i j)) := η.app _ ⁻¹' (G.map b ⁻¹' W)
  have hs : IsConstructible s := (hF a).isConstructible_preimage (hVc.isConstructible hVo)
  have ht : IsConstructible t :=
    (hη _).isSpectralMap.isConstructible_preimage ((hG b).isConstructible_preimage hW)
  -- The constructible sets `s` and `t` have the same preimage in the limit of `F`, so they
  -- agree after a transition map `g : l ⟶ min i j`.
  have hst : c.π.app _ ⁻¹' s = c.π.app _ ⁻¹' t := by
    ext x
    simpa only [s, t, mem_preimage, Cone.w_apply, ← IsLimit.map_π_apply c hd η] using
      (Set.ext_iff.1 hV x).symm
  obtain ⟨l, g, hg⟩ := exists_preimage_eq_of_isConstructible F hF c hc hs ht hst
  -- At stage `l`, the preimage of `G.map b ⁻¹' W` under `η l` is quasi-compact open, so this set
  -- is open because `η l` is a spectral submersion. Its preimage in the limit of `G` is `U`.
  have heq : η.app l ⁻¹' (G.map g ⁻¹' (G.map b ⁻¹' W)) = F.map g ⁻¹' s := by
    rw [hg]
    simp only [t, preimage_preimage, NatTrans.naturality_apply]
  have hWo : IsOpen (G.map g ⁻¹' (G.map b ⁻¹' W)) := by
    refine (hη l).isOpen_of_isOpen_preimage_of_isCompact_preimage ?_ ?_ <;> rw [heq]
    · exact (hVo.preimage (hF a).continuous).preimage (hF g).continuous
    · exact (hF g).isCompact_preimage_of_isOpen (hVo.preimage (hF a).continuous)
        ((hF a).isCompact_preimage_of_isOpen hVo hVc)
  have hUl : d.π.app j ⁻¹' W = d.π.app l ⁻¹' (G.map g ⁻¹' (G.map b ⁻¹' W)) := by
    ext y
    simp only [mem_preimage, Cone.w_apply]
  exact hUl ▸ hWo.preimage (d.π.app l).hom.continuous

end Compatible

include hF hG hη

/-- **Cofiltered limits of spectral submersions** ([Arc] Lemma 2.17). Let `η : F ⟶ G` be a
natural transformation between cofiltered diagrams of spectral spaces with spectral transition
maps. If every component `η j` is a spectral submersion, then so is the induced map
`limMap η : limit F ⟶ limit G`. -/
theorem isSpectralSubmersion_limMap : TauCeti.IsSpectralSubmersion (limMap η) :=
  isSpectralSubmersion_isLimitMap F G η hF hG hη _ (limit.isLimit F) (limit.isLimit G)

end TopCat
