/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.ProConstructible

/-!
# Spectral submersions

A **spectral submersion** is a surjective spectral map `f : X → Y` such that a subset `U ⊆ Y` is
open as soon as its preimage `f ⁻¹' U` is quasi-compact and open. This is weaker than being a
quotient map (`Topology.IsQuotientMap`), which asks the same of every subset with open preimage.
The weaker condition is the one that survives cofiltered limits of spectral spaces, which is why
it, rather than the quotient property, is the notion used for presentations of spectral spaces by
limits and for descent of topological data along such presentations.

## Main definitions

* `TauCeti.IsSpectralSubmersion f` — `f` is surjective and spectral, and a subset whose preimage
  is quasi-compact open is open.

## Main results

* `TauCeti.IsSpectralSubmersion.isOpen_preimage_and_isCompact_preimage_iff` — along a spectral
  submersion, `U` is quasi-compact open exactly when `f ⁻¹' U` is.
* `TauCeti.isSpectralSubmersion_id`, `TauCeti.IsSpectralSubmersion.comp` — identities are spectral
  submersions, and spectral submersions compose; `TauCeti.IsSpectralSubmersion.of_comp` is the
  cancellation property.
* `Topology.IsQuotientMap.isSpectralSubmersion` — a spectral quotient map is a spectral
  submersion; `IsSpectralMap.isSpectralSubmersion_of_generalizingMap` — so is a surjective
  generalizing spectral map onto a spectral space.
* `IsSpectralMap.isClopen_constructibleTopology_of_isOpen_preimage` — if `f` is a surjective
  spectral map of spectral spaces and `f ⁻¹' U` is quasi-compact open, then `U` is clopen for the
  constructible topology.
* `TauCeti.isSpectralSubmersion_iff_isClopen_constructibleTopology` — between spectral spaces it
  suffices to test the descent of quasi-compact openness on constructible subsets.
* `TauCeti.isSpectralSubmersion_iff_isHomeomorph_of_injective` — out of a prespectral space, an
  injective spectral submersion is a homeomorphism. For instance, the identity map from the
  constructible topology of a spectral space to the space itself is a bijective spectral map
  that is not a spectral submersion unless the two topologies agree.

## References

* B. Bhatt, A. Mathew, *The arc-topology*, Forum Math. Pi 9 (2021), §2, Definition 2.14 and
  Remark 2.15.
-/

public section

namespace TauCeti

open Set Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A map `f : X → Y` is a **spectral submersion** if it is surjective and spectral, and a subset
`U ⊆ Y` is open whenever its preimage `f ⁻¹' U` is quasi-compact and open.

Every spectral quotient map is a spectral submersion
(`Topology.IsQuotientMap.isSpectralSubmersion`), but not conversely: the descent condition is only
imposed on subsets with quasi-compact open preimage. -/
structure IsSpectralSubmersion (f : X → Y) : Prop where
  /-- A spectral submersion is surjective. -/
  surjective : Function.Surjective f
  /-- A spectral submersion is a spectral map. -/
  isSpectralMap : IsSpectralMap f
  /-- A subset whose preimage is quasi-compact open is open. -/
  isOpen_of_isOpen_preimage_of_isCompact_preimage :
    ∀ ⦃U : Set Y⦄, IsOpen (f ⁻¹' U) → IsCompact (f ⁻¹' U) → IsOpen U

namespace IsSpectralSubmersion

variable {f : X → Y} {g : Y → Z}

/-- A spectral submersion is continuous. -/
theorem continuous (hf : IsSpectralSubmersion f) : Continuous f :=
  hf.isSpectralMap.continuous

/-- Along a surjective continuous map, in particular along a spectral submersion, a subset is
quasi-compact if its preimage is. -/
theorem isCompact_of_isCompact_preimage (hf : IsSpectralSubmersion f) {U : Set Y}
    (hU : IsCompact (f ⁻¹' U)) : IsCompact U := by
  simpa only [image_preimage_eq U hf.surjective] using hU.image hf.continuous

/-- Along a spectral submersion `f`, a subset `U` is quasi-compact open exactly when its
preimage `f ⁻¹' U` is. -/
theorem isOpen_preimage_and_isCompact_preimage_iff (hf : IsSpectralSubmersion f) {U : Set Y} :
    IsOpen (f ⁻¹' U) ∧ IsCompact (f ⁻¹' U) ↔ IsOpen U ∧ IsCompact U :=
  ⟨fun ⟨hUo, hUc⟩ ↦ ⟨hf.isOpen_of_isOpen_preimage_of_isCompact_preimage hUo hUc,
      hf.isCompact_of_isCompact_preimage hUc⟩,
    fun ⟨hUo, hUc⟩ ↦ ⟨hUo.preimage hf.continuous,
      hf.isSpectralMap.isCompact_preimage_of_isOpen hUo hUc⟩⟩

/-- A composite of spectral submersions is a spectral submersion. No hypothesis on the spaces is
needed: the preimage of `U` under the second map is the image of its preimage under the
composite, hence quasi-compact. -/
theorem comp (hg : IsSpectralSubmersion g) (hf : IsSpectralSubmersion f) :
    IsSpectralSubmersion (g ∘ f) where
  surjective := hg.surjective.comp hf.surjective
  isSpectralMap := hg.isSpectralMap.comp hf.isSpectralMap
  isOpen_of_isOpen_preimage_of_isCompact_preimage U hUo hUc := by
    rw [preimage_comp] at hUo hUc
    exact hg.isOpen_of_isOpen_preimage_of_isCompact_preimage
      (hf.isOpen_of_isOpen_preimage_of_isCompact_preimage hUo hUc)
      (hf.isCompact_of_isCompact_preimage hUc)

/-- If a composite `g ∘ f` of spectral maps is a spectral submersion, then so is `g`. -/
theorem of_comp (hgf : IsSpectralSubmersion (g ∘ f)) (hg : IsSpectralMap g)
    (hf : IsSpectralMap f) : IsSpectralSubmersion g where
  surjective := hgf.surjective.of_comp
  isSpectralMap := hg
  isOpen_of_isOpen_preimage_of_isCompact_preimage _ hUo hUc :=
    hgf.isOpen_of_isOpen_preimage_of_isCompact_preimage (hUo.preimage hf.continuous)
      (hf.isCompact_preimage_of_isOpen hUo hUc)

end IsSpectralSubmersion

/-- The identity map of any topological space is a spectral submersion. -/
theorem isSpectralSubmersion_id : IsSpectralSubmersion (id : X → X) where
  surjective := Function.surjective_id
  isSpectralMap := isSpectralMap_id
  isOpen_of_isOpen_preimage_of_isCompact_preimage _ hU _ := hU

/-- A spectral quotient map is a spectral submersion: its descent clause is the quotient property
restricted to subsets with quasi-compact open preimage. -/
theorem _root_.Topology.IsQuotientMap.isSpectralSubmersion {f : X → Y} (hq : IsQuotientMap f)
    (hf : IsSpectralMap f) : IsSpectralSubmersion f where
  surjective := hq.surjective
  isSpectralMap := hf
  isOpen_of_isOpen_preimage_of_isCompact_preimage _ hU _ := hq.isOpen_preimage.1 hU

/-- A homeomorphism is a spectral submersion. -/
theorem _root_.IsHomeomorph.isSpectralSubmersion {f : X → Y} (hf : IsHomeomorph f) :
    IsSpectralSubmersion f :=
  hf.isQuotientMap.isSpectralSubmersion hf.isClosedEmbedding.isProperMap.isSpectralMap

/-- A surjective generalizing spectral map onto a spectral space is a spectral submersion; the
source need only be compact, quasi-sober, quasi-separated and prespectral. -/
theorem _root_.IsSpectralMap.isSpectralSubmersion_of_generalizingMap [CompactSpace X]
    [QuasiSober X] [PrespectralSpace X] [QuasiSeparatedSpace X] [SpectralSpace Y] {f : X → Y}
    (hf : IsSpectralMap f) (hg : GeneralizingMap f) (hsurj : Function.Surjective f) :
    IsSpectralSubmersion f :=
  (hf.isQuotientMap_of_generalizingMap hg hsurj).isSpectralSubmersion hf

/-! ### The constructible criterion -/

/-- Let `f : X → Y` be a surjective spectral map from a compact, quasi-sober, quasi-separated
prespectral space (for instance a spectral space) to a T₀ prespectral space. If `f ⁻¹' U` is
quasi-compact open, then `U` is clopen for the constructible topology of `Y`: both `U` and its
complement are images of pro-constructible subsets of `X`. -/
theorem _root_.IsSpectralMap.isClopen_constructibleTopology_of_isOpen_preimage [CompactSpace X]
    [QuasiSober X] [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y] [T0Space Y]
    {f : X → Y} (hf : IsSpectralMap f) (hsurj : Function.Surjective f) {U : Set Y}
    (hUo : IsOpen (f ⁻¹' U)) (hUc : IsCompact (f ⁻¹' U)) :
    IsClopen[constructibleTopology Y] U := by
  have hU : IsProConstructible U := by
    simpa only [image_preimage_eq U hsurj] using (hUc.isProConstructible hUo).image hf
  have hUcompl : IsProConstructible Uᶜ := by
    rw [← image_preimage_eq Uᶜ hsurj, preimage_compl]
    exact hUo.isClosed_compl.isProConstructible.image hf
  rw [isProConstructible_iff_isClosed] at hU hUcompl
  exact ⟨hU, (@isClosed_compl_iff Y (constructibleTopology Y) U).1 hUcompl⟩

/-- **Constructible criterion for spectral submersions.** For a map `f` from a compact,
quasi-sober, quasi-separated prespectral space (for instance a spectral space) to a T₀ prespectral
space, it suffices to check the descent of quasi-compact openness on subsets of `Y` that are
clopen for the constructible topology. The restriction loses nothing: by
`IsSpectralMap.isClopen_constructibleTopology_of_isOpen_preimage`, every subset with quasi-compact
open preimage is of this form. -/
theorem isSpectralSubmersion_iff_isClopen_constructibleTopology [CompactSpace X] [QuasiSober X]
    [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y] [T0Space Y] {f : X → Y} :
    IsSpectralSubmersion f ↔ Function.Surjective f ∧ IsSpectralMap f ∧
      ∀ U : Set Y, IsClopen[constructibleTopology Y] U →
        IsOpen (f ⁻¹' U) → IsCompact (f ⁻¹' U) → IsOpen U :=
  ⟨fun hf ↦ ⟨hf.surjective, hf.isSpectralMap,
      fun _ _ hUo hUc ↦ hf.isOpen_of_isOpen_preimage_of_isCompact_preimage hUo hUc⟩,
    fun ⟨hsurj, hf, h⟩ ↦ ⟨hsurj, hf, fun U hUo hUc ↦
      h U (hf.isClopen_constructibleTopology_of_isOpen_preimage hsurj hUo hUc) hUo hUc⟩⟩

/-! ### Injective spectral submersions -/

/-- An injective spectral submersion out of a prespectral space is a homeomorphism: it carries
each quasi-compact open subset `V` to a subset with preimage `V`, hence to an open subset. -/
theorem IsSpectralSubmersion.isHomeomorph_of_injective [PrespectralSpace X] {f : X → Y}
    (hf : IsSpectralSubmersion f) (hinj : Function.Injective f) : IsHomeomorph f where
  continuous := hf.continuous
  isOpenMap := PrespectralSpace.isTopologicalBasis.isOpenMap_iff.2 fun V ⟨hVo, hVc⟩ ↦
    hf.isOpen_of_isOpen_preimage_of_isCompact_preimage
      (by rwa [preimage_image_eq V hinj]) (by rwa [preimage_image_eq V hinj])
  bijective := ⟨hinj, hf.surjective⟩

/-- An injective map out of a prespectral space is a spectral submersion if and only if it is a
homeomorphism. In particular, a bijective spectral map need not be a spectral submersion. -/
theorem isSpectralSubmersion_iff_isHomeomorph_of_injective [PrespectralSpace X] {f : X → Y}
    (hinj : Function.Injective f) : IsSpectralSubmersion f ↔ IsHomeomorph f :=
  ⟨fun hf ↦ hf.isHomeomorph_of_injective hinj, IsHomeomorph.isSpectralSubmersion⟩

end TauCeti
