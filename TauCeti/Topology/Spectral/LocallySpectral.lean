/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.SpectralMap

/-!
# Locally spectral spaces and maps

A topological space is locally spectral when every point has a spectral open neighbourhood. A
map between locally spectral spaces is locally spectral when its restriction between any pair of
spectral open subspaces is a spectral map. This is the relative notion of spectral map used in
adic geometry; unlike Mathlib's `IsSpectralMap`, it does not require inverse images of all compact
opens to be compact globally.

The main comparison identifies locally spectral spaces that are compact and quasiseparated with
spectral spaces. Likewise, between spectral spaces the relative notion of locally spectral map
agrees with Mathlib's absolute one.

## Main definitions

* `TauCeti.IsLocallySpectralSpace`: a space covered by spectral open subspaces.
* `TauCeti.IsLocallySpectralMap`: a continuous map whose restrictions between spectral opens are
  spectral.

## Main results

* `TauCeti.spectralSpace_iff_isLocallySpectralSpace`: the global-to-local comparison for spaces.
* `TauCeti.isLocallySpectralMap_iff_isSpectralMap`: the global-to-local comparison for maps
  between spectral spaces.

## References

* P. Scholze, *Étale cohomology of diamonds*, §2, Definition 2.1.
* K. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, §8.1.
-/

public section

namespace TauCeti

open Set Topology TopologicalSpace

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A topological space is **locally spectral** if every point has a spectral open
neighbourhood. -/
def IsLocallySpectralSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ SpectralSpace U

/-- The defining property of a locally spectral space. -/
theorem isLocallySpectralSpace_iff :
    IsLocallySpectralSpace X ↔ ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ SpectralSpace U :=
  Iff.rfl

/-- A space is locally spectral as soon as every point has a spectral open neighbourhood, phrased
with the neighbourhood filter. -/
theorem IsLocallySpectralSpace.of_exists_mem_nhds
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, IsOpen U ∧ SpectralSpace U) : IsLocallySpectralSpace X := fun x ↦
  let ⟨U, hUx, hUo, hUs⟩ := h x
  ⟨U, hUo, mem_of_mem_nhds hUx, hUs⟩

/-- Every point of a locally spectral space has a spectral open neighbourhood. -/
theorem IsLocallySpectralSpace.exists_mem_nhds (hX : IsLocallySpectralSpace X) (x : X) :
    ∃ U ∈ 𝓝 x, IsOpen U ∧ SpectralSpace U :=
  let ⟨U, hUo, hxU, hUs⟩ := hX x
  ⟨U, hUo.mem_nhds hxU, hUo, hUs⟩

/-- Every spectral space is locally spectral. -/
theorem _root_.SpectralSpace.isLocallySpectralSpace [SpectralSpace X] :
    IsLocallySpectralSpace X := fun x ↦
  ⟨univ, isOpen_univ, mem_univ x, spectralSpace_univ⟩

/-- A locally spectral space has a basis of compact open subsets. -/
theorem IsLocallySpectralSpace.prespectralSpace (hX : IsLocallySpectralSpace X) :
    PrespectralSpace X := by
  let S : Set (Set X) := {U | IsOpen U ∧ SpectralSpace U}
  let U : S → Opens X := fun s ↦ ⟨s, s.2.1⟩
  have hU : IsOpenCover U := IsOpenCover.of_sets (fun s ↦ s.2.1) <| by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨V, hVo, hxV, hVs⟩ := hX x
    exact mem_iUnion.mpr ⟨⟨V, hVo, hVs⟩, hxV⟩
  let _ : ∀ s, PrespectralSpace (U s) := fun s ↦ s.2.2.toPrespectralSpace
  exact PrespectralSpace.of_isOpenCover hU

/-- A locally spectral space is quasi-sober. -/
theorem IsLocallySpectralSpace.quasiSober (hX : IsLocallySpectralSpace X) : QuasiSober X := by
  let S : Set (Set X) := {U | IsOpen U ∧ SpectralSpace U}
  let _ : ∀ s : S, QuasiSober s := fun s ↦ s.2.2.toQuasiSober
  apply quasiSober_of_open_cover S (fun s ↦ s.2.1)
  apply eq_univ_iff_forall.mpr
  intro x
  obtain ⟨U, hUo, hxU, hUs⟩ := hX x
  exact mem_sUnion_of_mem hxU ⟨hUo, hUs⟩

/-- A locally spectral space is Kolmogorov. -/
theorem IsLocallySpectralSpace.t0Space (hX : IsLocallySpectralSpace X) : T0Space X :=
  T0Space.of_open_cover fun x ↦ by
    obtain ⟨U, hUo, hxU, hUs⟩ := hX x
    exact ⟨U, hxU, hUo, hUs.toT0Space⟩

/-- A space is spectral exactly when it is locally spectral, compact, and quasiseparated. -/
theorem spectralSpace_iff_isLocallySpectralSpace :
    SpectralSpace X ↔ IsLocallySpectralSpace X ∧ CompactSpace X ∧ QuasiSeparatedSpace X := by
  constructor
  · intro hX
    exact ⟨hX.isLocallySpectralSpace, hX.toCompactSpace, hX.toQuasiSeparatedSpace⟩
  · rintro ⟨hX, hXc, hXqs⟩
    exact {
      toT0Space := hX.t0Space
      toCompactSpace := hXc
      toQuasiSober := hX.quasiSober
      toQuasiSeparatedSpace := hXqs
      toPrespectralSpace := hX.prespectralSpace }

/-- A map is **locally spectral** if it is continuous and every restriction between spectral open
subspaces is a spectral map. This is a relative condition: no global compactness is imposed on
the inverse image of a compact open. -/
def IsLocallySpectralMap (f : X → Y) : Prop :=
  Continuous f ∧ ∀ (U : Set X) (V : Set Y) (hUV : MapsTo f U V), IsOpen U → IsOpen V →
    SpectralSpace U → SpectralSpace V → IsSpectralMap (hUV.restrict f U V)

/-- The defining property of a locally spectral map. -/
theorem isLocallySpectralMap_iff {f : X → Y} :
    IsLocallySpectralMap f ↔ Continuous f ∧ ∀ (U : Set X) (V : Set Y) (hUV : MapsTo f U V),
      IsOpen U → IsOpen V → SpectralSpace U → SpectralSpace V →
        IsSpectralMap (hUV.restrict f U V) :=
  Iff.rfl

/-- A continuous map whose restrictions between spectral open subspaces are spectral is locally
spectral. -/
theorem IsLocallySpectralMap.of_isSpectralMap_restrict {f : X → Y} (hf : Continuous f)
    (h : ∀ (U : Set X) (V : Set Y) (hUV : MapsTo f U V), IsOpen U → IsOpen V →
      SpectralSpace U → SpectralSpace V → IsSpectralMap (hUV.restrict f U V)) :
    IsLocallySpectralMap f :=
  ⟨hf, h⟩

/-- A locally spectral map is continuous. -/
theorem IsLocallySpectralMap.continuous {f : X → Y} (hf : IsLocallySpectralMap f) : Continuous f :=
  hf.1

/-- The restriction of a locally spectral map between spectral open subspaces is spectral. -/
theorem IsLocallySpectralMap.isSpectralMap_restrict {f : X → Y} (hf : IsLocallySpectralMap f)
    {U : Set X} {V : Set Y} (hUV : MapsTo f U V) (hUo : IsOpen U) (hVo : IsOpen V)
    [SpectralSpace U] [SpectralSpace V] : IsSpectralMap (hUV.restrict f U V) :=
  hf.2 U V hUV hUo hVo ‹_› ‹_›

/-- The identity map is locally spectral. -/
theorem isLocallySpectralMap_id : IsLocallySpectralMap (id : X → X) := by
  refine ⟨continuous_id, fun U V hUV hUo hVo hUs hVs ↦ ?_⟩
  let _ : SpectralSpace U := hUs
  let _ : SpectralSpace V := hVs
  have hemb : IsOpenEmbedding (Set.inclusion hUV) :=
    IsOpenEmbedding.inclusion hUV (hUo.preimage continuous_subtype_val)
  have heq : hUV.restrict id U V = Set.inclusion hUV := by
    funext x
    rfl
  rw [heq]
  exact hemb.isSpectralMap

/-- On spectral spaces, a locally spectral map is a spectral map. -/
theorem IsLocallySpectralMap.isSpectralMap [SpectralSpace X] [SpectralSpace Y] {f : X → Y}
    (hf : IsLocallySpectralMap f) : IsSpectralMap f := by
  have _ : SpectralSpace (univ : Set X) := spectralSpace_univ
  have _ : SpectralSpace (univ : Set Y) := spectralSpace_univ
  have hrest := hf.isSpectralMap_restrict (Set.mapsTo_univ f univ) isOpen_univ isOpen_univ
  refine ⟨hf.continuous, fun s hso hsc ↦ ?_⟩
  let s' : Set (univ : Set Y) := Subtype.val ⁻¹' s
  have hs'o : IsOpen s' := hso.preimage continuous_subtype_val
  have hs'c : IsCompact s' := by
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    simpa [s'] using hsc
  have hpre := hrest.isCompact_preimage_of_isOpen hs'o hs'c
  have heq : Subtype.val '' ((Set.mapsTo_univ f univ).restrict f univ univ ⁻¹' s') =
      f ⁻¹' s := by
    rw [← preimage_comp, MapsTo.restrict_commutes, preimage_comp, Subtype.image_preimage_coe,
      univ_inter]
  rw [← heq]
  exact hpre.image continuous_subtype_val

/-- A spectral map from a quasiseparated space is locally spectral. -/
theorem _root_.IsSpectralMap.isLocallySpectralMap [QuasiSeparatedSpace X] {f : X → Y}
    (hf : IsSpectralMap f) : IsLocallySpectralMap f := by
  refine ⟨hf.continuous, fun U V hUV hUo hVo hUs hVs ↦ ?_⟩
  let _ : SpectralSpace U := hUs
  let _ : SpectralSpace V := hVs
  let iU : U → X := Subtype.val
  have hiU : IsSpectralMap iU := hUo.isOpenEmbedding_subtypeVal.isSpectralMap
  let g : U → Y := f ∘ iU
  have hg : IsSpectralMap g := hf.comp hiU
  refine ⟨hg.continuous.subtype_mk fun x ↦ hUV x.2, fun s hso hsc ↦ ?_⟩
  have hs_image_open : IsOpen (Subtype.val '' s : Set Y) :=
    hVo.isOpenEmbedding_subtypeVal.isOpenMap _ hso
  have hs_image_compact : IsCompact (Subtype.val '' s : Set Y) :=
    hsc.image continuous_subtype_val
  have hpre := hg.isCompact_preimage_of_isOpen hs_image_open hs_image_compact
  have heq : (hUV.restrict f U V) ⁻¹' s = g ⁻¹' (Subtype.val '' s) := by
    conv_lhs => rw [← preimage_image_eq s Subtype.val_injective]
    rw [← preimage_comp, MapsTo.restrict_commutes]
  rw [heq]
  exact hpre

/-- Between spectral spaces, locally spectral maps are precisely Mathlib's spectral maps. -/
theorem isLocallySpectralMap_iff_isSpectralMap [SpectralSpace X] [SpectralSpace Y] {f : X → Y} :
    IsLocallySpectralMap f ↔ IsSpectralMap f :=
  ⟨IsLocallySpectralMap.isSpectralMap, IsSpectralMap.isLocallySpectralMap⟩

end TauCeti

end
