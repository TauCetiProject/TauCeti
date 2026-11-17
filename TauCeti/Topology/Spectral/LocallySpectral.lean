/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.SpectralMap
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.WithTopology
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# Locally spectral spaces and maps

A topological space is locally spectral when every point has a spectral open neighbourhood. A
map between locally spectral spaces is locally spectral when its restriction between any pair of
spectral open subspaces is a spectral map. This is the relative notion of spectral map used in
adic geometry; unlike Mathlib's `IsSpectralMap`, it does not require inverse images of all compact
opens to be compact globally.

The main comparison identifies locally spectral spaces that are compact and quasiseparated with
spectral spaces. Likewise, between spectral spaces the relative notion of locally spectral map
agrees with Mathlib's absolute one. Local spectrality of spaces passes to open subspaces and
finite products, local spectrality of maps can be tested on a single cover of the source, and
locally spectral maps compose through a locally spectral middle space.

## Main definitions

* `TauCeti.IsLocallySpectralSpace`: a space covered by spectral open subspaces.
* `TauCeti.IsLocallySpectralMap`: a continuous map whose restrictions between spectral opens are
  spectral.

## Main results

* `TauCeti.spectralSpace_iff_isLocallySpectralSpace`: the global-to-local comparison for spaces.
* `TauCeti.isLocallySpectralMap_iff_isSpectralMap`: the global-to-local comparison for maps
  between spectral spaces.
* `TauCeti.IsLocallySpectralSpace.isTopologicalBasis`: the spectral open subsets of a locally
  spectral space form a basis.
* `TauCeti.IsLocallySpectralSpace.spectralSpace_of_isOpen_isCompact`: compact open subsets of a
  quasiseparated locally spectral space are spectral.
* `Topology.IsOpenEmbedding.isLocallySpectralSpace`: open subspaces of locally spectral spaces are
  locally spectral.
* `TauCeti.spectralSpace_prod`, `TauCeti.IsLocallySpectralSpace.prod`: binary products of spectral
  and locally spectral spaces are spectral and locally spectral, respectively.
* `TauCeti.IsLocallySpectralMap.of_forall_exists`: local spectrality of a map tested on one cover.
* `TauCeti.IsLocallySpectralMap.comp`: composition through a locally spectral middle space.
* `Topology.IsOpenEmbedding.isLocallySpectralMap`, `TauCeti.isLocallySpectralMap_fst`,
  `TauCeti.isLocallySpectralMap_snd`: open embeddings and projections out of prespectral products
  are locally spectral.

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

/-- The spectral open subsets of a locally spectral space form a basis of its topology. -/
theorem IsLocallySpectralSpace.isTopologicalBasis (hX : IsLocallySpectralSpace X) :
    IsTopologicalBasis {U : Set X | IsOpen U ∧ SpectralSpace U} := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun U hU ↦ hU.1) fun x O hxO hOo ↦ ?_
  obtain ⟨V, hVo, hxV, hVs⟩ := hX x
  obtain ⟨W, hWVO, hWo, hxW, -, hWs⟩ := hVo.exists_spectralSpace_subset_inter hVs hOo hxV hxO
  exact ⟨W, ⟨hWo, hWs⟩, hxW, hWVO.trans inter_subset_right⟩

/-- A space admitting an open embedding into a locally spectral space is locally spectral. In
particular, every open subspace of a locally spectral space is locally spectral. -/
theorem _root_.Topology.IsOpenEmbedding.isLocallySpectralSpace {Z : Type*} [TopologicalSpace Z]
    {e : Z → X} (he : IsOpenEmbedding e) (hX : IsLocallySpectralSpace X) :
    IsLocallySpectralSpace Z := by
  intro z
  obtain ⟨W, ⟨hWo, hWs⟩, hzW, hWe⟩ :=
    hX.isTopologicalBasis.exists_subset_of_mem_open (mem_range_self z) he.isOpen_range
  refine ⟨e ⁻¹' W, hWo.preimage he.continuous, hzW, ?_⟩
  -- `e` restricts to a homeomorphism from `e ⁻¹' W` onto the spectral space `W`.
  let h := he.isEmbedding.homeomorphOfSubsetRange hWe
  have : CompactSpace (e ⁻¹' W) := h.symm.compactSpace
  exact h.isOpenEmbedding.spectralSpace

/-- A compact open subset of a quasiseparated locally spectral space is spectral. -/
theorem IsLocallySpectralSpace.spectralSpace_of_isOpen_isCompact [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X) {U : Set X} (hUo : IsOpen U) (hUc : IsCompact U) :
    SpectralSpace U :=
  spectralSpace_iff_isLocallySpectralSpace.mpr
    ⟨hUo.isOpenEmbedding_subtypeVal.isLocallySpectralSpace hX,
      isCompact_iff_compactSpace.mp hUc,
      hUo.isOpenEmbedding_subtypeVal.quasiSeparatedSpace⟩

/-- A binary product of prespectral spaces is prespectral. -/
instance prespectralSpace_prod [PrespectralSpace X] [PrespectralSpace Y] :
    PrespectralSpace (X × Y) := by
  refine .of_isTopologicalBasis
    (PrespectralSpace.isTopologicalBasis.prod PrespectralSpace.isTopologicalBasis) ?_
  rintro _ ⟨U, hU, V, hV, rfl⟩
  exact hU.2.prod hV.2

/-- A binary product of spectral spaces is spectral. -/
instance spectralSpace_prod [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) := by
  have hb := PrespectralSpace.isTopologicalBasis (X := X) |>.prod
    (PrespectralSpace.isTopologicalBasis (X := Y))
  have hgen := hb.eq_generateFrom
  have hT0 : T0Space (X × Y) := inferInstance
  let t' : TopologicalSpace (X × Y) :=
    @instTopologicalSpaceProd X Y (constructibleTopology X) (constructibleTopology Y)
  have hc : @CompactSpace (X × Y) t' := by
    have hcompX : @CompactSpace X (constructibleTopology X) :=
      @Function.Surjective.compactSpace (WithConstructibleTopology X) X _
        (constructibleTopology X) WithTopology.ofTopology
        (WithTopology.continuous_ofTopology _) inferInstance
        (WithTopology.ofTopology_surjective _)
    have hcompY : @CompactSpace Y (constructibleTopology Y) :=
      @Function.Surjective.compactSpace (WithConstructibleTopology Y) Y _
        (constructibleTopology Y) WithTopology.ofTopology
        (WithTopology.continuous_ofTopology _) inferInstance
        (WithTopology.ofTopology_surjective _)
    exact ⟨by
      rw [← Set.univ_prod_univ]
      exact @IsCompact.prod X Y (constructibleTopology X) (constructibleTopology Y) _ _
        (@CompactSpace.isCompact_univ X _ hcompX) (@CompactSpace.isCompact_univ Y _ hcompY)⟩
  refine @spectralSpace_of_isClopen_generateFrom _ _ t' (@instTopologicalSpaceProd X Y _ _)
    hgen hc ?_ hT0
  rintro _ ⟨U, ⟨hUo, hUc⟩, V, ⟨hVo, hVc⟩, rfl⟩
  dsimp only
  rw [Set.prod_eq]
  exact @IsClopen.inter _ t' _ _
    (@IsClopen.preimage _ _ t' (constructibleTopology X) _
      (hUc.isClopen_constructibleTopology_of_isOpen hUo) Prod.fst
      (@continuous_fst X Y (constructibleTopology X) (constructibleTopology Y)))
    (@IsClopen.preimage _ _ t' (constructibleTopology Y) _
      (hVc.isClopen_constructibleTopology_of_isOpen hVo) Prod.snd
      (@continuous_snd X Y (constructibleTopology X) (constructibleTopology Y)))

/-- A binary product of locally spectral spaces is locally spectral. -/
theorem IsLocallySpectralSpace.prod (hX : IsLocallySpectralSpace X)
    (hY : IsLocallySpectralSpace Y) : IsLocallySpectralSpace (X × Y) := by
  rintro ⟨x, y⟩
  obtain ⟨U, hUo, hxU, hUs⟩ := hX x
  obtain ⟨V, hVo, hyV, hVs⟩ := hY y
  refine ⟨U ×ˢ V, hUo.prod hVo, ⟨hxU, hyV⟩, ?_⟩
  have _ : CompactSpace (U ×ˢ V : Set (X × Y)) := (Homeomorph.Set.prod U V).symm.compactSpace
  exact (Homeomorph.Set.prod U V).isOpenEmbedding.spectralSpace

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
  refine ⟨continuous_id, fun U V hUV hUo _ hUs hVs ↦ ?_⟩
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

/-- **Local spectrality can be tested on a single cover.** A map is locally spectral as soon as
every point of the source lies in a quasiseparated open subset that maps spectrally into an open
subset of the target. Continuity of the map is a consequence. -/
theorem IsLocallySpectralMap.of_forall_exists {f : X → Y}
    (h : ∀ x, ∃ (U : Set X) (V : Set Y) (hUV : MapsTo f U V), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧
      QuasiSeparatedSpace U ∧ IsSpectralMap (hUV.restrict f U V)) :
    IsLocallySpectralMap f := by
  choose U V hUV hUo hVo hxU hUqs hUVs using h
  have hcont (x : X) : ContinuousOn f (U x) := by
    rw [continuousOn_iff_continuous_domRestrict, domRestrict_eq, ← (hUV x).restrict_commutes]
    exact continuous_subtype_val.comp (hUVs x).continuous
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x ↦
    (hcont x).continuousAt ((hUo x).mem_nhds (hxU x))
  refine .of_isSpectralMap_restrict hf fun U₀ V₀ hU₀V₀ hU₀o hV₀o hU₀s hV₀s ↦ ?_
  rw [hU₀V₀.isSpectralMap_restrict_iff hf.continuousOn hV₀o]
  intro K hKV hKo hKc
  refine (isCompact_iff_compactSpace.mpr hU₀s.toCompactSpace).inter_of_forall_exists
    fun x hx ↦ ?_
  -- Shrink to a compact open `W ∋ f x` inside `V₀ ∩ V x`, then to a compact open `U' ∋ x` inside
  -- `U₀ ∩ U x` that maps into `W`.
  obtain ⟨W, hWV, hWo, hxW, hWc, -⟩ :=
    hV₀o.exists_spectralSpace_subset_inter hV₀s (hVo x) (hU₀V₀ hx) (hUV x (hxU x))
  obtain ⟨U', hU'sub, hU'o, hxU', hU'c, -⟩ := hU₀o.exists_spectralSpace_subset_inter hU₀s
    ((hUo x).inter (hWo.preimage hf)) hx ⟨hxU x, hxW⟩
  refine ⟨U', hU'sub.trans inter_subset_left, hU'o, hxU', ?_⟩
  -- Since `f` maps `U'` into `W`, only the compact open `K ∩ W ⊆ V x` matters.
  have hKW : IsCompact (K ∩ W) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace V₀ hV₀o).mpr hV₀s.toQuasiSeparatedSpace K W hKV hKo
      hKc (hWV.trans inter_subset_left) hWo hWc
  have hpre : IsCompact (U x ∩ f ⁻¹' (K ∩ W)) :=
    ((hUV x).isSpectralMap_restrict_iff (hcont x) (hVo x)).mp (hUVs x) (K ∩ W)
      (inter_subset_right.trans (hWV.trans inter_subset_right)) (hKo.inter hWo) hKW
  have heq : U' ∩ f ⁻¹' K = U' ∩ (U x ∩ f ⁻¹' (K ∩ W)) := Set.ext fun y ↦
    ⟨fun ⟨hy, hyK⟩ ↦ ⟨hy, (hU'sub hy).2.1, hyK, (hU'sub hy).2.2⟩, fun ⟨hy, _, hyK, _⟩ ↦ ⟨hy, hyK⟩⟩
  rw [heq]
  exact (isQuasiSeparated_iff_quasiSeparatedSpace (U x) (hUo x)).mpr (hUqs x)
    U' _ (hU'sub.trans (inter_subset_right.trans inter_subset_left)) hU'o hU'c inter_subset_left
    ((hUo x).inter ((hKo.inter hWo).preimage hf)) hpre

/-- **Composition of locally spectral maps.** The composite of two locally spectral maps is locally
spectral provided the middle space is locally spectral. Without that hypothesis the middle space
may have too few spectral open subsets for the relative condition to say anything. -/
theorem IsLocallySpectralMap.comp {Z : Type*} [TopologicalSpace Z] {g : Y → Z} {f : X → Y}
    (hY : IsLocallySpectralSpace Y) (hg : IsLocallySpectralMap g) (hf : IsLocallySpectralMap f) :
    IsLocallySpectralMap (g ∘ f) := by
  refine .of_isSpectralMap_restrict (hg.continuous.comp hf.continuous)
    fun U W hUW hUo hWo hUs hWs ↦ ?_
  rw [hUW.isSpectralMap_restrict_iff (hg.continuous.comp hf.continuous).continuousOn hWo]
  intro K hKW hKo hKc
  refine (isCompact_iff_compactSpace.mpr hUs.toCompactSpace).inter_of_forall_exists
    fun x hx ↦ ?_
  -- Factor through a spectral open `V ∋ f x` with `g(V) ⊆ W` and a spectral open `U' ∋ x` with
  -- `f(U') ⊆ V`.
  obtain ⟨V₀, hV₀o, hxV₀, hV₀s⟩ := hY (f x)
  obtain ⟨V, hVsub, hVo, hxV, -, hVs⟩ :=
    hV₀o.exists_spectralSpace_subset_inter hV₀s (hWo.preimage hg.continuous) hxV₀ (hUW hx)
  obtain ⟨U', hU'sub, hU'o, hxU', -, hU's⟩ :=
    hUo.exists_spectralSpace_subset_inter hUs (hVo.preimage hf.continuous) hx hxV
  refine ⟨U', hU'sub.trans inter_subset_left, hU'o, hxU', ?_⟩
  have hU'V : MapsTo f U' V := fun y hy ↦ (hU'sub hy).2
  have hVW : MapsTo g V W := fun y hy ↦ (hVsub hy).2
  have := hU's
  have := hVs
  have hgK : IsCompact (V ∩ g ⁻¹' K) :=
    (hVW.isSpectralMap_restrict_iff hg.continuous.continuousOn hWo).mp
      (hg.isSpectralMap_restrict hVW hVo hWo) K hKW hKo hKc
  have hfK : IsCompact (U' ∩ f ⁻¹' (V ∩ g ⁻¹' K)) :=
    (hU'V.isSpectralMap_restrict_iff hf.continuous.continuousOn hVo).mp
      (hf.isSpectralMap_restrict hU'V hU'o hVo) _ inter_subset_left
      (hVo.inter (hKo.preimage hg.continuous)) hgK
  have heq : U' ∩ (g ∘ f) ⁻¹' K = U' ∩ f ⁻¹' (V ∩ g ⁻¹' K) := Set.ext fun y ↦
    ⟨fun ⟨hy, hyK⟩ ↦ ⟨hy, hU'V hy, hyK⟩, fun ⟨hy, _, hyK⟩ ↦ ⟨hy, hyK⟩⟩
  rwa [heq]

/-- Precomposing a locally spectral map with an open embedding yields a locally spectral map. -/
theorem IsLocallySpectralMap.comp_isOpenEmbedding {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    {e : X → Y} (hg : IsLocallySpectralMap g) (he : IsOpenEmbedding e) :
    IsLocallySpectralMap (g ∘ e) := by
  refine .of_isSpectralMap_restrict (hg.continuous.comp he.continuous)
    fun U W hUW hUo hWo hUs hWs ↦ ?_
  rw [hUW.isSpectralMap_restrict_iff (hg.continuous.comp he.continuous).continuousOn hWo]
  intro K hKW hKo hKc
  have heU_open : IsOpen (e '' U) := he.isOpenMap U hUo
  have heU_spec : SpectralSpace (e '' U) := by
    have _ : SpectralSpace U := hUs
    refine (he.isEmbedding.spectralSpace_preimage_iff (Set.image_subset_range e U)).mp ?_
    rwa [Set.preimage_image_eq U he.injective]
  have hmaps : MapsTo g (e '' U) W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hUW hx
  have hpre : IsCompact (e '' U ∩ g ⁻¹' K) :=
    (hmaps.isSpectralMap_restrict_iff hg.continuous.continuousOn hWo).mp
      (hg.isSpectralMap_restrict hmaps heU_open hWo) K hKW hKo hKc
  rw [he.isEmbedding.isCompact_iff, Set.preimage_comp, Set.image_inter_preimage]
  exact hpre

/-- Every open embedding is a locally spectral map. -/
theorem _root_.Topology.IsOpenEmbedding.isLocallySpectralMap {f : X → Y}
    (hf : IsOpenEmbedding f) : IsLocallySpectralMap f :=
  isLocallySpectralMap_id.comp_isOpenEmbedding hf

/-- The first projection out of a product of prespectral spaces is locally spectral. -/
theorem isLocallySpectralMap_fst [PrespectralSpace X] [PrespectralSpace Y] :
    IsLocallySpectralMap (Prod.fst : X × Y → X) := by
  refine .of_isSpectralMap_restrict continuous_fst fun U V hUV hUo hVo hUs hVs ↦ ?_
  rw [hUV.isSpectralMap_restrict_iff continuous_fst.continuousOn hVo]
  intro K hKV hKo hKc
  have hUcomp : IsCompact U := isCompact_iff_compactSpace.mpr hUs.toCompactSpace
  have hboxes (p : U) : ∃ (A : Set X) (B : Set Y),
      IsOpen A ∧ IsCompact A ∧ IsOpen B ∧ IsCompact B ∧
        p.1 ∈ A ×ˢ B ∧ A ×ˢ B ⊆ U := by
    obtain ⟨W, ⟨A, ⟨hAo, hAc⟩, B, ⟨hBo, hBc⟩, rfl⟩, hpW, hWU⟩ :=
      (PrespectralSpace.isTopologicalBasis.prod
        PrespectralSpace.isTopologicalBasis).exists_subset_of_mem_open p.2 hUo
    exact ⟨A, B, hAo, hAc, hBo, hBc, hpW, hWU⟩
  choose A B hAo hAc hBo hBc hpAB hABU using hboxes
  obtain ⟨T, hT⟩ := hUcomp.elim_finite_subcover (fun p : U ↦ A p ×ˢ B p)
    (fun p ↦ (hAo p).prod (hBo p))
    (fun p hp ↦ Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hpAB ⟨p, hp⟩⟩)
  have heq : U ∩ Prod.fst ⁻¹' K = ⋃ p ∈ T, (A p ∩ K) ×ˢ B p := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨hxyU, hxK⟩
      obtain ⟨p, hpT, hxA, hyB⟩ := Set.mem_iUnion₂.mp (hT hxyU)
      exact Set.mem_iUnion₂.mpr ⟨p, hpT, ⟨hxA, hxK⟩, hyB⟩
    · intro h
      obtain ⟨p, -, ⟨hxA, hxK⟩, hyB⟩ := Set.mem_iUnion₂.mp h
      exact ⟨hABU p ⟨hxA, hyB⟩, hxK⟩
  rw [heq]
  refine T.isCompact_biUnion fun p _ ↦ (?_ : IsCompact (A p ∩ K)).prod (hBc p)
  have hAV : A p ⊆ V := fun a ha ↦ by
    have hmem : (a, p.1.2) ∈ A p ×ˢ B p := ⟨ha, (hpAB p).2⟩
    exact hUV (hABU p hmem)
  exact (isQuasiSeparated_iff_quasiSeparatedSpace V hVo).mpr hVs.toQuasiSeparatedSpace
    (A p) K hAV (hAo p) (hAc p) hKV hKo hKc

/-- The second projection out of a product of prespectral spaces is locally spectral. -/
theorem isLocallySpectralMap_snd [PrespectralSpace X] [PrespectralSpace Y] :
    IsLocallySpectralMap (Prod.snd : X × Y → Y) :=
  isLocallySpectralMap_fst.comp_isOpenEmbedding (Homeomorph.prodComm X Y).isOpenEmbedding

end TauCeti

end
