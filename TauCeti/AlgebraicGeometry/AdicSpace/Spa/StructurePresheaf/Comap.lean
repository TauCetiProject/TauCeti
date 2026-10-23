/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Cofinality

/-!
# The morphism of structure presheaves induced by a homomorphism of Huber pairs

Let `φ : A → B` be a continuous ring homomorphism of topological rings with pairs of definition
`P` and `P'` and subrings `A⁺ ⊆ A` and `B⁺ ⊆ B`, carrying `A⁺` into `B⁺`, and let
`f : Spa(B, B⁺) → Spa(A, A⁺)` be the induced map of adic spectra. Following Wedhorn §8.1, on a
rational open `R(T/s)` of `Spa(A, A⁺)` the structure presheaf has the value `A⟨T/s⟩`, and for every
rational open `R(q)` of `Spa(B, B⁺)` inside the preimage `f⁻¹(R(T/s))` there is the geometric base
change `A⟨T/s⟩ → B⟨q⟩` of `φ` (`TauCeti.Huber.PairOfDefinition.Presentation.mapHomOfSubset`). These
assemble into a morphism `A⟨T/s⟩ → 𝒪_{Spa B}(f⁻¹(R(T/s)))`. To extend them to a morphism
`𝒪_{Spa A} → f_* 𝒪_{Spa B}` on all opens, the morphisms on the rational opens `R(T/s) ⊆ U` have to
be assembled into a map into `𝒪_{Spa B}(f⁻¹U)`. The opens `f⁻¹(R(T/s))` cover `f⁻¹U`, so this is
possible when `𝒪_{Spa B}` is a sheaf, which is the case treated here. (A rational open of `f⁻¹U`
need not lie in the preimage of a single rational open of `U`, so the limit description of
`𝒪_{Spa B}(f⁻¹U)` alone does not provide the map.)

No condition relating the topologies of `A` and `B` beyond continuity of `φ` is needed. When `φ`
moreover carries open ideals to open ideals (for instance, when `φ` is adic), the preimage
`f⁻¹(R(T/s)) = R(φ(T)/φ(s))` is itself a rational open of `Spa(B, B⁺)`, and on it the morphism is
the base change `A⟨T/s⟩ → B⟨φ(T)/φ(s)⟩` (`presentationLimitComap_comp_map_comp_hom`).

This is the presheaf half of Wedhorn's construction of the morphism of pre-adic spaces
`Spa(φ) : Spa(B, B⁺) → Spa(A, A⁺)`; the compatibility with the stalk valuations is not treated
here.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitComap`: the component at an open `U` of
  `Spa(A, A⁺)`, a morphism `𝒪_{Spa A}(U) ⟶ 𝒪_{Spa B}(f⁻¹U)`.
* `TauCeti.ValuationSpectrum.presentationLimitPresheafComap`: the morphism of presheaves
  `𝒪_{Spa A} ⟶ f_* 𝒪_{Spa B}`.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitComap_comp_map_comp_π_of_subset`: on a rational open
  `R(q)` of `Spa(B, B⁺)` inside `f⁻¹(R(T/s))` the morphism is the geometric base change
  `A⟨T/s⟩ → B⟨q⟩`.
* `TauCeti.ValuationSpectrum.presentationLimitComap_comp_map_comp_π`: when `φ` carries open ideals
  to open ideals, on the rational open `f⁻¹(R(T/s)) = R(φ(T)/φ(s))` the morphism is the base change
  `A⟨T/s⟩ → B⟨φ(T)/φ(s)⟩`.
* `TauCeti.ValuationSpectrum.presentationLimit_hom_ext_of_isSheaf`: morphisms into
  `𝒪_{Spa B}(f⁻¹U)` are determined by their restrictions to the opens `f⁻¹(R(T/s))` for the
  rational opens `R(T/s) ⊆ U`.
* `TauCeti.ValuationSpectrum.presentationLimitMap_comp_presentationLimitComap`: the components are
  natural in `U`.
* `TauCeti.ValuationSpectrum.presentationLimitComap_id`,
  `TauCeti.ValuationSpectrum.presentationLimitComap_comp`: the components are contravariantly
  functorial in `φ`.
* `TauCeti.ValuationSpectrum.toPresentationLimit_comp_presentationLimitComap`: for complete
  Hausdorff `A` and `B`, the components are compatible with the canonical maps from `A` and `B`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.46, Lemma 8.1 and §8.1.
-/

open CategoryTheory CategoryTheory.Limits Opposite _root_.TopologicalSpace

public section

universe v

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {P : PairOfDefinition A}
  {P' : PairOfDefinition B} {Aplus : Subring A} {Bplus : Subring B}

variable (φ : A →+* B) (hφ : Continuous φ)
  (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
  (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
    (presentationLimitPresheaf P' Bplus))
  {U : Opens ↥(spa Aplus)}

/-! ### Geometric base change into a presentation limit -/

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- A rational open of `Spa(B, B⁺)` inside the preimage `f⁻¹(R(p))` lies over `R(p)`: this is the
hypothesis of the geometric base change `A⟨p⟩ → B⟨m⟩`. -/
private theorem rationalSubset_subset_comap_preimage (p : Presentation P)
    {V : Opens ↥(spa Bplus)}
    (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus p.num p.den))
    (m : PresentationIndex (P := P') Bplus V) :
    rationalSubset Bplus m.pres.num m.pres.den ⊆ comap φ ⁻¹' rationalSubset Aplus p.num p.den :=
  fun w hw ↦ by
    simpa using mem_spaBasicOpen.mp <| Opens.mem_map.mp <|
      hV <| m.le_open <| (mem_spaBasicOpen (v := ⟨w, rationalSubset_subset_spa _ _ _ hw⟩)).mpr hw

/-- The geometric base changes `A⟨p⟩ → B⟨m⟩`, for the indices `m` of an open `V` inside the
preimage of `R(p)`, commute with the restriction morphisms between them. -/
private theorem mapHomOfSubset_comp_restrictionHom (p : Presentation P) {V : Opens ↥(spa Bplus)}
    (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus p.num p.den))
    {m₁ m₂ : PresentationIndex (P := P') Bplus V} (h : m₁ ⟶ m₂) :
    p.mapHomOfSubset φ hφ Aplus Bplus hBplus m₁.pres
        (rationalSubset_subset_comap_preimage φ hφ hplus p hV m₁) ≫
        Presentation.restrictionHom h.le =
      p.mapHomOfSubset φ hφ Aplus Bplus hBplus m₂.pres
        (rationalSubset_subset_comap_preimage φ hφ hplus p hV m₂) :=
  p.hom_ext <| by
    rw [ObjectProperty.FullSubcategory.comp_hom,
      Presentation.toCompletionLocTopHom_comp_mapHomOfSubset_assoc,
      Presentation.toCompletionLocTopHom_comp_restrictionHom,
      Presentation.toCompletionLocTopHom_comp_mapHomOfSubset]

/-- **Geometric base change into a presentation limit**: for an open `V` of `Spa(B, B⁺)` inside the
preimage of `R(p)`, the morphism `A⟨p⟩ → 𝒪_{Spa B}(V)` whose projection to `B⟨m⟩`, for every index
`m` of `V`, is the geometric base change `A⟨p⟩ → B⟨m⟩`. -/
private noncomputable def mapHomOfSubsetToPresentationLimit (p : Presentation P)
    {V : Opens ↥(spa Bplus)}
    (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus p.num p.den)) :
    p.completionLocObj ⟶ presentationLimit (P := P') Bplus V :=
  eqToHom (presentationIndexCone_pt Bplus V _
      (fun m ↦ p.mapHomOfSubset φ hφ Aplus Bplus hBplus m.pres
        (rationalSubset_subset_comap_preimage φ hφ hplus p hV m))
      fun f ↦ mapHomOfSubset_comp_restrictionHom φ hφ hplus hBplus p hV f).symm ≫
    presentationLimitLift Bplus V (presentationIndexCone Bplus V _
      (fun m ↦ p.mapHomOfSubset φ hφ Aplus Bplus hBplus m.pres
        (rationalSubset_subset_comap_preimage φ hφ hplus p hV m))
      fun f ↦ mapHomOfSubset_comp_restrictionHom φ hφ hplus hBplus p hV f)

/-- The geometric base change into a presentation limit projects to the geometric base changes. -/
@[reassoc]
private theorem mapHomOfSubsetToPresentationLimit_comp_πToPresentation (p : Presentation P)
    {V : Opens ↥(spa Bplus)}
    (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus p.num p.den))
    (m : PresentationIndex (P := P') Bplus V) :
    mapHomOfSubsetToPresentationLimit φ hφ hplus hBplus p hV ≫
        presentationLimitπToPresentation Bplus V m =
      p.mapHomOfSubset φ hφ Aplus Bplus hBplus m.pres
        (rationalSubset_subset_comap_preimage φ hφ hplus p hV m) := by
  rw [mapHomOfSubsetToPresentationLimit, Category.assoc]
  exact presentationIndexCone_lift_comp_πToPresentation Bplus V _ _ _ m

/-- The geometric base change into a presentation limit commutes with restriction. -/
@[reassoc]
private theorem mapHomOfSubsetToPresentationLimit_comp_presentationLimitMap (p : Presentation P)
    {V W : Opens ↥(spa Bplus)}
    (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus p.num p.den))
    (h : W ≤ V) :
    mapHomOfSubsetToPresentationLimit (P' := P') φ hφ hplus hBplus p hV ≫ presentationLimitMap h =
      mapHomOfSubsetToPresentationLimit φ hφ hplus hBplus p (h.trans hV) := by
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  rw [Category.assoc, presentationLimitMap_comp_πToPresentation,
    mapHomOfSubsetToPresentationLimit_comp_πToPresentation_assoc,
    mapHomOfSubsetToPresentationLimit_comp_πToPresentation]
  refine p.hom_ext ?_
  rw [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset_assoc,
    Presentation.toCompletionLocTopHom_comp_eqToHom_hom (presentationIndexRestrict_obj_pres h m),
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset]

/-- Projecting `𝒪_{Spa A}(U)` at two indices over whose rational opens `R(q)` lies, and then
applying the geometric base changes to `B⟨q⟩`, gives the same morphism. -/
private theorem presentationLimitπToPresentation_comp_mapHomOfSubset_eq
    {k₁ k₂ : PresentationIndex (P := P) Aplus U} (q : Presentation P')
    (h₁ : rationalSubset Bplus q.num q.den ⊆
      comap φ ⁻¹' rationalSubset Aplus k₁.pres.num k₁.pres.den)
    (h₂ : rationalSubset Bplus q.num q.den ⊆
      comap φ ⁻¹' rationalSubset Aplus k₂.pres.num k₂.pres.den) :
    presentationLimitπToPresentation Aplus U k₁ ≫
        k₁.pres.mapHomOfSubset φ hφ Aplus Bplus hBplus q h₁ =
      presentationLimitπToPresentation Aplus U k₂ ≫
        k₂.pres.mapHomOfSubset φ hφ Aplus Bplus hBplus q h₂ := by
  -- both agree with the base change out of the common refinement of `k₁` and `k₂`
  have h : rationalSubset Bplus q.num q.den ⊆ comap φ ⁻¹' rationalSubset Aplus
      (k₁.commonRefinement k₂).pres.num (k₁.commonRefinement k₂).pres.den := by
    rw [PresentationIndex.commonRefinement_pres, rationalSubset_commonRefinement]
    exact fun w hw ↦ ⟨h₁ hw, h₂ hw⟩
  have hf (k : PresentationIndex (P := P) Aplus U)
      (hk : rationalSubset Bplus q.num q.den ⊆
        comap φ ⁻¹' rationalSubset Aplus k.pres.num k.pres.den) :
      k.pres.toCompletionLocTopHom ≫ (k.pres.mapHomOfSubset φ hφ Aplus Bplus hBplus q hk).hom =
        (⟨φ, hφ⟩ : _root_.TopCommRingCat.of A ⟶ _root_.TopCommRingCat.of B) ≫
          q.toCompletionLocTopHom :=
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset φ hφ Aplus Bplus hBplus _ q hk
  exact (presentationLimitπToPresentation_comp_eq (k₁.le_commonRefinement_left k₂)
    ((hf k₁ h₁).trans (hf _ h).symm)).trans
    (presentationLimitπToPresentation_comp_eq (k₁.le_commonRefinement_right k₂)
      ((hf k₂ h₂).trans (hf _ h).symm)).symm

/-! ### The components on the preimages of rational opens -/

/-- **The index of `f⁻¹U` induced by an index `i` of `U`**, when `φ` carries open ideals to open
ideals: the presentation `(φ(T), φ(s))` of the rational open `f⁻¹(R(T/s)) = R(φ(T)/φ(s))`, for
`R(T/s)` the rational open presented by `i`. This is `PresentationIndex.map` for the preimage of `U`
itself. -/
noncomputable abbrev PresentationIndex.comap (i : PresentationIndex (P := P) Aplus U) :
    PresentationIndex (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U) :=
  i.map φ hφ hopen hplus fun _ hw ↦ Opens.mem_map.mpr hw

/-- The leg at an index `i` of `U`: project to `A⟨i⟩`, then apply the geometric base change into
`𝒪_{Spa B}(f⁻¹(R(i)))`. -/
private noncomputable def presentationLimitComapLeg (i : PresentationIndex (P := P) Aplus U) :
    presentationLimit (P := P) Aplus U ⟶ presentationLimit (P := P') Bplus
      ((Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus i.pres.num i.pres.den)) :=
  presentationLimitπToPresentation Aplus U i ≫
    mapHomOfSubsetToPresentationLimit φ hφ hplus hBplus i.pres le_rfl

/-- The legs agree on overlaps: on an open `W ⊆ f⁻¹(R(i)) ∩ f⁻¹(R(j))` both restrict to the
projections followed by the geometric base changes. -/
private theorem presentationLimitComapLeg_comp_presentationLimitMap
    {i j : PresentationIndex (P := P) Aplus U} {W : Opens ↥(spa Bplus)}
    (a : W ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj
      (spaBasicOpen Aplus i.pres.num i.pres.den))
    (b : W ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj
      (spaBasicOpen Aplus j.pres.num j.pres.den)) :
    presentationLimitComapLeg (P' := P') φ hφ hplus hBplus i ≫ presentationLimitMap a =
      presentationLimitComapLeg φ hφ hplus hBplus j ≫ presentationLimitMap b := by
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  simp only [presentationLimitComapLeg, Category.assoc,
    mapHomOfSubsetToPresentationLimit_comp_presentationLimitMap_assoc,
    mapHomOfSubsetToPresentationLimit_comp_πToPresentation]
  exact presentationLimitπToPresentation_comp_mapHomOfSubset_eq φ hφ hBplus _ _ _

omit [IsTopologicalRing B] in
variable (U) in
/-- The opens `f⁻¹(R(i))`, for `i` ranging over the indices of `U`, cover `f⁻¹U`. -/
private theorem ofArrows_mem_grothendieckTopology :
    Sieve.ofArrows (fun i : PresentationIndex (P := P) Aplus U ↦
        (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus i.pres.num i.pres.den))
      (fun i ↦ homOfLE ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open)) ∈
      Opens.grothendieckTopology ↥(spa Bplus) ((Opens.map (spaComapTopHom φ hφ hplus)).obj U) := by
  intro w hw
  obtain ⟨i, hi⟩ := exists_presentationIndex_mem (P := P) (Opens.mem_map.mp hw)
  exact ⟨_, homOfLE ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open),
    Sieve.ofArrows_mk _ _ i, Opens.mem_map.mpr hi⟩

variable (U) in
/-- The legs, read as sections of the structure presheaf of `Spa(B, B⁺)`, agree on overlaps. -/
private theorem presentationLimitComapLeg_compatible ⦃W : Opens ↥(spa Bplus)⦄
    ⦃i j : PresentationIndex (P := P) Aplus U⦄
    (a : W ⟶ (Opens.map (spaComapTopHom φ hφ hplus)).obj
      (spaBasicOpen Aplus i.pres.num i.pres.den))
    (b : W ⟶ (Opens.map (spaComapTopHom φ hφ hplus)).obj
      (spaBasicOpen Aplus j.pres.num j.pres.den)) :
    (presentationLimitComapLeg (P' := P') φ hφ hplus hBplus i ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm) ≫
      (presentationLimitPresheaf P' Bplus).map a.op =
    (presentationLimitComapLeg (P' := P') φ hφ hplus hBplus j ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm) ≫
      (presentationLimitPresheaf P' Bplus).map b.op := by
  simp only [presentationLimitPresheaf_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [reassoc_of% presentationLimitComapLeg_comp_presentationLimitMap φ hφ hplus hBplus a.le b.le]

/-! ### The glued morphism -/

variable (U) in
/-- **The component at `U` of the morphism `𝒪_{Spa A} → f_* 𝒪_{Spa B}` induced by `φ`**, for
`𝒪_{Spa B}` a sheaf: the morphism `𝒪_{Spa A}(U) → 𝒪_{Spa B}(f⁻¹U)` whose restriction to a rational
open `R(q)` inside `f⁻¹(R(i))`, for an index `i` of `U`, is the projection to `A⟨i⟩` followed by the
geometric base change `A⟨i⟩ → B⟨q⟩` of `φ` (`presentationLimitComap_comp_map_comp_π_of_subset`). It
is obtained by gluing these base changes along the cover of `f⁻¹U` by the opens `f⁻¹(R(i))`. -/
noncomputable def presentationLimitComap :
    presentationLimit (P := P) Aplus U ⟶
      presentationLimit (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U) :=
  hsheaf.amalgamateOfArrows
    (fun i : PresentationIndex (P := P) Aplus U ↦
      homOfLE ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open))
    (ofArrows_mem_grothendieckTopology φ hφ hplus U)
    (fun i ↦ presentationLimitComapLeg φ hφ hplus hBplus i ≫
      eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm)
    (fun _ _ _ a b _ ↦ presentationLimitComapLeg_compatible φ hφ hplus hBplus U a b) ≫
  eqToHom (presentationLimitPresheaf_obj P' Bplus _)

/-- The component at `U`, restricted to the open `f⁻¹(R(i))`, is the leg at `i`. -/
@[reassoc]
private theorem presentationLimitComap_comp_map_le_open (i : PresentationIndex (P := P) Aplus U) :
    presentationLimitComap φ hφ hplus hBplus hsheaf U ≫
        presentationLimitMap ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open) =
      presentationLimitComapLeg φ hφ hplus hBplus i := by
  rw [← cancel_mono (eqToHom (presentationLimitPresheaf_obj P' Bplus (op
    ((Opens.map (spaComapTopHom φ hφ hplus)).obj
      (spaBasicOpen Aplus i.pres.num i.pres.den)))).symm)]
  have := hsheaf.amalgamateOfArrows_map
    (fun i : PresentationIndex (P := P) Aplus U ↦
      homOfLE ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open))
    (ofArrows_mem_grothendieckTopology φ hφ hplus U)
    (fun i ↦ presentationLimitComapLeg φ hφ hplus hBplus i ≫
      eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm)
    (fun _ _ _ a b _ ↦ presentationLimitComapLeg_compatible φ hφ hplus hBplus U a b) i
  simp only [presentationLimitPresheaf_map] at this
  simpa only [presentationLimitComap, Category.assoc] using this

include hsheaf in
/-- **Morphisms into `𝒪_{Spa B}(f⁻¹U)` are determined by their restrictions to the opens
`f⁻¹(R(i))`**, `i` ranging over the indices of `U`: these opens cover `f⁻¹U` and `𝒪_{Spa B}` is a
sheaf. -/
theorem presentationLimit_hom_ext_of_isSheaf {X : CompleteSeparatedTopCommRingCat.{v}}
    {g₁ g₂ : X ⟶
      presentationLimit (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U)}
    (h : ∀ i : PresentationIndex (P := P) Aplus U,
      g₁ ≫ presentationLimitMap ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open) =
        g₂ ≫ presentationLimitMap ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open)) :
    g₁ = g₂ := by
  rw [← cancel_mono (eqToHom (presentationLimitPresheaf_obj P' Bplus
    (op ((Opens.map (spaComapTopHom φ hφ hplus)).obj U))).symm)]
  refine Presheaf.IsSheaf.hom_ext_ofArrows hsheaf
    (fun i : PresentationIndex (P := P) Aplus U ↦
      homOfLE ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open))
    (ofArrows_mem_grothendieckTopology φ hφ hplus U) fun i ↦ ?_
  simp only [presentationLimitPresheaf_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Category.assoc, h i, Category.assoc]

include hsheaf in
/-- **Morphisms into `𝒪_{Spa B}(f⁻¹U)` are determined by their restrictions to the rational opens
`f⁻¹(R(i)) = R(φ(i))`**, when `φ` carries open ideals to open ideals, `i` ranging over the indices
of `U`. -/
theorem presentationLimit_hom_ext_of_isSheaf_comap {X : CompleteSeparatedTopCommRingCat.{v}}
    {g₁ g₂ : X ⟶
      presentationLimit (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U)}
    (h : ∀ i : PresentationIndex (P := P) Aplus U,
      g₁ ≫ presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open =
        g₂ ≫ presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open) :
    g₁ = g₂ := by
  refine presentationLimit_hom_ext_of_isSheaf (P := P) φ hφ hplus hsheaf fun i ↦ ?_
  -- restricting to `f⁻¹(R(i))` is restricting to `R(φ(i))` and transporting along their equality
  have e := (PresentationIndex.spaBasicOpen_map_pres (P' := P') φ hφ hopen hplus
    (V := (Opens.map (spaComapTopHom φ hφ hplus)).obj U) (fun _ hw ↦ Opens.mem_map.mpr hw) i).ge
  rw [← presentationLimitMap_comp (i.comap (P' := P') φ hφ hopen hplus).le_open e,
    ← Category.assoc, h i, Category.assoc]

/-- **On a rational open the morphism is the geometric base change**: for an open `V ⊆ f⁻¹U` and an
index `m` of `V` whose rational open lies over the rational open `R(i)` of an index `i` of `U`, the
component at `U`, restricted to `V` and followed by the projection at `m`, is the projection at `i`
followed by the geometric base change `A⟨i⟩ → B⟨m⟩` of `φ`. -/
theorem presentationLimitComap_comp_map_comp_π_of_subset (i : PresentationIndex (P := P) Aplus U)
    {V : Opens ↥(spa Bplus)} (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj U)
    (m : PresentationIndex (P := P') Bplus V)
    (hm : rationalSubset Bplus m.pres.num m.pres.den ⊆
      comap φ ⁻¹' rationalSubset Aplus i.pres.num i.pres.den) :
    presentationLimitComap φ hφ hplus hBplus hsheaf U ≫ presentationLimitMap hV ≫
        presentationLimitπToPresentation Bplus V m =
      presentationLimitπToPresentation Aplus U i ≫
        i.pres.mapHomOfSubset φ hφ Aplus Bplus hBplus m.pres hm := by
  -- `m` as an index of `f⁻¹(R(i))`; restricting to `V` or to `f⁻¹(R(i))` and projecting at `m` are
  -- the same projection of the limit on `f⁻¹U`
  let m' : PresentationIndex (P := P') Bplus
      ((Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus i.pres.num i.pres.den)) :=
    ⟨m.pres, m.isOpen_span, fun w hw ↦ Opens.mem_map.mpr (mem_spaBasicOpen.mpr
      (by simpa using hm (mem_spaBasicOpen.mp hw)))⟩
  have e : (presentationIndexRestrict hV).obj m =
      (presentationIndexRestrict
        ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open)).obj m' :=
    PresentationIndex.ext
      (by rw [presentationIndexRestrict_obj_pres, presentationIndexRestrict_obj_pres])
  rw [presentationLimitMap_comp_πToPresentation,
    presentationLimitπToPresentation_comp_eqToHom_congr e _
      (congrArg Presentation.completionLocObj (presentationIndexRestrict_obj_pres _ m')),
    ← presentationLimitMap_comp_πToPresentation,
    presentationLimitComap_comp_map_le_open_assoc, presentationLimitComapLeg, Category.assoc,
    mapHomOfSubsetToPresentationLimit_comp_πToPresentation]

/-- **On a rational open the morphism is the base change**, when `φ` carries open ideals to open
ideals: for an open `V ⊆ f⁻¹U` and an index `m` of `V` whose rational open lies in `R(φ(i))` for an
index `i` of `U`, the component at `U`, restricted to `V` and followed by the projection at `m`, is
the projection at `i`, the base change `A⟨i⟩ → B⟨φ(i)⟩` of `φ` and the comparison morphism
`B⟨φ(i)⟩ → B⟨m⟩`. -/
theorem presentationLimitComap_comp_map_comp_π_of_le (i : PresentationIndex (P := P) Aplus U)
    {V : Opens ↥(spa Bplus)} (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj U)
    (m : PresentationIndex (P := P') Bplus V)
    (hm : rationalSubset Bplus m.pres.num m.pres.den ⊆ rationalSubset Bplus
      (i.comap (P' := P') φ hφ hopen hplus).pres.num
      (i.comap (P' := P') φ hφ hopen hplus).pres.den) :
    presentationLimitComap φ hφ hplus hBplus hsheaf U ≫ presentationLimitMap hV ≫
        presentationLimitπToPresentation Bplus V m =
      presentationLimitπToPresentation Aplus U i ≫
        Presentation.mapHom φ hφ i.pres _ (PresentationIndex.map_pres_den φ hφ hopen hplus _ i)
          (fun t ht ↦ by
            classical
            rw [PresentationIndex.map_pres_num]
            exact Finset.mem_image_of_mem φ ht) ≫
        homOfRationalSubsetSubset Bplus hBplus hm := by
  -- `R(φ(i))` is the preimage of `R(i)`
  have hm' : rationalSubset Bplus m.pres.num m.pres.den ⊆
      comap φ ⁻¹' rationalSubset Aplus i.pres.num i.pres.den :=
    rationalSubset_subset_comap_preimage φ hφ hplus i.pres
      ((spaBasicOpen_le_spaBasicOpen_iff.mpr hm).trans
        (PresentationIndex.spaBasicOpen_map_pres φ hφ hopen hplus _ i).le)
      ⟨m.pres, m.isOpen_span, le_rfl⟩
  rw [presentationLimitComap_comp_map_comp_π_of_subset φ hφ hplus hBplus hsheaf i hV m hm']
  -- both base changes are the structure map `A → B⟨m⟩` through `φ`
  refine congrArg (presentationLimitπToPresentation Aplus U i ≫ ·) (i.pres.hom_ext ?_)
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset,
    Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
    toCompletionLocTopHom_comp_homOfRationalSubsetSubset hBplus]

/-- **On a rational open the morphism is the base change**, when `φ` carries open ideals to open
ideals: the component at `U`, restricted to the open `f⁻¹(R(i)) = R(φ(i))` for an index `i` of `U`
and followed by the projection at an index `m` of that open, is the projection at `i`, the base
change `A⟨i⟩ → B⟨φ(i)⟩` of `φ` and the comparison morphism `B⟨φ(i)⟩ → B⟨m⟩`. -/
theorem presentationLimitComap_comp_map_comp_π (i : PresentationIndex (P := P) Aplus U)
    (m : PresentationIndex (P := P') Bplus (spaBasicOpen Bplus
      (i.comap (P' := P') φ hφ hopen hplus).pres.num
      (i.comap (P' := P') φ hφ hopen hplus).pres.den)) :
    presentationLimitComap φ hφ hplus hBplus hsheaf U ≫
        presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open ≫
        presentationLimitπToPresentation Bplus _ m =
      presentationLimitπToPresentation Aplus U i ≫
        Presentation.mapHom φ hφ i.pres _ (PresentationIndex.map_pres_den φ hφ hopen hplus _ i)
          (fun t ht ↦ by
            classical
            rw [PresentationIndex.map_pres_num]
            exact Finset.mem_image_of_mem φ ht) ≫
        homOfRationalSubsetSubset Bplus hBplus (m.rationalSubset_subset le_rfl) :=
  presentationLimitComap_comp_map_comp_π_of_le φ hφ hopen hplus hBplus hsheaf i _ m _

/-- **On a rational open the morphism is the base change**, in terms of the identification
`presentationLimitRationalIso` of `𝒪_{Spa B}(R(φ(i)))` with `B⟨φ(i)⟩`, when `φ` carries open ideals
to open ideals: the component at `U`, restricted to `f⁻¹(R(i)) = R(φ(i))`, is the projection at `i`
followed by the base change `A⟨i⟩ → B⟨φ(i)⟩` of `φ`. -/
theorem presentationLimitComap_comp_map_comp_hom (i : PresentationIndex (P := P) Aplus U) :
    presentationLimitComap φ hφ hplus hBplus hsheaf U ≫
        presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open ≫
        (presentationLimitRationalIso Bplus hBplus _
          (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).hom =
      presentationLimitπToPresentation Aplus U i ≫
        Presentation.mapHom φ hφ i.pres _ (PresentationIndex.map_pres_den φ hφ hopen hplus _ i)
          (fun t ht ↦ by
            classical
            rw [PresentationIndex.map_pres_num]
            exact Finset.mem_image_of_mem φ ht) := by
  rw [presentationLimitRationalIso_hom, presentationLimitComap_comp_map_comp_π,
    homOfRationalSubsetSubset_self, Category.comp_id]

/-! ### Naturality -/

/-- **The components are natural in `U`**: restricting along `U' ≤ U` and then applying the
component at `U'` is applying the component at `U` and restricting along `f⁻¹U' ≤ f⁻¹U`. -/
@[reassoc]
theorem presentationLimitMap_comp_presentationLimitComap {U' : Opens ↥(spa Aplus)} (h : U' ≤ U) :
    presentationLimitMap (P := P) h ≫ presentationLimitComap φ hφ hplus hBplus hsheaf U' =
      presentationLimitComap φ hφ hplus hBplus hsheaf U ≫
        presentationLimitMap ((Opens.map (spaComapTopHom φ hφ hplus)).monotone h) := by
  refine presentationLimit_hom_ext_of_isSheaf (P := P) φ hφ hplus hsheaf fun i ↦ ?_
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  have hm := rationalSubset_subset_comap_preimage φ hφ hplus i.pres le_rfl m
  have hm' : rationalSubset Bplus m.pres.num m.pres.den ⊆ comap φ ⁻¹' rationalSubset Aplus
      ((presentationIndexRestrict h).obj i).pres.num
      ((presentationIndexRestrict h).obj i).pres.den := by
    rw [presentationIndexRestrict_obj_pres]
    exact hm
  -- the left side is the projection at `i`, read as an index of `U`, followed by the geometric
  -- base change to `B⟨m⟩`
  simp only [Category.assoc, reassoc_of% presentationLimitMap_comp]
  rw [presentationLimitComap_comp_map_comp_π_of_subset φ hφ hplus hBplus hsheaf i _ m hm,
    reassoc_of% presentationLimitMap_comp_πToPresentation,
    presentationLimitComap_comp_map_comp_π_of_subset φ hφ hplus hBplus hsheaf
      ((presentationIndexRestrict h).obj i) _ m hm']
  -- both base changes are the structure map `A → B⟨m⟩` through `φ`
  refine congrArg (presentationLimitπToPresentation Aplus U _ ≫ ·)
    (((presentationIndexRestrict h).obj i).pres.hom_ext ?_)
  rw [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_eqToHom_hom_assoc
      (presentationIndexRestrict_obj_pres h i),
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset,
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset]

/-! ### The morphism of presheaves -/

/-- **The morphism of structure presheaves `𝒪_{Spa A} ⟶ f_* 𝒪_{Spa B}` induced by `φ`**, for
`𝒪_{Spa B}` a sheaf: Wedhorn §8.1's `f♭`, with the components `presentationLimitComap`. -/
noncomputable def presentationLimitPresheafComap :
    presentationLimitPresheaf P Aplus ⟶
      (TopCat.Presheaf.pushforward _ (spaComapTopHom φ hφ hplus)).obj
        (presentationLimitPresheaf P' Bplus) where
  app U := eqToHom (presentationLimitPresheaf_obj P Aplus U) ≫
    presentationLimitComap φ hφ hplus hBplus hsheaf U.unop ≫
    eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm
  naturality U U' g := by
    simp only [presentationLimitPresheaf_map, TopCat.Presheaf.pushforward_obj_map, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [presentationLimitMap_comp_presentationLimitComap_assoc]

/-- The component of `presentationLimitPresheafComap` at an open is `presentationLimitComap`,
transported along the evaluation equations of the two presheaves. -/
@[simp]
theorem presentationLimitPresheafComap_app (U : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheafComap φ hφ hplus hBplus hsheaf).app U =
      eqToHom (presentationLimitPresheaf_obj P Aplus U) ≫
        presentationLimitComap φ hφ hplus hBplus hsheaf U.unop ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm :=
  (rfl)

/-! ### Functoriality -/

variable (U) in
/-- **The identity induces the identity**: for `φ` the identity of `A`, the component at `U` is
the restriction along the equality `id⁻¹U = U`. -/
theorem presentationLimitComap_id (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    presentationLimitComap (P := P) (P' := P) (RingHom.id A) continuous_id (fun _ ha ↦ ha) hAplus
        hsheafA U =
      presentationLimitMap (P := P) (map_spaComapTopHom_id_obj U).le := by
  refine presentationLimit_hom_ext_of_isSheaf (P := P) (RingHom.id A) continuous_id
    (fun _ ha ↦ ha) hsheafA fun i ↦ ?_
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  have hm := rationalSubset_subset_comap_preimage (P := P) (P' := P) (RingHom.id A) continuous_id
    (fun _ ha ↦ ha) i.pres le_rfl m
  rw [Category.assoc, presentationLimitComap_comp_map_comp_π_of_subset _ _ _ _ _ i _ m hm,
    presentationLimitMap_comp, presentationLimitMap_comp_πToPresentation]
  -- both sides are a projection followed by the structure map `A → A⟨m⟩`
  refine (presentationLimitπToPresentation_comp_eq_of_subset hAplus ?_ ?_).symm
  · rw [presentationIndexRestrict_obj_pres]
    simpa using hm
  · rw [Presentation.toCompletionLocTopHom_comp_eqToHom_hom
        (presentationIndexRestrict_obj_pres _ m),
      Presentation.toCompletionLocTopHom_comp_mapHomOfSubset]
    -- `⟨RingHom.id A, _⟩` is the identity of `TopCommRingCat.of A`
    rfl

/-- **The identity induces the identity morphism of structure presheaves**, up to the transport
along `spaComapTopHom_id`. -/
theorem presentationLimitPresheafComap_id (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    presentationLimitPresheafComap (P := P) (P' := P) (RingHom.id A) continuous_id
        (fun _ ha ↦ ha) hAplus hsheafA ≫
      Functor.whiskerRight (eqToHom (congrArg (fun f ↦ (Opens.map f).op) spaComapTopHom_id))
        (presentationLimitPresheaf P Aplus) =
      𝟙 _ := by
  refine NatTrans.ext (funext fun U ↦ ?_)
  simp only [NatTrans.comp_app, presentationLimitPresheafComap_app, Functor.whiskerRight_app,
    eqToHom_app, presentationLimitPresheaf_map, presentationLimitComap_id, NatTrans.id_app]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    reassoc_of% presentationLimitMap_comp]
  -- the remaining restriction is along `𝟙⁻¹U = U`, a transport
  have e := (congrArg unop (Opens.op_map_id_obj (X := TopCat.of ↥(spa Aplus)) U)).symm
  rw [← eqToHom_presentationLimit e (congrArg _ e)]
  simp only [eqToHom_trans]
  -- `𝟙⁻¹U` is definitionally `U`
  exact eqToHom_refl _ _

section Comp

variable {C : Type v} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  {P'' : PairOfDefinition C} {Cplus : Subring C} (ψ : B →+* C) (hψ : Continuous ψ)
  (hplus' : ∀ b ∈ Bplus, ψ b ∈ Cplus) (hCplus : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c)
  (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Cplus))
    (presentationLimitPresheaf P'' Cplus))

/-- The geometric base change along `φ` into `𝒪_{Spa B}(f⁻¹(R(p)))`, followed by the component at
`f⁻¹(R(p))` of the morphism induced by `ψ`, is the geometric base change along `ψ ∘ φ`, on the
preimage of `R(p)` under `Spa(C, C⁺) → Spa(B, B⁺)`. -/
private theorem mapHomOfSubsetToPresentationLimit_comp_presentationLimitComap (p : Presentation P)
    (hV : (Opens.map (spaComapTopHom ψ hψ hplus')).obj
        ((Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus p.num p.den)) ≤
      (Opens.map (spaComapTopHom (ψ.comp φ) (hψ.comp hφ) fun a ha ↦ hplus' (φ a) (hplus a ha))).obj
        (spaBasicOpen Aplus p.num p.den)) :
    mapHomOfSubsetToPresentationLimit (P' := P') φ hφ hplus hBplus p le_rfl ≫
        presentationLimitComap (P := P') (P' := P'') ψ hψ hplus' hCplus hsheaf' _ =
      mapHomOfSubsetToPresentationLimit (P' := P'') (ψ.comp φ) (hψ.comp hφ)
        (fun a ha ↦ hplus' (φ a) (hplus a ha)) hCplus p hV := by
  refine presentationLimit_hom_ext_of_isSheaf (P := P') ψ hψ hplus' hsheaf' fun j ↦ ?_
  refine presentationLimit_hom_ext_toPresentation fun n ↦ ?_
  simp only [Category.assoc]
  rw [presentationLimitComap_comp_map_le_open_assoc]
  simp only [presentationLimitComapLeg, Category.assoc]
  rw [mapHomOfSubsetToPresentationLimit_comp_πToPresentation_assoc,
    mapHomOfSubsetToPresentationLimit_comp_πToPresentation,
    mapHomOfSubsetToPresentationLimit_comp_presentationLimitMap_assoc,
    mapHomOfSubsetToPresentationLimit_comp_πToPresentation]
  -- both sides are the structure map `A → C⟨n⟩` through `ψ ∘ φ`
  refine p.hom_ext ?_
  rw [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset_assoc,
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset,
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset]
  -- `⟨ψ.comp φ, _⟩` is the composite of `⟨φ, hφ⟩` and `⟨ψ, hψ⟩` in `TopCommRingCat`
  rfl

variable (U) in
/-- **The morphisms are contravariantly functorial**: the component at `U` of the morphism induced
by `ψ ∘ φ` is the component at `U` of the morphism induced by `φ`, followed by the component at
`φ⁻¹U` of the morphism induced by `ψ` and the restriction along `(ψ ∘ φ)⁻¹U = ψ⁻¹(φ⁻¹U)`. -/
theorem presentationLimitComap_comp :
    presentationLimitComap (P := P) (P' := P'') (ψ.comp φ) (hψ.comp hφ)
        (fun a ha ↦ hplus' (φ a) (hplus a ha)) hCplus hsheaf' U =
      presentationLimitComap (P := P) (P' := P') φ hφ hplus hBplus hsheaf U ≫
        presentationLimitComap (P := P') (P' := P'') ψ hψ hplus' hCplus hsheaf' _ ≫
        presentationLimitMap (P := P'')
          (map_spaComapTopHom_comp_obj φ hφ hplus hψ hplus' U).le := by
  refine presentationLimit_hom_ext_of_isSheaf (P := P) (ψ.comp φ) (hψ.comp hφ)
    (fun a ha ↦ hplus' (φ a) (hplus a ha)) hsheaf' fun i ↦ ?_
  -- the preimage of `R(i)` under `ψ ∘ φ` is its preimage under `φ`, then under `ψ`
  have e := map_spaComapTopHom_comp_obj φ hφ hplus hψ hplus'
    (spaBasicOpen Aplus i.pres.num i.pres.den)
  -- on the right, restrict to `φ⁻¹(R(i))` before applying the morphism induced by `ψ`
  simp only [Category.assoc, presentationLimitMap_comp]
  rw [← presentationLimitMap_comp ((Opens.map (spaComapTopHom ψ hψ hplus')).monotone
      ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open)) e.le,
    ← presentationLimitMap_comp_presentationLimitComap_assoc ψ hψ hplus' hCplus hsheaf'
      ((Opens.map (spaComapTopHom φ hφ hplus)).monotone i.le_open),
    presentationLimitComap_comp_map_le_open_assoc, presentationLimitComap_comp_map_le_open,
    presentationLimitComapLeg, presentationLimitComapLeg, Category.assoc,
    reassoc_of% mapHomOfSubsetToPresentationLimit_comp_presentationLimitComap φ hφ hplus hBplus
      ψ hψ hplus' hCplus hsheaf' i.pres e.ge,
    mapHomOfSubsetToPresentationLimit_comp_presentationLimitMap]

/-- **The morphisms of structure presheaves are contravariantly functorial**: the morphism induced
by `ψ ∘ φ` is the morphism induced by `φ` followed by the pushforward of the morphism induced by
`ψ`, up to the transport along `spaComapTopHom_comp`. -/
theorem presentationLimitPresheafComap_comp :
    presentationLimitPresheafComap (P := P) (P' := P'') (ψ.comp φ) (hψ.comp hφ)
        (fun a ha ↦ hplus' (φ a) (hplus a ha)) hCplus hsheaf' ≫
      Functor.whiskerRight (eqToHom (congrArg (fun f ↦ (Opens.map f).op)
        (spaComapTopHom_comp φ hφ hplus hψ hplus'))) (presentationLimitPresheaf P'' Cplus) =
      presentationLimitPresheafComap (P := P) (P' := P') φ hφ hplus hBplus hsheaf ≫
        (TopCat.Presheaf.pushforward _ (spaComapTopHom φ hφ hplus)).map
          (presentationLimitPresheafComap (P := P') (P' := P'') ψ hψ hplus' hCplus hsheaf') := by
  refine NatTrans.ext (funext fun U ↦ ?_)
  simp only [NatTrans.comp_app, presentationLimitPresheafComap_app, Functor.whiskerRight_app,
    eqToHom_app, presentationLimitPresheaf_map, TopCat.Presheaf.pushforward_map_app']
  rw [presentationLimitComap_comp φ hφ hplus hBplus hsheaf (unop U) ψ hψ hplus' hCplus hsheaf']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    reassoc_of% presentationLimitMap_comp]
  -- the remaining restriction is along `ψ⁻¹(φ⁻¹U) = (ψ ≫ φ)⁻¹U`, a transport
  have e : (Opens.map (spaComapTopHom ψ hψ hplus')).obj
      ((Opens.map (spaComapTopHom φ hφ hplus)).obj U.unop) =
      ((Opens.map (spaComapTopHom ψ hψ hplus' ≫ spaComapTopHom φ hφ hplus)).op.obj U).unop :=
    (rfl)
  rw [← eqToHom_presentationLimit e (congrArg _ e)]
  simp only [eqToHom_trans]
  -- both final transports have the same source and target, up to `unop_op`
  rfl

end Comp

/-! ### Compatibility with the canonical maps from the coefficient rings -/

section Canonical

variable {A B : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B] {P : PairOfDefinition A}
  {P' : PairOfDefinition B} {Aplus : Subring A} {Bplus : Subring B}
  (φ : A →+* B) (hφ : Continuous φ)
  (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
    (presentationLimitPresheaf P' Bplus))

/-- **The induced morphism is compatible with the canonical maps from `A` and `B`**: for complete
Hausdorff `A` and `B`, the component at `U` sends the image of `a ∈ A` in `𝒪_{Spa A}(U)` to the
image of `φ(a)` in `𝒪_{Spa B}(f⁻¹U)`. -/
@[reassoc]
theorem toPresentationLimit_comp_presentationLimitComap (U : Opens ↥(spa Aplus)) :
    toPresentationLimit (P := P) Aplus U ≫
        presentationLimitComap φ hφ hplus hBplus hsheaf U =
      ObjectProperty.homMk (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A) ≫
          (⟨φ, hφ⟩ : _root_.TopCommRingCat.of A ⟶ _root_.TopCommRingCat.of B) ≫
          eqToHom (CompleteSeparatedTopCommRingCat.of_obj B).symm) ≫
        toPresentationLimit Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U) := by
  refine presentationLimit_hom_ext_of_isSheaf (P := P) φ hφ hplus hsheaf fun i ↦ ?_
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  simp only [Category.assoc]
  rw [presentationLimitComap_comp_map_comp_π_of_subset φ hφ hplus hBplus hsheaf i _ m
    (rationalSubset_subset_comap_preimage φ hφ hplus i.pres le_rfl m)]
  simp only [toPresentationLimit_comp_presentationLimitMap_assoc,
    toPresentationLimit_comp_πToPresentation_assoc, toPresentationLimit_comp_πToPresentation]
  -- both sides are morphisms out of `A`; compare them as structure maps followed by base change
  have eA (p : Presentation P) : p.toCompletionLocObjHom.hom =
      eqToHom (CompleteSeparatedTopCommRingCat.of_obj A) ≫ p.toCompletionLocTopHom := by
    rw [Presentation.toCompletionLocObjHom_hom, Presentation.toCompletionLocTopHom_eq]
  have eB (p : Presentation P') : p.toCompletionLocObjHom.hom =
      eqToHom (CompleteSeparatedTopCommRingCat.of_obj B) ≫ p.toCompletionLocTopHom := by
    rw [Presentation.toCompletionLocObjHom_hom, Presentation.toCompletionLocTopHom_eq]
  apply InducedCategory.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, eA, eB, Category.assoc,
    Presentation.toCompletionLocTopHom_comp_mapHomOfSubset, ObjectProperty.homMk_hom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end Canonical

end TauCeti.ValuationSpectrum

end
