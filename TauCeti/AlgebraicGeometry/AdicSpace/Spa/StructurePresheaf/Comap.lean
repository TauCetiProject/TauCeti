/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.BaseChange

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Cofinality

/-!
# The morphism of structure presheaves induced by a homomorphism of Huber pairs

Let `φ : A → B` be a continuous ring homomorphism of topological rings with pairs of definition
`P` and `P'` and subrings `A⁺ ⊆ A` and `B⁺ ⊆ B`, carrying `A⁺` into `B⁺` and open ideals to open
ideals, and let `f : Spa(B, B⁺) → Spa(A, A⁺)` be the induced map of adic spectra. Following
Wedhorn §8.1, on a rational open `R(T/s)` of `Spa(A, A⁺)` the structure presheaf has the value
`A⟨T/s⟩`, the preimage `f⁻¹(R(T/s)) = R(φ(T)/φ(s))` is a rational open of `Spa(B, B⁺)` with value
`B⟨φ(T)/φ(s)⟩`, and the base changes `A⟨T/s⟩ → B⟨φ(T)/φ(s)⟩` of `φ` form a morphism of presheaves on
the rational opens. To extend it to a morphism `𝒪_{Spa A} → f_* 𝒪_{Spa B}` on all opens, the base
changes on the rational opens `R(T/s) ⊆ U` have to be assembled into a map into `𝒪_{Spa B}(f⁻¹U)`.
The opens `f⁻¹(R(T/s))` cover `f⁻¹U`, so this is possible when `𝒪_{Spa B}` is a sheaf, which is the
case treated here. (The image under `f` of a rational open of `f⁻¹U` need not lie in a rational open
of `U`, so the limit description of `𝒪_{Spa B}(f⁻¹U)` alone does not provide the map.)

This is the presheaf half of Wedhorn's construction of the morphism of pre-adic spaces
`Spa(φ) : Spa(B, B⁺) → Spa(A, A⁺)`; the compatibility with the stalk valuations is not treated
here.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitComap`: the component at an open `U` of
  `Spa(A, A⁺)`, a morphism `𝒪_{Spa A}(U) ⟶ 𝒪_{Spa B}(f⁻¹U)`.
* `TauCeti.ValuationSpectrum.presentationLimitPresheafComap`: the morphism of presheaves
  `𝒪_{Spa A} ⟶ f_* 𝒪_{Spa B}`.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitComap_comp_map_comp_π`: on the rational open
  `f⁻¹(R(T/s)) = R(φ(T)/φ(s))` the morphism is the base change `A⟨T/s⟩ → B⟨φ(T)/φ(s)⟩`.
* `TauCeti.ValuationSpectrum.presentationLimit_hom_ext_of_isSheaf`: morphisms into
  `𝒪_{Spa B}(f⁻¹U)` are determined by their restrictions to the opens `f⁻¹(R(T/s))` for the
  rational opens `R(T/s) ⊆ U`.
* `TauCeti.ValuationSpectrum.presentationLimitMap_comp_presentationLimitComap`: the components are
  natural in `U`.
* `TauCeti.ValuationSpectrum.presentationLimitComap_id`,
  `TauCeti.ValuationSpectrum.presentationLimitComap_comp`: the components are contravariantly
  functorial in `φ`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.46 and §8.1.
-/

open CategoryTheory CategoryTheory.Limits Opposite _root_.TopologicalSpace

public section

universe v

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {P : PairOfDefinition A}
  {P' : PairOfDefinition B} {Aplus : Subring A} {Bplus : Subring B}

/-! ### The components on the rational opens -/

variable (φ : A →+* B) (hφ : Continuous φ)
  (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
  (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
    (presentationLimitPresheaf P' Bplus))
  {U : Opens ↥(spa Aplus)}

/-- **The index of `f⁻¹U` induced by an index `i` of `U`**: the presentation `(φ(T), φ(s))` of the
rational open `f⁻¹(R(T/s)) = R(φ(T)/φ(s))`, for `R(T/s)` the rational open presented by `i`. This is
`PresentationIndex.map` for the preimage of `U` itself. -/
noncomputable abbrev PresentationIndex.comap (i : PresentationIndex (P := P) Aplus U) :
    PresentationIndex (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U) :=
  i.map φ hφ hopen hplus fun _ hw ↦ Opens.mem_map.mpr hw

open scoped Classical in
/-- The component at an index `i` of `U`: project to `A⟨i⟩`, base change along `φ` to `B⟨φ(i)⟩`,
and identify `B⟨φ(i)⟩` with the presentation limit on the rational open `R(φ(i)) = f⁻¹(R(i))`. -/
private noncomputable def presentationLimitComapLeg (i : PresentationIndex (P := P) Aplus U) :
    presentationLimit (P := P) Aplus U ⟶
      presentationLimit (P := P') Bplus (spaBasicOpen Bplus
        (i.comap (P' := P') φ hφ hopen hplus).pres.num
        (i.comap (P' := P') φ hφ hopen hplus).pres.den) :=
  presentationLimitπToPresentation Aplus U i ≫
    Presentation.mapHom φ hφ i.pres (i.comap (P' := P') φ hφ hopen hplus).pres
      (PresentationIndex.map_pres_den φ hφ hopen hplus _ i) (fun t ht ↦ by
        rw [PresentationIndex.map_pres_num]
        exact Finset.mem_image_of_mem φ ht) ≫
    (presentationLimitRationalIso Bplus hBplus _
      (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).inv

/-- The leg at `i`, followed by the projection at an index `m` of `R(φ(i))`, is the projection at
`i`, the base change, and the comparison morphism `B⟨φ(i)⟩ → B⟨m⟩`. -/
private theorem presentationLimitComapLeg_comp_π (i : PresentationIndex (P := P) Aplus U)
    (m : PresentationIndex (P := P') Bplus (spaBasicOpen Bplus
      (i.comap (P' := P') φ hφ hopen hplus).pres.num
      (i.comap (P' := P') φ hφ hopen hplus).pres.den)) :
    presentationLimitComapLeg φ hφ hopen hplus hBplus i ≫
        presentationLimitπToPresentation Bplus _ m =
      presentationLimitπToPresentation Aplus U i ≫
        Presentation.mapHom φ hφ i.pres _ (PresentationIndex.map_pres_den φ hφ hopen hplus _ i)
          (fun t ht ↦ by
            classical
            rw [PresentationIndex.map_pres_num]
            exact Finset.mem_image_of_mem φ ht) ≫
        homOfRationalSubsetSubset Bplus hBplus (m.rationalSubset_subset le_rfl) := by
  simp only [presentationLimitComapLeg, Category.assoc, presentationLimitRationalIso_inv_comp_π]

omit [IsTopologicalRing A] in
/-- For `i ≤ k`, `R(φ(k)) ⊆ R(φ(i))`. -/
private theorem spaBasicOpen_map_le {i k : PresentationIndex (P := P) Aplus U} (h : i ≤ k) :
    spaBasicOpen Bplus (k.comap (P' := P') φ hφ hopen hplus).pres.num
        (k.comap (P' := P') φ hφ hopen hplus).pres.den ≤
      spaBasicOpen Bplus (i.comap (P' := P') φ hφ hopen hplus).pres.num
        (i.comap (P' := P') φ hφ hopen hplus).pres.den :=
  spaBasicOpen_le_spaBasicOpen_iff.mpr (rationalSubset_subset_rationalSubset_of_le Bplus
    (PresentationIndex.map_mono φ hφ hopen hplus _ h))

/-- The legs are compatible with refinement of indices. -/
private theorem presentationLimitComapLeg_comp_map {i k : PresentationIndex (P := P) Aplus U}
    (h : i ≤ k) :
    presentationLimitComapLeg φ hφ hopen hplus hBplus i ≫
        presentationLimitMap (spaBasicOpen_map_le (P' := P') φ hφ hopen hplus h) =
      presentationLimitComapLeg φ hφ hopen hplus hBplus k := by
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  rw [Category.assoc, presentationLimitMap_comp_πToPresentation, ← Category.assoc,
    presentationLimitComapLeg_comp_π, presentationLimitComapLeg_comp_π]
  simp only [Category.assoc]
  rw [homOfRationalSubsetSubset_comp_eqToHom hBplus
    (presentationIndexRestrict_obj_pres (spaBasicOpen_map_le φ hφ hopen hplus h) m) _
    ((m.rationalSubset_subset le_rfl).trans
      (spaBasicOpen_le_spaBasicOpen_iff.mp (spaBasicOpen_map_le φ hφ hopen hplus h)))]
  -- both sides are the structure map `A → B⟨m⟩` through `φ`
  refine presentationLimitπToPresentation_comp_eq h ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
    toCompletionLocTopHom_comp_homOfRationalSubsetSubset hBplus]

variable (U) in
/-- The opens `R(φ(i)) = f⁻¹(R(i))`, for `i` ranging over the indices of `U`, cover `f⁻¹U`. -/
private theorem ofArrows_mem_grothendieckTopology :
    Sieve.ofArrows (fun i : PresentationIndex (P := P) Aplus U ↦ spaBasicOpen Bplus
        (i.comap (P' := P') φ hφ hopen hplus).pres.num
        (i.comap (P' := P') φ hφ hopen hplus).pres.den)
      (fun i ↦ homOfLE (i.comap (P' := P') φ hφ hopen hplus).le_open) ∈
      Opens.grothendieckTopology ↥(spa Bplus) ((Opens.map (spaComapTopHom φ hφ hplus)).obj U) := by
  intro w hw
  obtain ⟨i, hi⟩ := exists_presentationIndex_mem (P := P) (Opens.mem_map.mp hw)
  refine ⟨_, homOfLE (i.comap (P' := P') φ hφ hopen hplus).le_open,
    Sieve.ofArrows_mk _ _ i, ?_⟩
  rw [PresentationIndex.spaBasicOpen_map_pres]
  exact Opens.mem_map.mpr hi

variable (U) in
/-- The legs agree on overlaps: `R(φ(i)) ∩ R(φ(j)) = R(φ(k))` for the common refinement `k` of `i`
and `j`, and both legs restrict to the leg at `k`. -/
private theorem presentationLimitComapLeg_compatible ⦃W : Opens ↥(spa Bplus)⦄
    ⦃i j : PresentationIndex (P := P) Aplus U⦄
    (a : W ⟶ spaBasicOpen Bplus
      (i.comap (P' := P') φ hφ hopen hplus).pres.num
      (i.comap (P' := P') φ hφ hopen hplus).pres.den)
    (b : W ⟶ spaBasicOpen Bplus
      (j.comap (P' := P') φ hφ hopen hplus).pres.num
      (j.comap (P' := P') φ hφ hopen hplus).pres.den) :
    (presentationLimitComapLeg φ hφ hopen hplus hBplus i ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm) ≫
      (presentationLimitPresheaf P' Bplus).map a.op =
    (presentationLimitComapLeg φ hφ hopen hplus hBplus j ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm) ≫
      (presentationLimitPresheaf P' Bplus).map b.op := by
  -- `W ⊆ R(φ(k))` for the common refinement `k` of `i` and `j`
  have hk : W ≤ spaBasicOpen Bplus
      ((i.commonRefinement j).comap (P' := P') φ hφ hopen hplus).pres.num
      ((i.commonRefinement j).comap (P' := P') φ hφ hopen hplus).pres.den := by
    rw [PresentationIndex.spaBasicOpen_map_pres, PresentationIndex.commonRefinement_pres,
      spaBasicOpen_commonRefinement]
    intro w hw
    rw [Opens.mem_map, Opens.mem_inf]
    exact ⟨Opens.mem_map.mp ((PresentationIndex.spaBasicOpen_map_pres φ hφ hopen hplus _ i).le
        (a.le hw)),
      Opens.mem_map.mp ((PresentationIndex.spaBasicOpen_map_pres φ hφ hopen hplus _ j).le
        (b.le hw))⟩
  simp only [presentationLimitPresheaf_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← presentationLimitMap_comp
      (spaBasicOpen_map_le φ hφ hopen hplus (i.le_commonRefinement_left j)) hk,
    ← presentationLimitMap_comp
      (spaBasicOpen_map_le φ hφ hopen hplus (i.le_commonRefinement_right j)) hk]
  simp only [Category.assoc,
    reassoc_of% presentationLimitComapLeg_comp_map φ hφ hopen hplus hBplus
      (i.le_commonRefinement_left j),
    reassoc_of% presentationLimitComapLeg_comp_map φ hφ hopen hplus hBplus
      (i.le_commonRefinement_right j)]

/-! ### The glued morphism -/

variable (U) in
/-- **The component at `U` of the morphism `𝒪_{Spa A} → f_* 𝒪_{Spa B}` induced by `φ`**, for
`𝒪_{Spa B}` a sheaf: the morphism `𝒪_{Spa A}(U) → 𝒪_{Spa B}(f⁻¹U)` whose restriction to the open
`f⁻¹(R(i)) = R(φ(i))`, for every index `i` of `U`, is the projection to `A⟨i⟩` followed by the base
change `A⟨i⟩ → B⟨φ(i)⟩` of `φ` (`presentationLimitComap_comp_map_comp_π`). It is obtained by
gluing these base changes along the cover of `f⁻¹U` by the opens `f⁻¹(R(i))`. -/
noncomputable def presentationLimitComap :
    presentationLimit (P := P) Aplus U ⟶
      presentationLimit (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U) :=
  hsheaf.amalgamateOfArrows
    (fun i : PresentationIndex (P := P) Aplus U ↦
      homOfLE (i.comap (P' := P') φ hφ hopen hplus).le_open)
    (ofArrows_mem_grothendieckTopology φ hφ hopen hplus U)
    (fun i ↦ presentationLimitComapLeg φ hφ hopen hplus hBplus i ≫
      eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm)
    (fun _ _ _ a b _ ↦ presentationLimitComapLeg_compatible φ hφ hopen hplus hBplus U a b) ≫
  eqToHom (presentationLimitPresheaf_obj P' Bplus _)

/-- The component at `U`, restricted to the open `R(φ(i)) = f⁻¹(R(i))`, is the leg at `i`. -/
private theorem presentationLimitComap_comp_map_le_open (i : PresentationIndex (P := P) Aplus U) :
    presentationLimitComap φ hφ hopen hplus hBplus hsheaf U ≫
        presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open =
      presentationLimitComapLeg φ hφ hopen hplus hBplus i := by
  rw [← cancel_mono (eqToHom (presentationLimitPresheaf_obj P' Bplus (op (spaBasicOpen Bplus
    (i.comap (P' := P') φ hφ hopen hplus).pres.num
    (i.comap (P' := P') φ hφ hopen hplus).pres.den))).symm)]
  have := hsheaf.amalgamateOfArrows_map
    (fun i : PresentationIndex (P := P) Aplus U ↦
      homOfLE (i.comap (P' := P') φ hφ hopen hplus).le_open)
    (ofArrows_mem_grothendieckTopology φ hφ hopen hplus U)
    (fun i ↦ presentationLimitComapLeg φ hφ hopen hplus hBplus i ≫
      eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm)
    (fun _ _ _ a b _ ↦ presentationLimitComapLeg_compatible φ hφ hopen hplus hBplus U a b) i
  simp only [presentationLimitPresheaf_map] at this
  simpa only [presentationLimitComap, Category.assoc] using this

include hsheaf in
/-- **Morphisms into `𝒪_{Spa B}(f⁻¹U)` are determined by their restrictions to the opens
`f⁻¹(R(i)) = R(φ(i))`**, `i` ranging over the indices of `U`: these opens cover `f⁻¹U` and
`𝒪_{Spa B}` is a sheaf. -/
theorem presentationLimit_hom_ext_of_isSheaf {X : CompleteSeparatedTopCommRingCat.{v}}
    {g₁ g₂ : X ⟶
      presentationLimit (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj U)}
    (h : ∀ i : PresentationIndex (P := P) Aplus U,
      g₁ ≫ presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open =
        g₂ ≫ presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open) :
    g₁ = g₂ := by
  rw [← cancel_mono (eqToHom (presentationLimitPresheaf_obj P' Bplus
    (op ((Opens.map (spaComapTopHom φ hφ hplus)).obj U))).symm)]
  refine Presheaf.IsSheaf.hom_ext_ofArrows hsheaf
    (fun i : PresentationIndex (P := P) Aplus U ↦
      homOfLE (i.comap (P' := P') φ hφ hopen hplus).le_open)
    (ofArrows_mem_grothendieckTopology φ hφ hopen hplus U) fun i ↦ ?_
  simp only [presentationLimitPresheaf_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Category.assoc, h i, Category.assoc]

/-- **On a rational open the morphism is the base change**: the component at `U`, restricted to
the open `f⁻¹(R(i)) = R(φ(i))` for an index `i` of `U` and followed by the projection at an index
`m` of that open, is the projection at `i`, the base change `A⟨i⟩ → B⟨φ(i)⟩` of `φ` and the
comparison morphism `B⟨φ(i)⟩ → B⟨m⟩`. -/
theorem presentationLimitComap_comp_map_comp_π (i : PresentationIndex (P := P) Aplus U)
    (m : PresentationIndex (P := P') Bplus (spaBasicOpen Bplus
      (i.comap (P' := P') φ hφ hopen hplus).pres.num
      (i.comap (P' := P') φ hφ hopen hplus).pres.den)) :
    presentationLimitComap φ hφ hopen hplus hBplus hsheaf U ≫
        presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open ≫
        presentationLimitπToPresentation Bplus _ m =
      presentationLimitπToPresentation Aplus U i ≫
        Presentation.mapHom φ hφ i.pres _ (PresentationIndex.map_pres_den φ hφ hopen hplus _ i)
          (fun t ht ↦ by
            classical
            rw [PresentationIndex.map_pres_num]
            exact Finset.mem_image_of_mem φ ht) ≫
        homOfRationalSubsetSubset Bplus hBplus (m.rationalSubset_subset le_rfl) := by
  rw [← Category.assoc, presentationLimitComap_comp_map_le_open, presentationLimitComapLeg_comp_π]

/-- **On a rational open the morphism is the base change**, for an open `V ⊆ f⁻¹U` and an index
`m` of `V` whose rational open lies in `R(φ(i))` for an index `i` of `U`: the component at `U`,
restricted to `V` and followed by the projection at `m`, is the projection at `i`, the base change
`A⟨i⟩ → B⟨φ(i)⟩` of `φ` and the comparison morphism `B⟨φ(i)⟩ → B⟨m⟩`. -/
theorem presentationLimitComap_comp_map_comp_π_of_le (i : PresentationIndex (P := P) Aplus U)
    {V : Opens ↥(spa Bplus)} (hV : V ≤ (Opens.map (spaComapTopHom φ hφ hplus)).obj U)
    (m : PresentationIndex (P := P') Bplus V)
    (hm : rationalSubset Bplus m.pres.num m.pres.den ⊆ rationalSubset Bplus
      (i.comap (P' := P') φ hφ hopen hplus).pres.num
      (i.comap (P' := P') φ hφ hopen hplus).pres.den) :
    presentationLimitComap φ hφ hopen hplus hBplus hsheaf U ≫ presentationLimitMap hV ≫
        presentationLimitπToPresentation Bplus V m =
      presentationLimitπToPresentation Aplus U i ≫
        Presentation.mapHom φ hφ i.pres _ (PresentationIndex.map_pres_den φ hφ hopen hplus _ i)
          (fun t ht ↦ by
            classical
            rw [PresentationIndex.map_pres_num]
            exact Finset.mem_image_of_mem φ ht) ≫
        homOfRationalSubsetSubset Bplus hBplus hm := by
  -- `m` as an index of `R(φ(i))`; restricting to `V` or to `R(φ(i))` and projecting at `m` are the
  -- same projection of the limit on `f⁻¹U`
  let m' : PresentationIndex (P := P') Bplus (spaBasicOpen Bplus
      (i.comap (P' := P') φ hφ hopen hplus).pres.num
      (i.comap (P' := P') φ hφ hopen hplus).pres.den) :=
    ⟨m.pres, m.isOpen_span, spaBasicOpen_le_spaBasicOpen_iff.mpr hm⟩
  have e : (presentationIndexRestrict hV).obj m =
      (presentationIndexRestrict
        (i.comap (P' := P') φ hφ hopen hplus).le_open).obj m' :=
    PresentationIndex.ext
      (by rw [presentationIndexRestrict_obj_pres, presentationIndexRestrict_obj_pres])
  rw [presentationLimitMap_comp_πToPresentation,
    presentationLimitπToPresentation_comp_eqToHom_congr e _
      (congrArg Presentation.completionLocObj (presentationIndexRestrict_obj_pres _ m')),
    ← presentationLimitMap_comp_πToPresentation]
  exact presentationLimitComap_comp_map_comp_π φ hφ hopen hplus hBplus hsheaf i m'

/-- **On a rational open the morphism is the base change**, in terms of the identification
`presentationLimitRationalIso` of `𝒪_{Spa B}(R(φ(i)))` with `B⟨φ(i)⟩`: the component at `U`,
restricted to `f⁻¹(R(i)) = R(φ(i))`, is the projection at `i` followed by the base change
`A⟨i⟩ → B⟨φ(i)⟩` of `φ`. -/
theorem presentationLimitComap_comp_map_comp_hom (i : PresentationIndex (P := P) Aplus U) :
    presentationLimitComap φ hφ hopen hplus hBplus hsheaf U ≫
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
    presentationLimitMap (P := P) h ≫ presentationLimitComap φ hφ hopen hplus hBplus hsheaf U' =
      presentationLimitComap φ hφ hopen hplus hBplus hsheaf U ≫
        presentationLimitMap ((Opens.map (spaComapTopHom φ hφ hplus)).monotone h) := by
  refine presentationLimit_hom_ext_of_isSheaf (P := P) φ hφ hopen hplus hsheaf fun i ↦ ?_
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  -- the left side is the projection at the index of `U` with the presentation of `i`, followed by
  -- the base change along `φ` to `B⟨m⟩`
  simp only [Category.assoc, presentationLimitComap_comp_map_comp_π, presentationLimitMap_comp]
  rw [reassoc_of% presentationLimitMap_comp_πToPresentation]
  -- so is the right side, through the open `R(φ(i))` read as an open inside `f⁻¹U`
  have e : (((presentationIndexRestrict h).obj i).comap (P' := P') φ hφ hopen hplus).pres =
      (i.comap (P' := P') φ hφ hopen hplus).pres :=
    Presentation.ext
      (by rw [PresentationIndex.map_pres_num, PresentationIndex.map_pres_num,
        presentationIndexRestrict_obj_pres])
      (by rw [PresentationIndex.map_pres_den, PresentationIndex.map_pres_den,
        presentationIndexRestrict_obj_pres])
  have hm : rationalSubset Bplus m.pres.num m.pres.den ⊆ rationalSubset Bplus
      (((presentationIndexRestrict h).obj i).comap (P' := P') φ hφ hopen hplus).pres.num
      (((presentationIndexRestrict h).obj i).comap (P' := P') φ hφ hopen hplus).pres.den := by
    rw [e]
    exact m.rationalSubset_subset le_rfl
  rw [presentationLimitComap_comp_map_comp_π_of_le φ hφ hopen hplus hBplus hsheaf
    ((presentationIndexRestrict h).obj i)
    ((i.comap (P' := P') φ hφ hopen hplus).le_open.trans
      ((Opens.map (spaComapTopHom φ hφ hplus)).monotone h)) m hm]
  -- both base changes are the structure map `A → B⟨m⟩` through `φ`
  refine congrArg (presentationLimitπToPresentation Aplus U _ ≫ ·)
    (((presentationIndexRestrict h).obj i).pres.hom_ext ?_)
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [Presentation.toCompletionLocTopHom_comp_eqToHom_hom_assoc
    (presentationIndexRestrict_obj_pres h i)]
  simp only [Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
    toCompletionLocTopHom_comp_homOfRationalSubsetSubset hBplus]

/-! ### The morphism of presheaves -/

/-- **The morphism of structure presheaves `𝒪_{Spa A} ⟶ f_* 𝒪_{Spa B}` induced by `φ`**, for
`𝒪_{Spa B}` a sheaf: Wedhorn §8.1's `f♭`, with the components `presentationLimitComap`. -/
noncomputable def presentationLimitPresheafComap :
    presentationLimitPresheaf P Aplus ⟶
      (TopCat.Presheaf.pushforward _ (spaComapTopHom φ hφ hplus)).obj
        (presentationLimitPresheaf P' Bplus) where
  app U := eqToHom (presentationLimitPresheaf_obj P Aplus U) ≫
    presentationLimitComap φ hφ hopen hplus hBplus hsheaf U.unop ≫
    eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm
  naturality U U' g := by
    simp only [presentationLimitPresheaf_map, TopCat.Presheaf.pushforward_obj_map, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [presentationLimitMap_comp_presentationLimitComap_assoc]

/-- The component of `presentationLimitPresheafComap` at an open is `presentationLimitComap`,
transported along the evaluation equations of the two presheaves. -/
@[simp]
theorem presentationLimitPresheafComap_app (U : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheafComap φ hφ hopen hplus hBplus hsheaf).app U =
      eqToHom (presentationLimitPresheaf_obj P Aplus U) ≫
        presentationLimitComap φ hφ hopen hplus hBplus hsheaf U.unop ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus _).symm :=
  (rfl)

/-! ### Functoriality -/

variable (U) in
/-- **The identity induces the identity**: for `φ` the identity of `A`, the component at `U` is
the restriction along the equality `id⁻¹U = U`. -/
theorem presentationLimitComap_id (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    presentationLimitComap (P := P) (P' := P) (RingHom.id A) continuous_id
        (fun J hJ ↦ by rwa [Ideal.map_id]) (fun _ ha ↦ ha) hAplus hsheafA U =
      presentationLimitMap (P := P) (map_spaComapTopHom_id_obj U).le := by
  classical
  refine presentationLimit_hom_ext_of_isSheaf (P := P) (RingHom.id A) continuous_id
    (fun J hJ ↦ by rwa [Ideal.map_id]) (fun _ ha ↦ ha) hsheafA fun i ↦ ?_
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  rw [Category.assoc, presentationLimitComap_comp_map_comp_π, presentationLimitMap_comp,
    presentationLimitMap_comp_πToPresentation]
  -- both sides are a projection followed by the structure map `A → A⟨m⟩`
  refine (presentationLimitπToPresentation_comp_eq_of_subset hAplus ?_ ?_).symm
  · rw [presentationIndexRestrict_obj_pres]
    simpa using m.rationalSubset_subset le_rfl
  · rw [Presentation.toCompletionLocTopHom_comp_eqToHom_hom
        (presentationIndexRestrict_obj_pres _ m), ObjectProperty.FullSubcategory.comp_hom,
      Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
      toCompletionLocTopHom_comp_homOfRationalSubsetSubset]
    -- `⟨RingHom.id A, _⟩` is the identity of `TopCommRingCat.of A`
    rfl

/-- **The identity induces the identity morphism of structure presheaves**, up to the transport
along `spaComapTopHom_id`. -/
theorem presentationLimitPresheafComap_id (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    presentationLimitPresheafComap (P := P) (P' := P) (RingHom.id A) continuous_id
        (fun J hJ ↦ by rwa [Ideal.map_id]) (fun _ ha ↦ ha) hAplus hsheafA ≫
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
  (hopen' : ∀ ⦃J : Ideal B⦄, IsOpen (J : Set B) → IsOpen (J.map ψ : Set C))
  (hplus' : ∀ b ∈ Bplus, ψ b ∈ Cplus) (hCplus : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c)
  (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Cplus))
    (presentationLimitPresheaf P'' Cplus))

variable (U) in
/-- **The morphisms are contravariantly functorial**: the component at `U` of the morphism induced
by `ψ ∘ φ` is the component at `U` of the morphism induced by `φ`, followed by the component at
`φ⁻¹U` of the morphism induced by `ψ` and the restriction along `(ψ ∘ φ)⁻¹U = ψ⁻¹(φ⁻¹U)`. -/
theorem presentationLimitComap_comp :
    presentationLimitComap (P := P) (P' := P'') (ψ.comp φ) (hψ.comp hφ)
        (fun J hJ ↦ by rw [← Ideal.map_map]; exact hopen' (hopen hJ))
        (fun a ha ↦ hplus' (φ a) (hplus a ha)) hCplus hsheaf' U =
      presentationLimitComap (P := P) (P' := P') φ hφ hopen hplus hBplus hsheaf U ≫
        presentationLimitComap (P := P') (P' := P'') ψ hψ hopen' hplus' hCplus hsheaf' _ ≫
        presentationLimitMap (P := P'')
          (map_spaComapTopHom_comp_obj φ hφ hplus hψ hplus' U).le := by
  classical
  refine presentationLimit_hom_ext_of_isSheaf (P := P) (ψ.comp φ) (hψ.comp hφ)
    (fun J hJ ↦ by rw [← Ideal.map_map]; exact hopen' (hopen hJ))
    (fun a ha ↦ hplus' (φ a) (hplus a ha)) hsheaf' fun i ↦ ?_
  refine presentationLimit_hom_ext_toPresentation fun m ↦ ?_
  rw [Category.assoc, presentationLimitComap_comp_map_comp_π]
  simp only [Category.assoc, reassoc_of% presentationLimitMap_comp]
  -- the rational open `R((ψ ∘ φ)(i))` is presented by the index `ψ(φ(i))` of `ψ⁻¹(φ⁻¹U)`
  have hm : rationalSubset Cplus m.pres.num m.pres.den ⊆ rationalSubset Cplus
      ((i.comap (P' := P') φ hφ hopen hplus).comap (P' := P'') ψ hψ hopen' hplus').pres.num
      ((i.comap (P' := P') φ hφ hopen hplus).comap (P' := P'') ψ hψ hopen' hplus').pres.den := by
    simpa [Finset.image_image] using m.rationalSubset_subset le_rfl
  rw [presentationLimitComap_comp_map_comp_π_of_le ψ hψ hopen' hplus' hCplus hsheaf'
    (i.comap (P' := P') φ hφ hopen hplus) _ m hm]
  -- the projection at `φ(i)` after the morphism induced by `φ` is the base change along `φ`
  have hi := presentationLimitComap_comp_map_comp_π_of_le φ hφ hopen hplus hBplus hsheaf i le_rfl
    (i.comap (P' := P') φ hφ hopen hplus) subset_rfl
  rw [presentationLimitMap_refl, Category.id_comp] at hi
  rw [reassoc_of% hi]
  -- both sides are the structure map `A → C⟨m⟩` through `ψ ∘ φ`
  refine congrArg (presentationLimitπToPresentation Aplus U i ≫ ·) (i.pres.hom_ext ?_)
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
    toCompletionLocTopHom_comp_homOfRationalSubsetSubset_assoc,
    toCompletionLocTopHom_comp_homOfRationalSubsetSubset]
  -- `⟨ψ.comp φ, _⟩` is the composite of `⟨φ, hφ⟩` and `⟨ψ, hψ⟩` in `TopCommRingCat`
  rfl

/-- **The morphisms of structure presheaves are contravariantly functorial**: the morphism induced
by `ψ ∘ φ` is the morphism induced by `φ` followed by the pushforward of the morphism induced by
`ψ`, up to the transport along `spaComapTopHom_comp`. -/
theorem presentationLimitPresheafComap_comp :
    presentationLimitPresheafComap (P := P) (P' := P'') (ψ.comp φ) (hψ.comp hφ)
        (fun J hJ ↦ by rw [← Ideal.map_map]; exact hopen' (hopen hJ))
        (fun a ha ↦ hplus' (φ a) (hplus a ha)) hCplus hsheaf' ≫
      Functor.whiskerRight (eqToHom (congrArg (fun f ↦ (Opens.map f).op)
        (spaComapTopHom_comp φ hφ hplus hψ hplus'))) (presentationLimitPresheaf P'' Cplus) =
      presentationLimitPresheafComap (P := P) (P' := P') φ hφ hopen hplus hBplus hsheaf ≫
        (TopCat.Presheaf.pushforward _ (spaComapTopHom φ hφ hplus)).map
          (presentationLimitPresheafComap (P := P') (P' := P'') ψ hψ hopen' hplus' hCplus
            hsheaf') := by
  refine NatTrans.ext (funext fun U ↦ ?_)
  simp only [NatTrans.comp_app, presentationLimitPresheafComap_app, Functor.whiskerRight_app,
    eqToHom_app, presentationLimitPresheaf_map, TopCat.Presheaf.pushforward_map_app']
  rw [presentationLimitComap_comp φ hφ hopen hplus hBplus hsheaf (unop U) ψ hψ hopen' hplus' hCplus
    hsheaf']
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

end TauCeti.ValuationSpectrum

end
