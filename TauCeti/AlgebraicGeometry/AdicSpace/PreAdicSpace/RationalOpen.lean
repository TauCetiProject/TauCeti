/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.OpenImmersion
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyAffinoid

/-!
# Rational subsets are open affinoid subspaces

Let `X = Spa(A, A⁺)` be the presentation-limit pre-adic space of `A` with a plus ring `A⁺` of
power-bounded elements containing the ring of definition, let `U = R(T/s)` be a rational subset with
`T` spanning an open ideal, and let `j : Spa(A⟨T/s⟩, A_U⁺) → X` be the open embedding induced by the
structure map `A → A⟨T/s⟩`. This file proves that the restriction of `X` along `j` is isomorphic in
`𝒱^pre` to the pre-adic space `Spa(A⟨T/s⟩, A_U⁺)`, Wedhorn's Remark 8.8. The underlying isomorphism
of presheafed spaces is Wedhorn's Remark 8.4, `presentationLimitPresheafLocIso`; what is added here
is the compatibility of the stalk valuations, which makes it an isomorphism of pre-adic spaces.

Consequently every rational open of `X` is an open affinoid subspace, and when `A` is a Huber ring
the open affinoid subspaces of `X` form a basis of its topology. That is the basis hypothesis of
`TauCeti.PreAdicSpace.isSheafy_of_isAdapted_of_isSheaf_affinoidOpens`, under which the sheaf
condition can be checked on open affinoid subspaces. Since the whole space is rational and the
structure presheaf is adapted to the rational opens, hence to the larger family of open affinoid
subspaces, `X` is a pre-adic space in Wedhorn's sense.

## The stalk valuations

The valuation on the stalk at a point is determined by its pullbacks along the germ maps of the
rational neighbourhoods of the point (`eq_presentationLimitStalkValuation`). For a rational
neighbourhood `R(p')` of `y` in `Spa(A⟨T/s⟩, A_U⁺)`, present `j(R(p'))` by `p`. The germ maps of
`R(p')` at `y` and of `R(p)` at `j(y)` correspond under the ring isomorphism
`A⟨p⟩ ≅ A⟨T/s⟩⟨p'⟩` of Remark 8.4, and that isomorphism matches the points of the two coordinate
rings determined by `j(y)` and by `y` (`comap_presentationLimitLocIso_rationalLocalizationPoint`).

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceLocIso`: the isomorphism in `𝒱^pre`
  between the restriction of `Spa(A, A⁺)` along `j` and `Spa(A⟨T/s⟩, A_U⁺)`.

## Main results

* `TauCeti.ValuationSpectrum.isAffinoid_restrict_spaComapLocHom`: the restriction of `Spa(A, A⁺)`
  along `j` is an affinoid pre-adic space.
* `TauCeti.ValuationSpectrum.spaBasicOpen_mem_affinoidOpens`,
  `TauCeti.ValuationSpectrum.spaRationalOpens_subset_affinoidOpens`: rational subsets are open
  affinoid subspaces.
* `TauCeti.ValuationSpectrum.isBasis_affinoidOpens_presentationLimitPreAdicSpace`: the open
  affinoid subspaces form a basis of the topology.
* `TauCeti.ValuationSpectrum.isPreAdic_presentationLimitPreAdicSpace`,
  `TauCeti.PreAdicSpace.isPreAdic_of_isAffinoid`: `Spa(A, A⁺)`, and hence every affinoid pre-adic
  space, is a pre-adic space, Wedhorn's Remark and Definition 8.10.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remarks 8.4 and 8.8 and Remark
  and Definition 8.10.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Topology TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

namespace TauCeti.ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
  (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus) (hT : IsOpen (Ideal.span (T : Set A) : Set A))

private noncomputable def restrictLocPresheafedSpaceIso :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ((presentationLimitPreAdicSpace P Aplus hAplus hP).restrict
        (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden)).toPresheafedSpace ≅
      (presentationLimitPreAdicSpace (completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden)
        (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden)
        (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden)
        ).toPresheafedSpace :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  PresheafedSpace.isoOfComponents (Iso.refl _)
    (presentationLimitPresheafLocIso P Aplus T s S hden hAplus hP hT)

-- The germ condition on a map `θ` from the stalk of `Spa(A⟨T/s⟩, A_U⁺)` at `y` to the stalk of
-- `Spa(A, A⁺)` at `j(y)`: on every rational open `W ∋ y`, `θ` is induced by the inverse of
-- `presentationLimitLocImageIso`. It holds for the stalk map of the open immersion `j`.
private abbrev IsLocStalkMap (y : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      spa (completedPlusSubring P Aplus T s S hden))
    (θ : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      (presentationLimitPresheafInCommRingCat (completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden)).stalk y ⟶
      (presentationLimitPresheafInCommRingCat P Aplus).stalk
        (spaComapLocHom P Aplus T s S hden y)) : Prop :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  ∀ (W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)))
    (hW : W ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden)) (hy : y ∈ W),
    (presentationLimitPresheafInCommRingCat (completionLocalization P T s S hden)
      (completedPlusSubring P Aplus T s S hden)).germ W y hy ≫ θ =
    eqToHom (presentationLimitPresheafInCommRingCat_obj _ _ (op W)) ≫
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W hW).inv ≫
      eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus
        (op ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W))).symm ≫
      (presentationLimitPresheafInCommRingCat P Aplus).germ
        ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W)
        (spaComapLocHom P Aplus T s S hden y) ⟨y, hy, rfl⟩
-- For a rational open `W = R(p')` of `Spa(A⟨T/s⟩, A_U⁺)` whose image `j(W)` is presented by `p`,
-- a germ map `θ` as in `IsLocStalkMap` carries the germ map of `R(p')` to the germ map of `R(p)`
-- through the ring isomorphism `A⟨p⟩ ≅ 𝒪_X(j(W)) ≅ 𝒪_U(W) ≅ A⟨T/s⟩⟨p'⟩` of Remark 8.4.
private theorem map_comp_presentationLimitRationalGerm_comp_of_isLocStalkMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (y : spa (completedPlusSubring P Aplus T s S hden)) (θ : _)
      (_ : IsLocStalkMap P Aplus T s S hden hAplus hP hT y θ)
      (p' : Presentation (completionLocalization P T s S hden))
      (hp' : IsOpen (Ideal.span (p'.num : Set (UniformSpace.Completion S)) :
        Set (UniformSpace.Completion S)))
      (hy : y ∈ spaBasicOpen (completedPlusSubring P Aplus T s S hden) p'.num p'.den)
      (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
      (hpV : (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj
        (spaBasicOpen _ p'.num p'.den) = spaBasicOpen Aplus p.num p.den)
      (hjy : spaComapLocHom P Aplus T s S hden y ∈ spaBasicOpen Aplus p.num p.den),
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          ((presentationLimitRationalIso Aplus hAplus p hp).inv ≫
            presentationLimitMap (P := P) hpV.le ≫
            (presentationLimitLocIso P Aplus T s S hden hAplus hT _
              (spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT _
                (mem_spaRationalOpens_iff_exists_spaBasicOpen.mpr ⟨_, _, hp', rfl⟩))
              (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden _)).hom ≫
            presentationLimitMap (P := completionLocalization P T s S hden)
              (locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden _).ge ≫
            (presentationLimitRationalIso _
              (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden) p' hp').hom) ≫
          presentationLimitRationalGerm
            (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden) p' hp' y hy ≫ θ =
        presentationLimitRationalGerm hAplus p hp (spaComapLocHom P Aplus T s S hden y) hjy := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro y θ hθ p' hp' hy p hp hpV hjy
  have hW : spaBasicOpen (completedPlusSubring P Aplus T s S hden) p'.num p'.den ∈
      spaRationalOpens (completedPlusSubring P Aplus T s S hden) :=
    mem_spaRationalOpens_iff_exists_spaBasicOpen.mpr ⟨_, _, hp', rfl⟩
  have hVW := locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden
    (spaBasicOpen _ p'.num p'.den)
  -- both sides are germ maps at `R(p)`, after restricting `j(W) = R(p)` to `R(p)`
  rw [presentationLimitRationalGerm_def, presentationLimitRationalGerm_def, Category.assoc,
    hθ _ hW hy, ← TopCat.Presheaf.germ_res (presentationLimitPresheafInCommRingCat P Aplus)
      (homOfLE hpV.ge) _ hjy]
  -- restriction in the ring presheaf is the reindexing map of presentation limits
  have hmap := presentationLimitPresheafInCommRingCat_map P Aplus (homOfLE hpV.ge).op
  rw [comp_eqToHom_iff] at hmap
  rw [hmap, presentationLimitRationalIsoInCommRingCat_inv,
    presentationLimitRationalIsoInCommRingCat_inv]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← Functor.map_comp_assoc]
  -- the identification on `W` is `presentationLimitLocIso` at `j(W)`, up to transport
  have hli : (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT _ hW).inv =
      eqToHom (congrArg _ hVW).symm ≫ (presentationLimitLocIso P Aplus T s S hden hAplus hT _
        (spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT _ hW)
        (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden _)).inv := by
    rw [← cancel_epi (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT _ hW).hom,
      Iso.hom_inv_id, presentationLimitLocImageIso_hom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Iso.hom_inv_id]
  rw [hli, ← eqToHom_presentationLimit hVW (congrArg _ hVW)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, presentationLimitMap_comp, presentationLimitMap_refl, Category.comp_id]

-- **The stalk valuation is determined by a germ map.** If `θ` satisfies the germ condition
-- `IsLocStalkMap`, then it pulls the stalk valuation at `j(y)` back to the stalk valuation at `y`.
-- By `eq_presentationLimitStalkValuation` it suffices to compare the two after pulling back along
-- the germ map of every rational neighbourhood `R(p')` of `y`. Presenting `j(R(p'))` by `p`, the
-- germ maps of `R(p')` and `R(p)` correspond under the ring isomorphism of Remark 8.4
-- (`map_comp_presentationLimitRationalGerm_comp_of_isLocStalkMap`), which matches the points of
-- `A⟨p⟩` and `A⟨T/s⟩⟨p'⟩` (`comap_presentationLimitLocIso_rationalLocalizationPoint`).
private theorem presentationLimitStalkValuation_eq_comap_of_isLocStalkMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (y : spa (completedPlusSubring P Aplus T s S hden)) (θ : _),
      IsLocStalkMap P Aplus T s S hden hAplus hP hT y θ →
      presentationLimitStalkValuation
          (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden)
          (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden)
          y =
        comap θ.hom
          (presentationLimitStalkValuation hAplus hP (spaComapLocHom P Aplus T s S hden y)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have hAplus' := isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden
  have hP' := completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden
  intro y θ hθ
  refine eq_presentationLimitStalkValuation hAplus' hP' (fun p' hp' hy ↦ ?_) |>.symm
  -- the image `j(W)` of `W = R(p')` is a rational open of `Spa(A, A⁺)`, presented by some `p`
  set W := spaBasicOpen (completedPlusSubring P Aplus T s S hden) p'.num p'.den
  have hW : W ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden) :=
    mem_spaRationalOpens_iff_exists_spaBasicOpen.mpr ⟨_, _, hp', rfl⟩
  have hV := spaComapLoc_functor_obj_mem_spaRationalOpens P Aplus hP T s S hden hT W hW
  have hVW := locOpensComap_spaComapLoc_functor_obj P Aplus hP T s S hden W
  obtain ⟨T', s', hT', hpV⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  let p : Presentation P := ⟨T', s', hasDenominatorPower_of_isOpen_span P T' s' _ hT'⟩
  have hjy : spaComapLocHom P Aplus T s S hden y ∈ spaBasicOpen Aplus p.num p.den :=
    hpV ▸ ⟨y, hy, rfl⟩
  -- the ring isomorphism `A⟨p⟩ ≅ A⟨T/s⟩⟨p'⟩` of Remark 8.4; pulling back along it is injective
  let f := (presentationLimitRationalIso Aplus hAplus p hT').inv ≫
    presentationLimitMap (P := P) hpV.le ≫
    (presentationLimitLocIso P Aplus T s S hden hAplus hT _ hV
      (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W)).hom ≫
    presentationLimitMap (P := completionLocalization P T s S hden) hVW.ge ≫
    (presentationLimitRationalIso _ hAplus' p' hp').hom
  have hiso : IsIso f := by
    simp only [f]
    rw [← eqToHom_presentationLimit hpV.symm (congrArg _ hpV.symm),
      ← eqToHom_presentationLimit hVW (congrArg _ hVW)]
    infer_instance
  refine comap_injective (ConcreteCategory.bijective_of_isIso
    ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map f)).2 ?_
  refine ((comap_hom_comap_hom _ _ _).trans ((comap_hom_comap_hom _ _ _).trans ?_)).trans
    (comap_presentationLimitLocIso_rationalLocalizationPoint P Aplus T s S hden hAplus hP hT hV
      (spaComapLoc_functor_obj_le_spaBasicOpen P Aplus hP T s S hden W) p hT' hpV p' hp' hVW y
      hy).symm
  rw [Category.assoc, map_comp_presentationLimitRationalGerm_comp_of_isLocStalkMap P Aplus T s S
      hden hAplus hP hT y θ hθ p' hp' hy p hT' hpV hjy,
    comap_presentationLimitRationalGerm_presentationLimitStalkValuation hAplus hP p hT' _ hjy]
  -- the two names of the point `j(y)`
  congr 1
  exact congrFun (coe_spaComapLocHom P Aplus T s S hden) y

-- After forgetting the topology on sections, the component of the isomorphism of presheafed
-- spaces at `W` is the forgetful image of the component of the inverse of Remark 8.4.
private theorem toRingPresheafedSpaceHom_restrictLocPresheafedSpaceIso_c_app :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      (PreAdicSpace.toRingPresheafedSpaceHom
          (restrictLocPresheafedSpaceIso P Aplus T s S hden hAplus hP hT).hom).c.app (op W) =
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          ((presentationLimitPresheafLocIso P Aplus T s S hden hAplus hP hT).inv.app (op W)) := by
  intro W
  rfl

-- The stalk maps of the isomorphism of presheafed spaces, followed by the identification of the
-- stalks of the restriction, satisfy the germ condition `IsLocStalkMap`: on a rational open `W`,
-- the component of the isomorphism is the inverse of `presentationLimitLocImageIso`.
private theorem isLocStalkMap_stalkMap_comp_restrictStalkIso :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ x : spa (completedPlusSubring P Aplus T s S hden),
      IsLocStalkMap P Aplus T s S hden hAplus hP hT x
        ((PreAdicSpace.toRingPresheafedSpaceHom
            (restrictLocPresheafedSpaceIso P Aplus T s S hden hAplus hP hT).hom).stalkMap x ≫
          ((presentationLimitPreAdicSpace P Aplus hAplus hP).toRingPresheafedSpace.restrictStalkIso
            (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden) x).hom) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro x W hW hx
  have hsm := PresheafedSpace.stalkMap_germ (PreAdicSpace.toRingPresheafedSpaceHom
    (restrictLocPresheafedSpaceIso P Aplus T s S hden hAplus hP hT).hom) W x hx
  have hrs := PresheafedSpace.restrictStalkIso_hom_eq_germ
    (presentationLimitPreAdicSpace P Aplus hAplus hP).toRingPresheafedSpace
    (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden) W x hx
  -- the component at `W` of the inverse of Wedhorn's Remark 8.4 isomorphism
  have hc : (presentationLimitPresheafLocIso P Aplus T s S hden hAplus hP hT).inv.app (op W) =
      eqToHom (presentationLimitPresheaf_obj _ _ (op W)) ≫
        (presentationLimitLocImageIso P Aplus T s S hden hAplus hP hT W hW).inv ≫
        eqToHom (presentationLimitPresheaf_obj P Aplus _).symm := by
    rw [← cancel_epi ((presentationLimitPresheafLocIso P Aplus T s S hden hAplus hP hT).hom.app
      (op W)), Iso.hom_inv_id_app, presentationLimitPresheafLocIso_hom_app P Aplus T s S hden
      hAplus hP hT W hW]
    simp
  -- the germ maps of the stalk map and of the identification of the restricted stalk
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hsm).trans
    ((Category.assoc _ _ _).trans ((congrArg ((PreAdicSpace.toRingPresheafedSpaceHom
      (restrictLocPresheafedSpaceIso P Aplus T s S hden hAplus hP hT).hom).c.app (op W) ≫ ·)
        hrs).trans ?_)))
  rw [toRingPresheafedSpaceHom_restrictLocPresheafedSpaceIso_c_app, hc, Functor.map_comp,
    Functor.map_comp, eqToHom_map, eqToHom_map]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))

-- The isomorphism of presheafed spaces is compatible with the stalk valuations: through the stalk
-- maps it carries the valuation at `j(y)` to the valuation at `y`.
private noncomputable def restrictLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (presentationLimitPreAdicSpace P Aplus hAplus hP).restrict
        (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden) ⟶
      presentationLimitPreAdicSpace (completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden)
        (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden)
        (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  { toHom := (restrictLocPresheafedSpaceIso P Aplus T s S hden hAplus hP hT).hom
    stalkValuation_eq := by
      have _ := isUniformAddGroup_locUniformSpace P T s S hden
      have _ := isTopologicalRing_locUniformSpace P T s S hden
      intro x
      have h1 := PreAdicSpace.stalkValuation_restrict
        (presentationLimitPreAdicSpace P Aplus hAplus hP)
        (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden) x
      rw [PreAdicSpace.restrictStalkIso_def (presentationLimitPreAdicSpace P Aplus hAplus hP)
        (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden) x] at h1
      refine (presentationLimitPreAdicSpace_stalkValuation _ _
        (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden)
        (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden)
        x).trans ((presentationLimitStalkValuation_eq_comap_of_isLocStalkMap P Aplus T s S hden
        hAplus hP hT x _ (isLocStalkMap_stalkMap_comp_restrictStalkIso P Aplus T s S hden hAplus hP
        hT x)).trans ((comap_hom_comap_hom _ _ _).symm.trans (congrArg _ ?_)))
      exact (congrArg _ (presentationLimitPreAdicSpace_stalkValuation P Aplus hAplus hP
        (spaComapLocHom P Aplus T s S hden x)).symm).trans h1.symm }

/-- **Wedhorn's Remark 8.8 for the presentation-limit pre-adic spaces.** Let `U = R(T/s)` be a
rational subset of `X = Spa(A, A⁺)`, where `T` spans an open ideal, `A⁺` consists of power-bounded
elements and contains the ring of definition, and let `j : Spa(A⟨T/s⟩, A_U⁺) → X` be the open
embedding induced by the structure map. The restriction of the pre-adic space `X` along `j` is
isomorphic in `𝒱^pre` to the pre-adic space `Spa(A⟨T/s⟩, A_U⁺)`: the isomorphism is the identity
on points, it is `presentationLimitPresheafLocIso` on sections
(`presentationLimitPreAdicSpaceLocIso_hom_toHom`), and it matches the stalk valuations. -/
noncomputable def presentationLimitPreAdicSpaceLocIso :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (presentationLimitPreAdicSpace P Aplus hAplus hP).restrict
        (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden) ≅
      presentationLimitPreAdicSpace (completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden)
        (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden)
        (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  haveI := PreAdicSpace.isIso_of_isIso_toHom (restrictLocHom P Aplus T s S hden hAplus hP hT)
    (hf := (restrictLocPresheafedSpaceIso P Aplus T s S hden hAplus hP hT).isIso_hom)
  asIso (restrictLocHom P Aplus T s S hden hAplus hP hT)

/-- On points, `presentationLimitPreAdicSpaceLocIso` is the identity. -/
@[simp]
theorem presentationLimitPreAdicSpaceLocIso_hom_base :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (presentationLimitPreAdicSpaceLocIso P Aplus T s S hden hAplus hP hT).hom.base = 𝟙 _ :=
  (rfl)

/-- The underlying isomorphism of presheafed spaces of `presentationLimitPreAdicSpaceLocIso` is the
identity on points together with `presentationLimitPresheafLocIso`, Wedhorn's Remark 8.4 for the
presentation-limit presheaves, on sections. -/
theorem presentationLimitPreAdicSpaceLocIso_hom_toHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (presentationLimitPreAdicSpaceLocIso P Aplus T s S hden hAplus hP hT).hom.toHom =
      (PresheafedSpace.isoOfComponents (Iso.refl _)
        (presentationLimitPresheafLocIso P Aplus T s S hden hAplus hP hT) :
          ((presentationLimitPreAdicSpace P Aplus hAplus hP).restrict
            (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden)).toPresheafedSpace ≅
          (presentationLimitPreAdicSpace (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden)
            (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden)
            (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden)
            ).toPresheafedSpace).hom :=
  (rfl)

include hT in
/-- **The restriction of `Spa(A, A⁺)` along `j : Spa(A⟨T/s⟩, A_U⁺) → Spa(A, A⁺)` is an affinoid
pre-adic space**, isomorphic in `𝒱^pre` to the pre-adic space of the Huber pair
`(A⟨T/s⟩, A_U⁺)`. -/
theorem isAffinoid_restrict_spaComapLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    PreAdicSpace.isAffinoid ((presentationLimitPreAdicSpace P Aplus hAplus hP).restrict
      (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let S' : Pair (UniformSpace.Completion S) :=
    ⟨completedPlusSubring P Aplus T s S hden, isRingOfIntegralElements_completedPlusSubring P Aplus
      (fun j _ ↦ hP j.2) hAplus T s S hden⟩
  exact ObjectProperty.prop_of_iso PreAdicSpace.isAffinoid
    (presentationLimitPreAdicSpaceLocIso P Aplus T s S hden hAplus hP hT).symm
    (PreAdicSpace.isAffinoid_presentationLimitPreAdicSpace S' (completionLocalization P T s S hden)
      (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden))

/-- **Rational subsets are open affinoid subspaces.** For `T` spanning an open ideal, the rational
subset `R(T/s)` of the presentation-limit pre-adic space `Spa(A, A⁺)` is an open affinoid subspace:
the restriction to it is isomorphic in `𝒱^pre` to `Spa(A⟨T/s⟩, A_U⁺)`. -/
theorem spaBasicOpen_mem_affinoidOpens {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    spaBasicOpen Aplus T s ∈ (presentationLimitPreAdicSpace P Aplus hAplus hP).affinoidOpens := by
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have hrange : Set.range (Opens.inclusion' (spaBasicOpen Aplus T s)) =
      Set.range (spaComapLocHom P Aplus T s _ hden) := by
    rw [Opens.set_range_inclusion', coe_spaComapLocHom, range_spaComapLoc P Aplus hP T s _ hden]
  exact ObjectProperty.prop_of_iso PreAdicSpace.isAffinoid
    ((presentationLimitPreAdicSpace P Aplus hAplus hP).restrictIsoOfRangeEq _
      (isOpenEmbedding_spaComapLocHom P Aplus hP T s _ hden) hrange).symm
    (isAffinoid_restrict_spaComapLocHom P Aplus T s _ hden hAplus hP hT)

/-- **Every rational open is an open affinoid subspace** of the presentation-limit pre-adic space
`Spa(A, A⁺)`. -/
theorem spaRationalOpens_subset_affinoidOpens :
    spaRationalOpens Aplus ⊆ (presentationLimitPreAdicSpace P Aplus hAplus hP).affinoidOpens := by
  intro U hU
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hU
  exact spaBasicOpen_mem_affinoidOpens P Aplus hAplus hP hT

/-- **The open affinoid subspaces of `Spa(A, A⁺)` form a basis of its topology**, since the
rational opens do. This is the basis hypothesis of
`TauCeti.PreAdicSpace.isSheafy_of_isAdapted_of_isSheaf_affinoidOpens`. -/
theorem isBasis_affinoidOpens_presentationLimitPreAdicSpace [IsHuberRing A] :
    Opens.IsBasis (presentationLimitPreAdicSpace P Aplus hAplus hP).affinoidOpens := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens Aplus) hx
  exact ⟨V, spaRationalOpens_subset_affinoidOpens P Aplus hAplus hP hV, hxV, hVU⟩

/-- **`Spa(A, A⁺)` is a pre-adic space** (Wedhorn, Remark and Definition 8.10): the
presentation-limit pre-adic space of `A` with a plus ring `A⁺` of power-bounded elements containing
the ring of definition is locally affinoid, since the whole space is a rational open and so an
open affinoid subspace, and its structure presheaf is adapted to the open affinoid subspaces,
since it is adapted to the rational opens, which are among them. -/
theorem isPreAdic_presentationLimitPreAdicSpace :
    PreAdicSpace.isPreAdic (presentationLimitPreAdicSpace P Aplus hAplus hP) :=
  ⟨fun x ↦ ⟨⊤, spaRationalOpens_subset_affinoidOpens P Aplus hAplus hP
      (top_mem_spaRationalOpens Aplus), Opens.mem_top x⟩,
    (isAdapted_presentationLimitPresheaf (P := P) (Aplus := Aplus)).mono
      (spaRationalOpens_subset_affinoidOpens P Aplus hAplus hP)⟩

end TauCeti.ValuationSpectrum

namespace TauCeti.PreAdicSpace

universe u

/-- **Affinoid pre-adic spaces are pre-adic spaces** (Wedhorn, Remark and Definition 8.10): an
object of `𝒱^pre` isomorphic to some `Spa(A, A⁺)` is locally affinoid with structure presheaf
adapted to its open affinoid subspaces. -/
theorem isPreAdic_of_isAffinoid {X : PreAdicSpace.{u}} (hX : isAffinoid X) : isPreAdic X := by
  rw [isAffinoid_iff] at hX
  obtain ⟨A, _, _, _, _, S, P, hP, ⟨e⟩⟩ := hX
  exact ObjectProperty.prop_of_iso isPreAdic e.symm
    (ValuationSpectrum.isPreAdic_presentationLimitPreAdicSpace P S.plus _ hP)

end TauCeti.PreAdicSpace
