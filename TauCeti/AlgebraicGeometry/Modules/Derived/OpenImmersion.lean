/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction
public import TauCeti.Algebra.Homology.HomotopyCategory.Functor
public import TauCeti.Algebra.Homology.HomotopyCategory.KInjective
public import TauCeti.AlgebraicGeometry.Modules.Derived.Restrict
public import TauCeti.AlgebraicGeometry.Modules.Derived.TotalDirectImage
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Pushforward

/-!
# Total direct images along open immersions

For an open immersion `j : U ⟶ X`, this file compares the total direct image
`Rj_* : D(𝒪_U) ⥤ D(𝒪_X)` (`AlgebraicGeometry.Scheme.Hom.totalDirectImage`) with derived restriction
`K ↦ K|_U` (`AlgebraicGeometry.Scheme.Hom.derivedRestrict`).

* `Scheme.Modules.isKInjective_restrictFunctor_mapHomologicalComplex_obj`: restriction along an open
  immersion preserves K-injective complexes, because up to an equivalence it is right adjoint to
  the exact functor of extension by zero.
* `Scheme.Hom.totalDirectImageCompDerivedRestrictIso`: the derived counit `(Rj_* K)|_U ≅ K`, induced
  by the counit isomorphism `(j_* M)|_U ≅ M` of module sheaves.
* `Scheme.Hom.totalDirectImageRestrict`: for open immersions `i : W ⟶ U` and `j : U ⟶ X` with
  composite `k`, the restriction map `Rj_* K ⟶ Rk_* (K|_W)`, induced by the restriction map
  `j_* M ⟶ k_* (M|_W)` of module sheaves (`Scheme.Modules.pushforwardRestriction`, constructed
  with its termwise properties in `TauCeti.AlgebraicGeometry.Modules.Restriction.Pushforward`).
* `Scheme.Hom.derivedRestrict_map_totalDirectImageRestrict_app`: restricted to `W`, the
  restriction map followed by the derived counit of `k` is the restriction of the derived counit
  of `j`.
* `TauCeti.AlgebraicGeometry.Coherent.isIso_derivedRestrict_map_totalDirectImageRestrict_app`: for
  opens `W ≤ V` and `U` of `X` with `U ⊓ V ≤ W`, the restriction map `R(V.ι)_* K ⟶ R(W.ι)_* (K|_W)`
  becomes an isomorphism after restriction to `U`, a base change property of open immersions.

Natural transformations out of `Rj_*` and out of `Rj_* ⋙ G` for any functor `G` are constructed and
compared through the universal property of right derived functors
(`CategoryTheory.Functor.isRightDerivedFunctor_rightDerivedFunctor_comp`), so that they are
determined by their values on all complexes; isomorphisms are checked on K-injective complexes,
where `Rj_*` is computed termwise. These are the inputs of the gluing of objects of `D(𝒪_X)` along
two opens, `TauCeti.AlgebraicGeometry.Coherent.exists_derivedGluing_two_opens`.

## References

* [Stacks: Lemma 20.45.1](https://stacks.math.columbia.edu/tag/08DG), whose proof uses these
  comparisons.
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory Functor TauCeti

universe w₁ w₂ w₃ w₄ u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction along an open immersion sends K-injective complexes of module sheaves to
K-injective complexes. Restriction to an open subscheme is, up to an equivalence, a right adjoint
whose left adjoint, extension by zero, is exact. -/
theorem isKInjective_restrictFunctor_mapHomologicalComplex_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : CochainComplex Y.Modules ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((restrictFunctor f).mapHomologicalComplex (.up ℤ)).obj I) := by
  have hU (U : Y.Opens) (J : CochainComplex Y.Modules ℤ) [J.IsKInjective] :
      CochainComplex.IsKInjective
        (((restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj J) := by
    -- The left adjoint of restriction to `U` is extension by zero from the slice site, up to the
    -- equivalence `Scheme.Modules.overEquiv U`; it is exact.
    let P := SheafOfModules.pullback.{u} (F := Over.forget U) (𝟙 (Y.ringCatSheaf.over U))
    let L : U.toScheme.Modules ⥤ Y.Modules := (overEquiv U).inverse ⋙ P
    let adj : L ⊣ restrictFunctor U.ι :=
      ((overEquiv U).symm.toAdjunction.comp
        (SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U)
          (𝟙 (Y.ringCatSheaf.over U)))).ofNatIsoRight (overFunctorEquiv U)
    have h : PreservesFiniteLimits ((overEquiv U).inverse ⋙ P) := inferInstance
    have : PreservesFiniteLimits L := h
    exact CochainComplex.isKInjective_map_of_adjunction adj J
  let e := f.isoOpensRange
  let i : restrictFunctor f.opensRange.ι ⋙ restrictFunctor e.hom ≅ restrictFunctor f :=
    (restrictFunctorComp e.hom f.opensRange.ι).symm ≪≫ restrictFunctorCongr f.isoOpensRange_hom_ι
  have := hU f.opensRange I
  -- Restriction along the isomorphism `e` is an equivalence, with left adjoint its inverse.
  let adj : (restrictEquivalence e).inverse ⊣ restrictFunctor e.hom :=
    (restrictEquivalence e).symm.toAdjunction.ofNatIsoRight
      (eqToIso (by rw [Equivalence.symm_inverse, restrictEquivalence_functor]))
  exact (CochainComplex.isKInjective_iff_of_iso
    ((Functor.mapHomologicalComplexCompIso i (.up ℤ)).app I)).1
      (CochainComplex.isKInjective_map_of_adjunction adj _)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {W U X : Scheme.{u}} [HasDerivedCategory.{w₁} W.Modules]
  [HasDerivedCategory.{w₂} U.Modules] [HasDerivedCategory.{w₃} X.Modules]

section Counit

variable (j : U ⟶ X) [IsOpenImmersion j]

/-- The transformation `(j_* K)|_U ⟶ K` on complexes of module sheaves on `U` induced by the counit
of the adjunction between restriction and pushforward along the open immersion `j`, from which
`Scheme.Hom.totalDirectImageCompDerivedRestrictIso` is derived. -/
private def totalDirectImageCompDerivedRestrictAux :
    ((pushforward j).mapHomotopyCategory (.up ℤ) ⋙ Qh) ⋙ j.derivedRestrict ⟶ Qh ⋙ 𝟭 _ :=
  Quotient.natTransLift _
    { app K := (Modules.restrictFunctor j).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ _).obj (((pushforward j).mapHomologicalComplex _).obj K)) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (restrictAdjunction j).counit _).app K))
      naturality K L f := by
        have h := (Modules.restrictFunctor j).mapDerivedCategoryFactorsh.hom.naturality
          ((HomotopyCategory.quotient _ _).map (((pushforward j).mapHomologicalComplex _).map f))
        dsimp at h ⊢
        simp only [HomotopyCategory.quotient_functor_map, Functor.mapHomotopyCategory_map]
        rw [reassoc_of% h, ← Qh.map_comp, Category.assoc, ← Qh.map_comp, ← Functor.map_comp,
          ← Functor.map_comp]
        congr 3
        exact (NatTrans.mapHomologicalComplex (restrictAdjunction j).counit _).naturality f }

private lemma totalDirectImageCompDerivedRestrictAux_app (K : CochainComplex U.Modules ℤ) :
    (totalDirectImageCompDerivedRestrictAux j).app ((HomotopyCategory.quotient _ _).obj K) =
      (Modules.restrictFunctor j).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ _).obj (((pushforward j).mapHomologicalComplex _).obj K)) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (restrictAdjunction j).counit _).app K)) :=
  Quotient.natTransLift_app _ _ _ _ K

/-- On a complex `K` placed in the homotopy category, the auxiliary transformation of
`Scheme.Hom.totalDirectImageCompDerivedRestrictAux` is an isomorphism, induced by the counit
isomorphism `(j_* M)|_U ≅ M` of module sheaves. -/
private instance (K : HomotopyCategory U.Modules (.up ℤ)) :
    IsIso ((totalDirectImageCompDerivedRestrictAux j).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [totalDirectImageCompDerivedRestrictAux_app]
  have : IsIso ((NatTrans.mapHomologicalComplex (restrictAdjunction j).counit (.up ℤ)).app K) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
      (asIso (restrictAdjunction j).counit) (.up ℤ)).hom.app K))
  infer_instance

/-- The derived counit `(Rj_* K)|_U ≅ K` for an open immersion `j : U ⟶ X` and `K ∈ D(𝒪_U)`: the
total direct image along `j` followed by derived restriction along `j` is the identity of
`D(𝒪_U)`. It is induced by the counit isomorphism `(j_* M)|_U ≅ M` of module sheaves, through the
universal property of the right derived functor `Rj_* ⋙ j^*` of `j_* ⋙ j^*`; it is an
isomorphism because every complex is quasi-isomorphic to a K-injective one. -/
def totalDirectImageCompDerivedRestrictIso :
    j.totalDirectImage ⋙ j.derivedRestrict ≅ 𝟭 _ :=
  let τ := (j.totalDirectImage ⋙ j.derivedRestrict).rightDerivedDesc
      (whiskerRight (pushforward j).rightDerivedFunctorUnith j.derivedRestrict ≫
        (associator _ _ _).hom)
      (HomotopyCategory.quasiIso U.Modules (.up ℤ)) (𝟭 _)
      (totalDirectImageCompDerivedRestrictAux j)
  have : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro A
    refine (NatTrans.isIso_app_iff_of_iso _
      (asIso ((kInjectiveReplacementAdjunction U.Modules).counit.app A))).1 ?_
    have h := rightDerived_fac_app (j.totalDirectImage ⋙ j.derivedRestrict)
      (whiskerRight (pushforward j).rightDerivedFunctorUnith j.derivedRestrict ≫
        (associator _ _ _).hom) (HomotopyCategory.quasiIso U.Modules (.up ℤ)) (𝟭 _)
      (totalDirectImageCompDerivedRestrictAux j) ((kInjectiveReplacement U.Modules).obj A)
    simp only [NatTrans.comp_app, whiskerRight_app, associator_hom_app, Category.comp_id] at h
    exact IsIso.of_isIso_fac_left h
  asIso τ

/-- The derived counit `Scheme.Hom.totalDirectImageCompDerivedRestrictIso` on the image of a
complex `K` is induced by the counit `(j_* K)|_U ≅ K` of module sheaves, up to the comparison
`F(K) ⟶ RF(K)` of the total direct image and the identification of derived restriction on
complexes. -/
@[reassoc]
lemma totalDirectImageCompDerivedRestrictIso_hom_app_fac
    (K : CochainComplex U.Modules ℤ) :
    j.derivedRestrict.map ((pushforward j).rightDerivedFunctorUnith.app
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      (totalDirectImageCompDerivedRestrictIso j).hom.app
        (Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      (Modules.restrictFunctor j).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ _).obj (((pushforward j).mapHomologicalComplex _).obj K)) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (restrictAdjunction j).counit _).app K)) := by
  rw [← totalDirectImageCompDerivedRestrictAux_app]
  simpa [totalDirectImageCompDerivedRestrictIso] using rightDerived_fac_app
    (j.totalDirectImage ⋙ j.derivedRestrict)
    (whiskerRight (pushforward j).rightDerivedFunctorUnith j.derivedRestrict ≫
        (associator _ _ _).hom) (HomotopyCategory.quasiIso U.Modules (.up ℤ)) _
    (totalDirectImageCompDerivedRestrictAux j) ((HomotopyCategory.quotient _ _).obj K)

end Counit

section Restriction

variable (i : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X) (w : i ≫ j = k) [IsOpenImmersion i]

/-- The transformation `j_* K ⟶ Rk_* (K|_W)` on complexes of module sheaves on `U` induced by the
restriction map `Scheme.Modules.pushforwardRestriction`, from which
`Scheme.Hom.totalDirectImageRestrict` is derived. -/
private def totalDirectImageRestrictAux :
    (pushforward j).mapHomotopyCategory (.up ℤ) ⋙ Qh ⟶
      Qh ⋙ i.derivedRestrict ⋙ k.totalDirectImage :=
  Quotient.natTransLift _
    { app K := Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) _).app K)) ≫
        (pushforward k).rightDerivedFunctorUnith.app
          ((HomotopyCategory.quotient _ _).obj (((Modules.restrictFunctor i).mapHomologicalComplex
            _).obj K)) ≫
        k.totalDirectImage.map ((Modules.restrictFunctor i).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj K))
      naturality K L f := by
        have h₁ := (pushforward k).rightDerivedFunctorUnith.naturality
          ((HomotopyCategory.quotient _ _).map
            (((Modules.restrictFunctor i).mapHomologicalComplex _).map f))
        have h₂ := (Modules.restrictFunctor i).mapDerivedCategoryFactorsh.inv.naturality
          ((HomotopyCategory.quotient _ _).map f)
        -- `(restrictFunctor i ⋙ pushforward k).mapHomologicalComplex` is the composite of the
        -- functors on complexes by definition.
        have h₃ : ((pushforward j).mapHomologicalComplex _).map f ≫
            (NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) _).app L =
            (NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) _).app K ≫
              ((pushforward k).mapHomologicalComplex _).map
                (((Modules.restrictFunctor i).mapHomologicalComplex _).map f) :=
          (NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) (.up ℤ)).naturality f
        dsimp at h₁ h₂ ⊢
        simp only [HomotopyCategory.quotient_functor_map, Functor.mapHomotopyCategory_map]
        rw [← Qh.map_comp_assoc, ← Functor.map_comp, h₃, Functor.map_comp, Qh.map_comp_assoc,
          reassoc_of% h₁]
        simp only [Category.assoc, ← Functor.map_comp]
        rw [h₂] }

private lemma totalDirectImageRestrictAux_app (K : CochainComplex U.Modules ℤ) :
    (totalDirectImageRestrictAux i j k w).app ((HomotopyCategory.quotient _ _).obj K) =
      Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) _).app K)) ≫
        (pushforward k).rightDerivedFunctorUnith.app
          ((HomotopyCategory.quotient _ _).obj (((Modules.restrictFunctor i).mapHomologicalComplex
            _).obj K)) ≫
        k.totalDirectImage.map ((Modules.restrictFunctor i).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj K)) :=
  Quotient.natTransLift_app _ _ _ _ K

/-- The restriction map `Rj_* K ⟶ Rk_* (K|_W)` for open immersions `i : W ⟶ U` and
`j : U ⟶ X` with `i ≫ j = k`, natural in `K ∈ D(𝒪_U)`: the morphism of right derived functors
induced by the restriction map `j_* M ⟶ k_* (M|_W)` of module sheaves
(`Scheme.Modules.pushforwardRestriction`). -/
def totalDirectImageRestrict : j.totalDirectImage ⟶ i.derivedRestrict ⋙ k.totalDirectImage :=
  j.totalDirectImage.rightDerivedDesc (pushforward j).rightDerivedFunctorUnith
    (HomotopyCategory.quasiIso U.Modules (.up ℤ)) _ (totalDirectImageRestrictAux i j k w)

/-- On the image of a complex `K`, the restriction map `Scheme.Hom.totalDirectImageRestrict` is
induced by the restriction map of module sheaves, up to the comparisons `F(K) ⟶ RF(K)` of the
total direct images and the identification of derived restriction on complexes. -/
@[reassoc]
lemma totalDirectImageRestrict_app_fac
    (K : CochainComplex U.Modules ℤ) :
    (pushforward j).rightDerivedFunctorUnith.app ((HomotopyCategory.quotient _ _).obj K) ≫
      (totalDirectImageRestrict i j k w).app (Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) _).app K)) ≫
        (pushforward k).rightDerivedFunctorUnith.app
          ((HomotopyCategory.quotient _ _).obj (((Modules.restrictFunctor i).mapHomologicalComplex
            _).obj K)) ≫
        k.totalDirectImage.map ((Modules.restrictFunctor i).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj K)) := by
  rw [← totalDirectImageRestrictAux_app]
  exact rightDerived_fac_app _ _ _ _ _ _

end Restriction

section Compatibility

variable (i : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X) (w : i ≫ j = k) [IsOpenImmersion i]
  [IsOpenImmersion j] [IsOpenImmersion k]

omit [HasDerivedCategory W.Modules] [HasDerivedCategory U.Modules] [HasDerivedCategory X.Modules] in
/-- The restriction map of complexes followed by the counit of `k` is the restriction to `W` of
the counit of `j`, termwise by
`Scheme.Modules.restrictFunctorComp_inv_app_comp_restrictFunctor_map_pushforwardRestriction_app`. -/
private lemma mapHomologicalComplex_restrictFunctorComp_inv_comp_pushforwardRestriction
    (K : CochainComplex U.Modules ℤ) :
    (NatTrans.mapHomologicalComplex
        ((restrictFunctorComp i j).inv ≫ (restrictFunctorCongr w).hom) _).app
        (((pushforward j).mapHomologicalComplex _).obj K) ≫
      ((Modules.restrictFunctor k).mapHomologicalComplex _).map
        ((NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) _).app K) ≫
        (NatTrans.mapHomologicalComplex (restrictAdjunction k).counit _).app
          (((Modules.restrictFunctor i).mapHomologicalComplex _).obj K) =
      ((Modules.restrictFunctor i).mapHomologicalComplex _).map
        ((NatTrans.mapHomologicalComplex (restrictAdjunction j).counit _).app K) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  simpa using restrictFunctorComp_inv_app_comp_restrictFunctor_map_pushforwardRestriction_app
    i j k w (K.X n)

/-- The compatibility of restriction maps with derived counits on the image of a complex `K`,
after precomposition with the comparison `F(K) ⟶ RF(K)` of the total direct image along `j`. -/
private lemma derivedRestrict_map_totalDirectImageRestrict_app_aux
    (K : CochainComplex U.Modules ℤ) :
    k.derivedRestrict.map ((pushforward j).rightDerivedFunctorUnith.app
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      k.derivedRestrict.map ((totalDirectImageRestrict i j k w).app
        (Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
        (totalDirectImageCompDerivedRestrictIso k).hom.app
          (i.derivedRestrict.obj (Qh.obj ((HomotopyCategory.quotient _ _).obj K))) =
      k.derivedRestrict.map ((pushforward j).rightDerivedFunctorUnith.app
          ((HomotopyCategory.quotient _ _).obj K)) ≫
        (derivedRestrictComp i j k w).inv.app
          (j.totalDirectImage.obj (Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
          i.derivedRestrict.map ((totalDirectImageCompDerivedRestrictIso j).hom.app
            (Qh.obj ((HomotopyCategory.quotient _ _).obj K))) := by
  -- Both sides are computed on the complex `K` by the factorization lemmas of the restriction map
  -- and of the derived counits, and reduce to the identity of complexes
  -- `mapHomologicalComplex_restrictFunctorComp_inv_comp_pushforwardRestriction`. The source of
  -- `pushforwardRestriction` is `restrictFunctor i ⋙ pushforward k`, whose functor on complexes
  -- agrees with the composite of the functors on complexes only by definition; the two `erw`
  -- steps and the final `rfl` match these objects.
  have e₁ := (totalDirectImageCompDerivedRestrictIso k).hom.naturality
    ((Modules.restrictFunctor i).mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ _).obj K))
  have e₂ := (derivedRestrictComp i j k w).inv.naturality
    ((pushforward j).rightDerivedFunctorUnith.app ((HomotopyCategory.quotient _ _).obj K))
  have e₃ := (Modules.restrictFunctor k).mapDerivedCategoryFactorsh.hom.naturality
    ((HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (pushforwardRestriction i j k w) _).app K))
  have e₄ := (Modules.restrictFunctor i).mapDerivedCategoryFactorsh.hom.naturality
    ((HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (restrictAdjunction j).counit _).app K))
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Functor.mapHomotopyCategory_obj_quotient_obj] at e₁ e₂ ⊢
  simp only [Functor.comp_obj, Functor.comp_map, Functor.mapHomotopyCategory_map] at e₃ e₄
  rw [← Functor.map_comp_assoc, totalDirectImageRestrict_app_fac]
  simp only [Functor.map_comp, Category.assoc]
  rw [e₁, totalDirectImageCompDerivedRestrictIso_hom_app_fac_assoc
      k (((Modules.restrictFunctor i).mapHomologicalComplex _).obj K),
    reassoc_of% e₂, ← Functor.map_comp, totalDirectImageCompDerivedRestrictIso_hom_app_fac,
    ← cancel_epi ((derivedRestrictComp i j k w).hom.app (Qh.obj
      ((HomotopyCategory.quotient _ _).obj (((pushforward j).mapHomologicalComplex _).obj K)))),
    Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% e₃]
  rw [derivedRestrictComp_hom_app_Qh_obj_assoc, Functor.map_comp, ← cancel_mono
    ((Modules.restrictFunctor i).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [e₄, Category.comp_id, ← Qh.map_comp, ← Qh.map_comp, ← Functor.map_comp,
    mapHomologicalComplex_restrictFunctorComp_inv_comp_pushforwardRestriction]
  rfl

/-- **Restriction maps restrict to counits.** Restricted to `W` along `k`, the restriction map
`Rj_* K ⟶ Rk_* (K|_W)` followed by the derived counit `(Rk_* L)|_W ≅ L` of `k` is the restriction
to `W` of the derived counit `(Rj_* K)|_U ≅ K` of `j`, up to the comparison
`((Rj_* K)|_U)|_W ≅ (Rj_* K)|_W` of `Scheme.Hom.derivedRestrictComp`. -/
@[reassoc]
theorem derivedRestrict_map_totalDirectImageRestrict_app (A : DerivedCategory U.Modules) :
    k.derivedRestrict.map ((totalDirectImageRestrict i j k w).app A) ≫
        (totalDirectImageCompDerivedRestrictIso k).hom.app (i.derivedRestrict.obj A) =
      (derivedRestrictComp i j k w).inv.app (j.totalDirectImage.obj A) ≫
        i.derivedRestrict.map ((totalDirectImageCompDerivedRestrictIso j).hom.app A) := by
  -- Both sides are natural transformations out of `Rj_* ⋙ k^*`, a right derived functor, so they
  -- agree once they agree on the images of all complexes.
  have key : whiskerRight (totalDirectImageRestrict i j k w) k.derivedRestrict ≫
      (associator _ _ _).hom ≫
        whiskerLeft i.derivedRestrict (totalDirectImageCompDerivedRestrictIso k).hom ≫
          (rightUnitor _).hom =
      whiskerLeft j.totalDirectImage (derivedRestrictComp i j k w).inv ≫
        (associator _ _ _).inv ≫
          whiskerRight (totalDirectImageCompDerivedRestrictIso j).hom i.derivedRestrict ≫
            (leftUnitor _).hom := by
    apply (j.totalDirectImage ⋙ k.derivedRestrict).rightDerived_ext
      (whiskerRight (pushforward j).rightDerivedFunctorUnith k.derivedRestrict ≫
        (associator _ _ _).hom) (HomotopyCategory.quasiIso U.Modules (.up ℤ))
    ext K
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    simpa using derivedRestrict_map_totalDirectImageRestrict_app_aux i j k w K
  simpa using NatTrans.congr_app key A

end Compatibility

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.Coherent

open _root_.AlgebraicGeometry Scheme.Modules

variable {X : Scheme.{u}} {U V W : X.Opens} [HasDerivedCategory.{w₁} U.toScheme.Modules]
  [HasDerivedCategory.{w₂} V.toScheme.Modules] [HasDerivedCategory.{w₃} W.toScheme.Modules]
  [HasDerivedCategory.{w₄} X.Modules]

/-- **Restriction maps are isomorphisms away from `V \ W`.** For opens `W ≤ V` and `U` of
`X` with `U ⊓ V ≤ W`, the restriction map `R(V.ι)_* K ⟶ R(W.ι)_* (K|_W)` becomes an isomorphism
after restriction to `U`, for every `K ∈ D(𝒪_V)`. It is computed on a K-injective replacement of
`K`, whose restriction to `W` is K-injective, from the corresponding isomorphism of module sheaves
`Scheme.Modules.isIso_restrictFunctor_map_pushforwardRestriction_app`. -/
theorem isIso_derivedRestrict_map_totalDirectImageRestrict_app (hWV : W ≤ V) (hUVW : U ⊓ V ≤ W)
    (B : DerivedCategory V.toScheme.Modules) :
    IsIso (U.ι.derivedRestrict.map
      (((X.homOfLE hWV).totalDirectImageRestrict V.ι W.ι (X.homOfLE_ι hWV)).app B)) := by
  let ρ := (X.homOfLE hWV).totalDirectImageRestrict V.ι W.ι (X.homOfLE_ι hWV)
  refine (NatTrans.isIso_app_iff_of_iso (whiskerRight ρ U.ι.derivedRestrict)
    (asIso ((kInjectiveReplacementAdjunction _).counit.app B))).1 ?_
  let K := ((kInjectiveReplacement V.toScheme.Modules).obj B).as
  -- An object of the homotopy category is the image of its underlying complex `K`, so that the
  -- factorization lemma of the restriction map applies.
  change IsIso (U.ι.derivedRestrict.map (ρ.app (Qh.obj ((HomotopyCategory.quotient _ _).obj K))))
  have : CochainComplex.IsKInjective ((HomotopyCategory.quotient _ _).obj K).as :=
    isKInjective_kInjectiveReplacement_obj_as B
  have : CochainComplex.IsKInjective ((HomotopyCategory.quotient _ _).obj
      (((Scheme.Modules.restrictFunctor (X.homOfLE hWV)).mapHomologicalComplex
        (.up ℤ)).obj K)).as :=
    isKInjective_restrictFunctor_mapHomologicalComplex_obj (X.homOfLE hWV) K
  have h := Scheme.Hom.totalDirectImageRestrict_app_fac (X.homOfLE hWV) V.ι W.ι
    (X.homOfLE_ι hWV) K
  rw [← IsIso.eq_inv_comp] at h
  -- The restriction map of complexes is an isomorphism after restriction to `U`.
  let τ := (NatTrans.mapHomologicalComplex
    (pushforwardRestriction (X.homOfLE hWV) V.ι W.ι (X.homOfLE_ι hWV)) (.up ℤ)).app K
  have : IsIso (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map τ) := by
    have (n : ℤ) : IsIso ((((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
        (.up ℤ)).map τ).f n) :=
      isIso_restrictFunctor_map_pushforwardRestriction_app hWV hUVW (K.X n)
    exact HomologicalComplex.Hom.isIso_of_components _
  have hτ := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactorsh.hom.naturality
    ((HomotopyCategory.quotient _ _).map τ)
  simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at hτ
  have : IsIso (U.ι.derivedRestrict.map (Qh.map ((HomotopyCategory.quotient _ _).map τ))) := by
    have : IsIso (U.ι.derivedRestrict.map (Qh.map ((HomotopyCategory.quotient _ _).map τ)) ≫
        (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactorsh.hom.app _) := by
      rw [hτ]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactorsh.hom.app _)
  rw [h]
  simp only [Functor.map_comp]
  infer_instance

end TauCeti.AlgebraicGeometry.Coherent
