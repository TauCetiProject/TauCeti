/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.MarkedModel.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers

/-!
# Marked models over a discrete valuation ring

For a discrete valuation ring `R` with a chosen fraction field `K`, `TauCeti.Model R K C toK` is
the category of flat finitely presented models of a scheme `C` over `Spec K`, with the generic
fibre computed as the scalar extension along `R → K`. This file identifies it with the category
`TauCeti.MarkedModel (Spec R) C _` of marked models over the scheme `Spec R`, whose generic fibre
is computed along the generic point `Spec K(Spec R) ⟶ Spec R`.

The two fraction fields are related by the canonical isomorphism
`TauCeti.specFractionRingIsoFunctionField R K : Spec K ≅ Spec K(Spec R)` over `Spec R`, and the
marking of `C` over `Spec K(Spec R)` is `toK` followed by it. The generic fibre
`TauCeti.genericFiber R K` of a marked model is then identified with `C` over `Spec K`
(`TauCeti.MarkedModel.fractionRingGenericFiberIso`), compatibly with the marking. The equivalence
`TauCeti.Model.markedModelEquivalence` preserves total spaces, structure morphisms and the
inclusions of the marked generic fibres, and acts as the identity on morphisms of total spaces;
in particular it preserves properness.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

namespace Model

/-- A model over a discrete valuation ring, regarded as a marked model over the scheme `Spec R`.
The total space, structure morphism and generic-fibre inclusion are unchanged. -/
-- The body is exposed so that the total spaces agree by definition, as the comparison of morphisms
-- requires.
@[expose] def toMarkedModel (M : Model R K C toK) :
    MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom) where
  total := M.total
  toBase := M.toBase
  flat := M.flat
  locallyOfFinitePresentation := M.locallyOfFinitePresentation
  quasiCompact := M.quasiCompact
  quasiSeparated := M.quasiSeparated
  genericι := M.genericι
  isPullback := M.isPullback_genericι.of_iso (Iso.refl _) (Iso.refl _)
    (specFractionRingIsoFunctionField R K) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma toMarkedModel_total (M : Model R K C toK) : M.toMarkedModel.total = M.total :=
  (rfl)

@[simp]
lemma toMarkedModel_toBase (M : Model R K C toK) : M.toMarkedModel.toBase = M.toBase :=
  (rfl)

@[simp]
lemma toMarkedModel_genericι (M : Model R K C toK) : M.toMarkedModel.genericι = M.genericι :=
  (rfl)

/-- A proper model over a discrete valuation ring is a proper marked model. -/
instance isProper_toMarkedModel (M : Model R K C toK) [M.IsProper] : M.toMarkedModel.IsProper :=
  ‹M.IsProper›

end Model

namespace MarkedModel

omit [IsDiscreteValuationRing R] in
/-- For a marked model over `Spec R` with marking `toK` followed by `Spec K ≅ Spec K(Spec R)`, the
marked scheme `C` is also the scalar extension of the total space along `R → K`. -/
lemma isPullback_specMap
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    IsPullback M.genericι toK M.toBase (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  M.isPullback.of_iso (Iso.refl _) (Iso.refl _) (specFractionRingIsoFunctionField R K).symm
    (Iso.refl _) (by simp) (by simp) (by simp) (by
      rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
        ← specFractionRingIsoFunctionField_hom_fromSpecStalk R K, Iso.inv_hom_id_assoc])

omit [IsDiscreteValuationRing R] in
/-- For a marked model over `Spec R` with marking `toK` followed by `Spec K ≅ Spec K(Spec R)`, the
identification of the generic fibre `TauCeti.genericFiber R K M.toBase`, computed as the scalar
extension along `R → K`, with `C` over `Spec K`. It agrees with the marking
`TauCeti.MarkedModel.genericFiberIso` through `Spec K ≅ Spec K(Spec R)`
(`TauCeti.MarkedModel.fractionRingGenericFiberIso_hom_left`). -/
def fractionRingGenericFiberIso
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    genericFiber R K M.toBase ≅ Over.mk toK :=
  Over.isoMk M.isPullback_specMap.isoPullback.symm (IsPullback.isoPullback_inv_snd _)

omit [IsDiscreteValuationRing R] in
/-- The identification of the scalar-extension generic fibre with `C`, followed by the inclusion of
`C`, is the projection of the generic fibre. -/
@[reassoc (attr := simp)]
lemma fractionRingGenericFiberIso_hom_left_genericι
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    M.fractionRingGenericFiberIso.hom.left ≫ M.genericι = genericFiberι R K M.toBase :=
  M.isPullback_specMap.isoPullback_inv_fst

omit [IsDiscreteValuationRing R] in
/-- The identification of the scalar-extension generic fibre with `C` is the marking, precomposed
with the comparison of the generic fibres along `R → K` and along the generic point of `Spec R`. -/
lemma fractionRingGenericFiberIso_hom_left
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    M.fractionRingGenericFiberIso.hom.left =
      pullback.map M.toBase (Spec.map (CommRingCat.ofHom (algebraMap R K))) M.toBase
          ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))) (𝟙 _)
          (specFractionRingIsoFunctionField R K).hom (𝟙 _) (by simp) (by simp) ≫
        M.genericFiberIso.hom :=
  M.isPullback.hom_ext (by simp) (by
    rw [← Category.assoc]
    simpa using congrArg (· ≫ (specFractionRingIsoFunctionField R K).hom)
      (Over.w M.fractionRingGenericFiberIso.hom))

/-- A marked model over the spectrum of a discrete valuation ring, regarded as a model over the
ring with generic fibre computed along a chosen fraction field `K`. The total space, structure
morphism and generic-fibre inclusion are unchanged. -/
-- The body is exposed so that the total spaces agree by definition, as the comparison of morphisms
-- requires.
@[expose] def toModel
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    Model R K C toK :=
  Model.ofIsPullback M.toBase M.isPullback_specMap

variable (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom))

@[simp]
lemma toModel_total : M.toModel.total = M.total :=
  (rfl)

@[simp]
lemma toModel_toBase : M.toModel.toBase = M.toBase :=
  (rfl)

@[simp]
lemma toModel_genericι : M.toModel.genericι = M.genericι :=
  (Model.genericι_ofIsPullback _ _).trans (Category.comp_id _)

/-- The generic-fibre identification of the model attached to a marked model is the identification
of the scalar-extension generic fibre with `C`. -/
@[simp]
lemma toModel_genericFiberIso : M.toModel.genericFiberIso = M.fractionRingGenericFiberIso :=
  (rfl)

/-- A proper marked model over the spectrum of a discrete valuation ring is a proper model. -/
instance isProper_toModel [M.IsProper] : M.toModel.IsProper :=
  ‹M.IsProper›

end MarkedModel

namespace Model

/-- Regarding models over a discrete valuation ring as marked models over its spectrum, as a
functor. It acts as the identity on maps of total spaces. -/
-- The body is exposed so that its objects compute to `TauCeti.Model.toMarkedModel`.
@[expose] def toMarkedModelFunctor :
    Model R K C toK ⥤
      MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom) where
  obj := toMarkedModel
  map f := ⟨f.hom, f.overBase, genericι_hom f⟩
  map_id M := by
    apply MarkedModel.hom_ext
    simp only [MarkedModel.id_hom, id_hom]
    -- The two identities are of the same scheme, the total spaces agreeing by definition.
    rfl
  map_comp f g := by
    apply MarkedModel.hom_ext
    simp only [MarkedModel.comp_hom, comp_hom]
    -- Both sides are `f.hom ≫ g.hom`, between total spaces agreeing by definition.
    rfl

@[simp]
lemma toMarkedModelFunctor_obj (M : Model R K C toK) :
    toMarkedModelFunctor.obj M = M.toMarkedModel :=
  (rfl)

@[simp]
lemma toMarkedModelFunctor_map_hom {M N : Model R K C toK} (f : M ⟶ N) :
    (toMarkedModelFunctor.map f).hom = f.hom :=
  (rfl)

/-- Regarding marked models over the spectrum of a discrete valuation ring as models over the ring,
as a functor. It acts as the identity on maps of total spaces. -/
-- The body is exposed so that its objects compute to `TauCeti.MarkedModel.toModel`.
@[expose] def ofMarkedModelFunctor :
    MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom) ⥤
      Model R K C toK where
  obj := MarkedModel.toModel
  map {M N} f := ⟨f.hom, f.overBase, baseChangeHom_genericFiberIso_hom_left (M := M.toModel)
    (N := N.toModel) f.hom f.overBase
    (by rw [MarkedModel.toModel_genericι, MarkedModel.toModel_genericι]; exact f.genericι_hom)⟩
  map_id M := by
    apply Hom.ext
    simp only [MarkedModel.id_hom, id_hom]
    -- The two identities are of the same scheme, the total spaces agreeing by definition.
    rfl
  map_comp f g := by
    apply Hom.ext
    simp only [MarkedModel.comp_hom, comp_hom]
    -- Both sides are `f.hom ≫ g.hom`, between total spaces agreeing by definition.
    rfl

@[simp]
lemma ofMarkedModelFunctor_obj
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    ofMarkedModelFunctor.obj M = M.toModel :=
  (rfl)

@[simp]
lemma ofMarkedModelFunctor_map_hom
    {M N : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)}
    (f : M ⟶ N) : (ofMarkedModelFunctor.map f).hom = f.hom :=
  (rfl)

/-- Over a discrete valuation ring `R` with fraction field `K`, models of `C` over `R` are
equivalent to marked models of `C` over the scheme `Spec R`, with marking `toK` followed by the
isomorphism `Spec K ≅ Spec K(Spec R)`. Both functors preserve total spaces, structure morphisms
and generic-fibre inclusions, and act as the identity on maps of total spaces; the components of
the unit and counit are identities of total spaces. -/
-- The body is exposed so that the components of its unit and counit are stated between total
-- spaces that agree by definition.
@[expose] def markedModelEquivalence :
    Model R K C toK ≌
      MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom) where
  functor := toMarkedModelFunctor
  inverse := ofMarkedModelFunctor
  unitIso := NatIso.ofComponents
    (fun M ↦ ({
      hom := ⟨𝟙 _, Category.id_comp _, baseChangeHom_genericFiberIso_hom_left _ _ (by
        rw [MarkedModel.toModel_genericι, toMarkedModel_genericι]; exact Category.comp_id _)⟩
      inv := ⟨𝟙 _, Category.id_comp _, baseChangeHom_genericFiberIso_hom_left _ _ (by
        rw [MarkedModel.toModel_genericι, toMarkedModel_genericι]; exact Category.comp_id _)⟩
      hom_inv_id := Hom.ext (by rw [comp_hom, id_hom]; exact Category.id_comp _)
      inv_hom_id := Hom.ext (by rw [comp_hom, id_hom]; exact Category.id_comp _) } :
        M ≅ M.toMarkedModel.toModel))
    fun f ↦ Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents
    (fun M ↦ MarkedModel.isoMk (Iso.refl M.total) (Category.id_comp _)
      ((Category.comp_id _).trans M.toModel_genericι))
    fun f ↦ by
      apply MarkedModel.hom_ext
      rw [MarkedModel.comp_hom, MarkedModel.comp_hom]
      -- The components are stated between the objects of the composite functor, which agree
      -- with the given marked models only up to unfolding the exposed functors.
      erw [MarkedModel.isoMk_hom_hom, MarkedModel.isoMk_hom_hom]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  functor_unitIso_comp M := MarkedModel.hom_ext
    ((Category.id_comp _).trans (MarkedModel.isoMk_hom_hom _ _ _))

@[simp]
lemma markedModelEquivalence_functor :
    markedModelEquivalence.functor = toMarkedModelFunctor (R := R) (K := K) (toK := toK) :=
  (rfl)

@[simp]
lemma markedModelEquivalence_inverse :
    markedModelEquivalence.inverse = ofMarkedModelFunctor (R := R) (K := K) (toK := toK) :=
  (rfl)

@[simp]
lemma markedModelEquivalence_unitIso_hom_app_hom (M : Model R K C toK) :
    (markedModelEquivalence.unitIso.hom.app M).hom = 𝟙 M.total :=
  (rfl)

@[simp]
lemma markedModelEquivalence_unitIso_inv_app_hom (M : Model R K C toK) :
    (markedModelEquivalence.unitIso.inv.app M).hom = 𝟙 M.total :=
  (rfl)

@[simp]
lemma markedModelEquivalence_counitIso_hom_app_hom
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    (markedModelEquivalence.counitIso.hom.app M).hom = 𝟙 M.total :=
  MarkedModel.isoMk_hom_hom _ _ _

@[simp]
lemma markedModelEquivalence_counitIso_inv_app_hom
    (M : MarkedModel (Spec (.of R)) C (toK ≫ (specFractionRingIsoFunctionField R K).hom)) :
    (markedModelEquivalence.counitIso.inv.app M).hom = 𝟙 M.total :=
  MarkedModel.isoMk_inv_hom _ _ _

end Model

end TauCeti
