/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic
public import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.Derives
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Derived extension of scalars and its adjunction with restriction of scalars

For a homomorphism `f : R →+* S` of commutative rings, degreewise extension of scalars on cochain
complexes (`TauCeti.complexBaseChange f`) does not preserve arbitrary quasi-isomorphisms when `S`
is not flat over `R`, so it does not descend directly to derived categories. It does, however,
preserve quasi-isomorphisms between K-flat complexes of `R`-modules
(`TauCeti.quasiIso_complexBaseChange_map_of_isKFlat`).

Together with the K-flat left derivability structure on `CochainComplex (ModuleCat.{u} R) ℤ`, this
provides:
* existence of the left derived extension-of-scalars functor `- ⊗^L_R S : D(R) ⥤ D(S)`
  (`TauCeti.hasLeftDerivedFunctor_extendScalars`, `TauCeti.derivedExtendScalars`);
* invertibility of the derived comparison on K-flat complexes
  (`TauCeti.isIso_app_of_isKFlat_of_isLeftDerivedFunctor_extendScalars`);
* for any functor `F` inverting quasi-isomorphisms, existence and a K-flat characterization of left
  derived functors of `complexBaseChange f ⋙ F`
  (`TauCeti.hasLeftDerivedFunctor_extendScalars_of_inverts`,
  `TauCeti.isLeftDerivedFunctor_extendScalars_iff_isIso`), their computation on bounded-above flat
  complexes, and their absoluteness
  (`TauCeti.isLeftDerivedFunctor_comp_of_isLeftDerivedFunctor_extendScalars`);
* the derived adjunction `G ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory` for any left
  derived functor `(G, α)` of scalar extension (`TauCeti.derivedExtendRestrictScalarsAdj`,
  `TauCeti.nonempty_derivedExtendRestrictScalarsAdj`), together with the compatibility of its unit
  and counit on complex models with the degreewise lift of `ModuleCat.extendRestrictScalarsAdj f`,
  and the canonical adjunction `TauCeti.derivedExtendScalarsAdj` with the K-flat object
  isomorphism `TauCeti.derivedExtendScalarsKFlatIso`;
* on a flat module in degree zero, derived extension of scalars is the ordinary extension of
  scalars in degree zero (`TauCeti.derivedExtendScalarsSingleIso`).

## References

* [The Stacks Project][stacks], Section 15.60 (Tag 064L) and Section 15.61 (Tags 06Y6 and 0GMT).
* Georges Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés, revisité*,
  C. R. Math. Acad. Sci. Paris 344 (2007), no. 9, 549–552.
* Joël Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42, §5.3.4, and `CategoryTheory.Adjunction.derived` in
  `Mathlib.CategoryTheory.Functor.Derived.Adjunction`.
-/

public section

universe u w w'

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace TauCeti

section BaseChangeQuasiIso

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Degreewise scalar extension along `f : R →+* S` preserves quasi-isomorphisms between K-flat
cochain complexes of `R`-modules. -/
instance quasiIso_complexBaseChange_map_of_isKFlat
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso ((complexBaseChange f).map φ) := by
  let S₀ : ModuleCat.{u} R := (ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))
  let P₀ : CochainComplex (ModuleCat.{u} R) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj S₀
  have hP₀ : QuasiIso (tensorHom (𝟙 P₀) φ) := CochainComplex.quasiIso_id_tensorHom_of_isKFlat P₀ φ
  let e := complexBaseChangeCompRestrictScalarsIso f
  have hRes : QuasiIso (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((complexBaseChange f).map φ)) := by
    refine quasiIso_of_arrow_mk_iso (tensorHom (𝟙 P₀) φ)
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((complexBaseChange f).map φ)) ?_
    exact Arrow.isoMk (e.symm.app K) (e.symm.app L) (e.inv.naturality φ).symm
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((complexBaseChange f).map φ) (ModuleCat.restrictScalars.{u} f)).mp hRes

/-- The K-flat localizer morphism on `CochainComplex (ModuleCat.{u} R) ℤ` derives degreewise scalar
extension along `f : R →+* S` followed by `DerivedCategory.Q`. -/
theorem localizerMorphism_derives_complexBaseChange
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).Derives
      (complexBaseChange f ⋙ DerivedCategory.Q (C := ModuleCat.{u} S)) := by
  rw [LocalizerMorphism.Derives, CochainComplex.KFlat.localizerMorphism_functor]
  intro K L g hg
  have : QuasiIso g.hom := (CochainComplex.KFlat.quasiIso_iff g).1 hg
  simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.ι_obj]
  infer_instance

end BaseChangeQuasiIso

section DerivedExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- **Derived extension of scalars exists.** For `f : R →+* S`, degreewise scalar extension of
cochain complexes followed by localization to `DerivedCategory (ModuleCat.{u} S)` admits a left
derived functor with respect to quasi-isomorphisms of complexes of `R`-modules. -/
theorem hasLeftDerivedFunctor_extendScalars [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    (complexBaseChange f ⋙ DerivedCategory.Q (C := ModuleCat.{u} S)).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := (localizerMorphism_derives_complexBaseChange.{u, w} f).hasPointwiseLeftDerivedFunctor
  infer_instance

attribute [instance] hasLeftDerivedFunctor_extendScalars

/-- The canonical left derived extension-of-scalars functor `- ⊗^L_R S` from
`DerivedCategory (ModuleCat.{u} R)` to `DerivedCategory (ModuleCat.{u} S)`. -/
def derivedExtendScalars [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} S)] :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  (complexBaseChange f ⋙ DerivedCategory.Q).totalLeftDerived
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- The canonical counit comparison `Q ⋙ derivedExtendScalars f ⟶ complexBaseChange f ⋙ Q`. -/
def derivedExtendScalarsCounit [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} S)] :
    DerivedCategory.Q ⋙ derivedExtendScalars f ⟶ complexBaseChange f ⋙ DerivedCategory.Q :=
  (complexBaseChange f ⋙ DerivedCategory.Q).totalLeftDerivedCounit
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

instance instIsLeftDerivedFunctorDerivedExtendScalars
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)] :
    (derivedExtendScalars f).IsLeftDerivedFunctor (derivedExtendScalarsCounit f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  dsimp only [derivedExtendScalars, derivedExtendScalarsCounit]
  infer_instance

/-- On a K-flat complex `P` of `R`-modules, the comparison `α.app P` of any left derived
extension-of-scalars functor `(G, α)` is an isomorphism in `DerivedCategory (ModuleCat.{u} S)`. -/
instance isIso_app_of_isKFlat_of_isLeftDerivedFunctor_extendScalars
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (α.app P) := by
  have h := (localizerMorphism_derives_complexBaseChange f).isIso' α
    (CochainComplex.KFlat.mk P)
  have heq : (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).functor.obj
      (CochainComplex.KFlat.mk P) = P := by
    simp
  rwa [NatTrans.isIso_app_iff_of_iso α (eqToIso heq)] at h

end DerivedExtendScalars

section DerivedAdjunction

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

/-- **Derived extension-restriction adjunction.** Any left derived functor `(G, α)` of degreewise
scalar extension along `f : R →+* S` is left adjoint to
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
def derivedExtendRestrictScalarsAdj
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory := by
  let W_R := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let W_S := HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)
  let R' := (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
  let eR := (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
  have : R'.IsRightDerivedFunctor eR.inv W_S :=
    Functor.isRightDerivedFunctor_of_inverts W_S R' eR
  have : (R' ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight eR.inv G ≫ (Functor.associator _ _ _).hom) W_S :=
    Functor.isRightDerivedFunctor_of_inverts W_S (R' ⋙ G)
      ((Functor.associator DerivedCategory.Q R' G).symm ≪≫ Functor.isoWhiskerRight eR G)
  have : (G ⋙ R').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α R') W_R :=
    (localizerMorphism_derives_complexBaseChange f).isLeftDerivedFunctor_comp α R'
  exact ((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
    (ComplexShape.up ℤ)).derived W_R W_S α eR.inv

/-- On a complex model `K`, the unit of `derivedExtendRestrictScalarsAdj` intertwines `α.app K`
with the degreewise extension-restriction unit. -/
@[reassoc (attr := simp)]
theorem derivedExtendRestrictScalarsAdj_unit_app_Q_comp
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendRestrictScalarsAdj f G α).unit.app (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (α.app K) =
    DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
        ((complexBaseChange f).obj K) := by
  dsimp [derivedExtendRestrictScalarsAdj]
  simp

/-- On a complex model `M`, the counit of `derivedExtendRestrictScalarsAdj` intertwines
`mapDerivedCategoryFactors.inv` with the degreewise extension-restriction counit. -/
@[reassoc (attr := simp)]
theorem map_derivedExtendRestrictScalarsAdj_counit_app_Q
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    G.map ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app M) ≫
      (derivedExtendRestrictScalarsAdj f G α).counit.app (DerivedCategory.Q.obj M) =
    α.app (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
        (ComplexShape.up ℤ)).counit.app M) := by
  dsimp [derivedExtendRestrictScalarsAdj]
  simp

instance instIsLeftAdjointDerivedExtendScalars :
    (derivedExtendScalars.{u, w, w'} f).IsLeftAdjoint :=
  (derivedExtendRestrictScalarsAdj f (derivedExtendScalars f)
    (derivedExtendScalarsCounit f)).isLeftAdjoint

/-- **Derived extension of scalars is left adjoint to restriction of scalars.** Any left derived
functor `(G, α)` of degreewise scalar extension along `f : R →+* S` admits an adjunction with
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
theorem nonempty_derivedExtendRestrictScalarsAdj
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    Nonempty (G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory) :=
  ⟨derivedExtendRestrictScalarsAdj f G α⟩

end DerivedAdjunction

end TauCeti

/-! ### Further results -/

namespace TauCeti

section GeneralTarget

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {H : Type*} [Category* H]
  (F : CochainComplex (ModuleCat.{u} S) ℤ ⥤ H)
  (hF : (quasiIso (ModuleCat.{u} S) (.up ℤ)).IsInvertedBy F)

include hF in
/-- The K-flat left derivability structure on `R`-module complexes derives the postcomposition of
`TauCeti.complexBaseChange f` with any functor `F` that inverts quasi-isomorphisms of `S`-module
complexes. -/
theorem derives_extendScalars_of_inverts :
    (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).Derives
      (complexBaseChange f ⋙ F) := by
  rw [LocalizerMorphism.Derives, CochainComplex.KFlat.localizerMorphism_functor]
  intro P Q g hg
  have : QuasiIso g.hom := (CochainComplex.KFlat.quasiIso_iff g).1 hg
  simp only [Functor.comp_map, ObjectProperty.ι_map]
  exact hF _ ((mem_quasiIso_iff _).2 (quasiIso_complexBaseChange_map_of_isKFlat f g.hom))

include hF in
/-- Postcomposing `TauCeti.complexBaseChange f` with any functor `F` that inverts
quasi-isomorphisms of `S`-module complexes yields a functor admitting a left derived functor with
respect to quasi-isomorphisms of `R`-module complexes. -/
theorem hasLeftDerivedFunctor_extendScalars_of_inverts :
    (complexBaseChange f ⋙ F).HasLeftDerivedFunctor (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have := (derives_extendScalars_of_inverts f F hF).hasPointwiseLeftDerivedFunctor
  infer_instance

section Characterization

variable {D : Type*} [Category* D] {L : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D}
  [L.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))] {LF : D ⥤ H}
  (α : L ⋙ LF ⟶ complexBaseChange f ⋙ F)

include hF in
/-- When `F` inverts quasi-isomorphisms of `S`-module complexes, a pair `(LF, α)` is a left derived
functor of `TauCeti.complexBaseChange f ⋙ F` if and only if `α.app P` is an isomorphism for every
K-flat complex `P` of `R`-modules. -/
theorem isLeftDerivedFunctor_extendScalars_iff_isIso :
    LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ)) ↔
      ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat], IsIso (α.app P) := by
  rw [(derives_extendScalars_of_inverts f F hF).isLeftDerivedFunctor_iff_isIso,
    CochainComplex.KFlat.localizerMorphism_functor]
  exact ⟨fun h P hP ↦ h ⟨P, (CochainComplex.kFlat_iff P).2 hP⟩,
    fun h ⟨P, hP⟩ ↦ @h P ((CochainComplex.kFlat_iff P).1 hP)⟩

include hF in
/-- When `F` inverts quasi-isomorphisms of `S`-module complexes, any left derived functor `(LF, α)`
of `TauCeti.complexBaseChange f ⋙ F` is computed by termwise scalar extension on K-flat
complexes. -/
theorem isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat
    [LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] : IsIso (α.app P) :=
  (isLeftDerivedFunctor_extendScalars_iff_isIso f F hF α).1 inferInstance P

include hF in
/-- When `F` inverts quasi-isomorphisms of `S`-module complexes, any left derived functor `(LF, α)`
of `TauCeti.complexBaseChange f ⋙ F` is computed by termwise scalar extension on bounded-above
complexes of flat `R`-modules. -/
theorem isIso_app_of_isLeftDerivedFunctor_extendScalars_of_boundedAbove_flat
    [LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ n, Module.Flat R (P.X n)) : IsIso (α.app P) :=
  have := CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat P b hP
  isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat f F hF α P

include hF in
/-- **Left derived scalar extension is absolute.** When `F` inverts quasi-isomorphisms of `S`-module
complexes, postcomposing any left derived functor `(LF, α)` of `TauCeti.complexBaseChange f ⋙ F`
with an arbitrary functor `M : H ⥤ E` yields a left derived functor of
`TauCeti.complexBaseChange f ⋙ (F ⋙ M)`. -/
theorem isLeftDerivedFunctor_comp_of_isLeftDerivedFunctor_extendScalars
    {E : Type*} [Category* E] (M : H ⥤ E)
    [LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))] :
    (LF ⋙ M).IsLeftDerivedFunctor ((Functor.associator L LF M).inv ≫ Functor.whiskerRight α M)
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  (derives_extendScalars_of_inverts f F hF).isLeftDerivedFunctor_comp α M

end Characterization

end GeneralTarget

section Canonical

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

/-- The object isomorphism `(derivedExtendScalars f).obj (DerivedCategory.Q.obj P) ≅
DerivedCategory.Q.obj ((complexBaseChange f).obj P)` induced by `derivedExtendScalarsCounit f` at a
K-flat complex `P` of `R`-modules. -/
def derivedExtendScalarsKFlatIso (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedExtendScalars.{u, w, w'} f).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((complexBaseChange f).obj P) :=
  asIso ((derivedExtendScalarsCounit f).app P)

/-- The forward morphism of `derivedExtendScalarsKFlatIso` is the counit component. -/
@[simp]
lemma derivedExtendScalarsKFlatIso_hom (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedExtendScalarsKFlatIso.{u, w, w'} f P).hom = (derivedExtendScalarsCounit f).app P :=
  (rfl)

/-- The inverse morphism of `derivedExtendScalarsKFlatIso` is the categorical inverse of the counit
component. -/
@[simp]
lemma derivedExtendScalarsKFlatIso_inv (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedExtendScalarsKFlatIso.{u, w, w'} f P).inv =
      inv ((derivedExtendScalarsCounit f).app P) := (rfl)

/-- **Derived extension of scalars of a flat module.** For a flat `R`-module `M` placed in degree
zero, the derived extension of scalars `M ⊗^L_R S` is the ordinary extension of scalars
`S ⊗_R M` placed in degree zero, since `M` in degree zero is K-flat. -/
def derivedExtendScalarsSingleIso (M : ModuleCat.{u} R) [Module.Flat R M] :
    (derivedExtendScalars.{u, w, w'} f).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((ModuleCat.extendScalars f).obj M) :=
  (derivedExtendScalars f).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M) ≪≫
    derivedExtendScalarsKFlatIso f _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.extendScalars f) (.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- The canonical adjunction
`derivedExtendScalars f ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory` between derived
extension and derived restriction of scalars. -/
def derivedExtendScalarsAdj :
    derivedExtendScalars.{u, w, w'} f ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory :=
  derivedExtendRestrictScalarsAdj f (derivedExtendScalars f) (derivedExtendScalarsCounit f)

/-- The unit of `derivedExtendScalarsAdj` intertwines `derivedExtendScalarsCounit` with the
degreewise unit of `ModuleCat.extendRestrictScalarsAdj f`. -/
@[reassoc (attr := simp)]
lemma derivedExtendScalarsAdj_unit_app_comp (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendScalarsAdj.{u, w, w'} f).unit.app (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((derivedExtendScalarsCounit f).app K) =
      DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app K) ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
          ((complexBaseChange f).obj K) :=
  derivedExtendRestrictScalarsAdj_unit_app_Q_comp f (derivedExtendScalars f)
    (derivedExtendScalarsCounit f) K

/-- The counit of `derivedExtendScalarsAdj` intertwines `derivedExtendScalarsCounit` with the
degreewise counit of `ModuleCat.extendRestrictScalarsAdj f`. -/
@[reassoc (attr := simp)]
lemma map_comp_derivedExtendScalarsAdj_counit_app (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    (derivedExtendScalars.{u, w, w'} f).map
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app M) ≫
      (derivedExtendScalarsAdj f).counit.app (DerivedCategory.Q.obj M) =
      (derivedExtendScalarsCounit f).app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
          (ComplexShape.up ℤ)).counit.app M) :=
  map_derivedExtendRestrictScalarsAdj_counit_app_Q f (derivedExtendScalars f)
    (derivedExtendScalarsCounit f) M

end Canonical

end TauCeti
