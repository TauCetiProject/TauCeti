/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.RingTheory.Flat.CategoryTheory
import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport
import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor
import TauCeti.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
# Derived extension of scalars and the extension–restriction adjunction

For a homomorphism `f : R →+* S` of commutative rings, degreewise extension of scalars
`(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)` on unbounded cochain complexes of
`R`-modules need not preserve quasi-isomorphisms when `S` is not flat over `R`. After composing
with degreewise restriction of scalars along `f`, however, it becomes naturally isomorphic to
totalized tensoring on the left with the single-degree complex `S[0]` viewed as an `R`-module
(`ModuleCat.extendScalarsMapCochainComplexCompRestrictScalarsIso`). Because restriction of scalars
is exact and conservative on `ModuleCat` and tensoring with any complex preserves
quasi-isomorphisms between K-flat complexes (`CochainComplex.quasiIso_id_tensorHom_of_isKFlat`),
degreewise scalar extension preserves quasi-isomorphisms between unbounded K-flat complexes
(`CochainComplex.quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat`).

Combining this with the K-flat left derivability structure on `CochainComplex (ModuleCat.{u} R) ℤ`
yields:

* Existence of the left derived scalar extension functor `- ⊗^L_R S`
  (`TauCeti.ModuleCat.hasLeftDerivedFunctor_extendScalars`), together with the canonical choice
  `TauCeti.ModuleCat.derivedExtendScalars f` and its counit
  `TauCeti.ModuleCat.derivedExtendScalarsCounit f`.
* Universal K-flat and bounded-above flat model comparisons: for any left derived functor `(G, α)`
  of scalar extension along `f`, `α.app K` is an isomorphism whenever `K` is K-flat (in particular
  whenever `K` is bounded above with flat terms,
  `TauCeti.ModuleCat.isIso_app_of_isLeftDerivedFunctor_extendScalars_of_boundedAbove_flat`).
* The derived extension–restriction adjunction
  `TauCeti.ModuleCat.derivedExtendRestrictScalarsAdj α`
  (`G ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory`)
  for every left derived functor `(G, α)` of scalar extension along `f`, obtained from
  `CategoryTheory.Adjunction.derived` via absoluteness of K-flat left derived functors
  (`CategoryTheory.LocalizerMorphism.Derives.isLeftDerivedFunctor_comp`) and of exact right derived
  functors.

## References

* The Stacks Project, More on Algebra, Section 15.61, Tags 06Y6 and 0GMT.
* [Georges Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés,
  revisité*][Maltsiniotis2007]
* [Joël Riou, *Formalization of derived categories in {Lean}/mathlib*][riou-2025]
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

universe u w w'

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Degreewise extension followed by degreewise restriction of scalars along `f : R →+* S` on
unbounded cochain complexes is naturally isomorphic to totalized tensoring on the left with `S[0]`
viewed as a complex of `R`-modules. -/
def extendScalarsMapCochainComplexCompRestrictScalarsIso :
    (extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
      (restrictScalars.{u} f).mapHomologicalComplex (.up ℤ) ≅
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft (.up ℤ) (.up ℤ)
      ((single (ModuleCat.{u} R) (.up ℤ) 0).obj
        ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))) :=
  Functor.mapHomologicalComplexCompIso (extendScalarsCompRestrictScalarsIso f) (.up ℤ) ≪≫
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorSingleRowZeroNatIso
      ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).symm

/-- In degree `j`, the forward morphism of `extendScalarsMapCochainComplexCompRestrictScalarsIso`
identifies `(restrictScalars f).obj ((extendScalars f).obj (K.X j))` with `S ⊗[R] K.X j` and
includes it as the `(0, j)` totalization summand. -/
@[reassoc, simp]
theorem extendScalarsMapCochainComplexCompRestrictScalarsIso_hom_app_f
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ((extendScalarsMapCochainComplexCompRestrictScalarsIso f).hom.app K).f j =
      (extendScalarsCompRestrictScalarsIso f).hom.app (K.X j) ≫
        ((singleObjXSelf (.up ℤ) 0 ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).inv ▷
          K.X j) ≫
        ιTensorObj
          ((single (ModuleCat.{u} R) (.up ℤ) 0).obj
            ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))))
          K 0 j j (zero_add j) := by
  simp [extendScalarsMapCochainComplexCompRestrictScalarsIso]

/-- Precomposing the degree-`j` inverse of `extendScalarsMapCochainComplexCompRestrictScalarsIso`
with the `(0, j)` totalization summand inclusion gives the inverse of
`extendScalarsCompRestrictScalarsIso` on `K.X j`. -/
@[reassoc (attr := simp)]
theorem ι_extendScalarsMapCochainComplexCompRestrictScalarsIso_inv_app_f
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ιTensorObj
        ((single (ModuleCat.{u} R) (.up ℤ) 0).obj
          ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))))
        K 0 j j (zero_add j) ≫
      ((extendScalarsMapCochainComplexCompRestrictScalarsIso f).inv.app K).f j =
      ((singleObjXSelf (.up ℤ) 0 ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).hom ▷
        K.X j) ≫
      (extendScalarsCompRestrictScalarsIso f).inv.app (K.X j) := by
  simp [extendScalarsMapCochainComplexCompRestrictScalarsIso]

end ModuleCat

namespace CochainComplex

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Degreewise extension of scalars along any commutative ring homomorphism `f : R →+* S` preserves
quasi-isomorphisms between unbounded K-flat cochain complexes of `R`-modules. -/
instance quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map φ) := by
  let S₀ : CochainComplex (ModuleCat.{u} R) ℤ :=
    (single (ModuleCat.{u} R) (.up ℤ) 0).obj
      ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))
  let e := ModuleCat.extendScalarsMapCochainComplexCompRestrictScalarsIso f
  have hq : QuasiIso (HomologicalComplex.tensorHom (𝟙 S₀) φ) := inferInstance
  have hres : QuasiIso (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).map
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map φ)) :=
    quasiIso_of_arrow_mk_iso (HomologicalComplex.tensorHom (𝟙 S₀) φ) _
      (Arrow.isoMk (e.symm.app K) (e.symm.app L) (e.symm.hom.naturality φ).symm)
  exact (quasiIso_map_iff_of_preservesHomology
    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map φ)
    (ModuleCat.restrictScalars.{u} f)).1 hres

end CochainComplex

namespace TauCeti.ModuleCat

open CochainComplex

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

section DerivedExtendScalars

variable [HasDerivedCategory.{w} (_root_.ModuleCat.{u} S)]

/-- Degreewise extension of scalars along `f : R →+* S` followed by localization to
`DerivedCategory (ModuleCat.{u} S)`. -/
abbrev extendScalarsCompQ :
    CochainComplex (_root_.ModuleCat.{u} R) ℤ ⥤ DerivedCategory (_root_.ModuleCat.{u} S) :=
  (_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q (C := _root_.ModuleCat.{u} S)

/-- The K-flat localizer morphism derives degreewise extension of scalars along `f`. -/
theorem derives_extendScalarsCompQ :
    (kFlatLocalizerMorphism (_root_.ModuleCat.{u} R)).Derives (extendScalarsCompQ f) := by
  intro K L φ hφ
  have : QuasiIso φ.hom := by simpa [mem_quasiIso_iff] using hφ
  dsimp [extendScalarsCompQ, kFlatLocalizerMorphism]
  infer_instance

/-- **Existence of derived extension of scalars.** For any homomorphism `f : R →+* S` of
commutative rings, degreewise extension of scalars on `CochainComplex (ModuleCat.{u} R) ℤ` followed
by localization to `DerivedCategory (ModuleCat.{u} S)` admits a left derived functor with respect
to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_extendScalars :
    ((_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := _root_.ModuleCat.{u} S)).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := (derives_extendScalarsCompQ f).hasPointwiseLeftDerivedFunctor
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

section ModelComparison

variable {f}
variable [HasDerivedCategory.{w'} (_root_.ModuleCat.{u} R)]
  {G : DerivedCategory (_root_.ModuleCat.{u} R) ⥤ DerivedCategory (_root_.ModuleCat.{u} S)}
  (α : DerivedCategory.Q ⋙ G ⟶
    (_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α
    (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ))]

/-- On any K-flat complex `K`, the counit `α.app K` of any left derived scalar extension functor
along `f` is an isomorphism in `DerivedCategory (ModuleCat.{u} S)`. -/
instance isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat
    (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso (α.app K) :=
  (derives_extendScalarsCompQ f).isIso' α ⟨K, ‹_›⟩

/-- On any bounded-above complex `K` of flat `R`-modules, the counit `α.app K` of any left derived
scalar extension functor along `f` is an isomorphism. -/
theorem isIso_app_of_isLeftDerivedFunctor_extendScalars_of_boundedAbove_flat
    (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] :
    IsIso (α.app K) :=
  have := K.isKFlat_of_boundedAbove_flat b
  inferInstance

end ModelComparison

end DerivedExtendScalars

section CanonicalAndAdjunction

variable [HasDerivedCategory.{w} (_root_.ModuleCat.{u} R)]
  [HasDerivedCategory.{w'} (_root_.ModuleCat.{u} S)]

/-- The canonical left derived scalar extension functor `- ⊗^L_R S` from
`DerivedCategory (ModuleCat.{u} R)` to `DerivedCategory (ModuleCat.{u} S)`. -/
def derivedExtendScalars :
    DerivedCategory (_root_.ModuleCat.{u} R) ⥤ DerivedCategory (_root_.ModuleCat.{u} S) :=
  ((_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q (C := _root_.ModuleCat.{u} S)).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- The canonical counit exhibiting `TauCeti.ModuleCat.derivedExtendScalars f` as a left derived
functor of degreewise extension of scalars. -/
def derivedExtendScalarsCounit :
    DerivedCategory.Q ⋙ derivedExtendScalars f ⟶
      (_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  ((_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q (C := _root_.ModuleCat.{u} S)).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ))

instance isLeftDerivedFunctor_derivedExtendScalars :
    (derivedExtendScalars f).IsLeftDerivedFunctor (derivedExtendScalarsCounit f)
      (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  dsimp [derivedExtendScalars, derivedExtendScalarsCounit]
  infer_instance

section Adjunction

variable {f}
variable {G : DerivedCategory (_root_.ModuleCat.{u} R) ⥤ DerivedCategory (_root_.ModuleCat.{u} S)}
  (α : DerivedCategory.Q ⋙ G ⟶
    (_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α
    (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ))]

/-- **Derived scalar extension–restriction adjunction.** Any left derived functor `(G, α)` of
degreewise scalar extension along `f : R →+* S` is left adjoint to derived restriction of scalars
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
def derivedExtendRestrictScalarsAdj :
    G ⊣ (_root_.ModuleCat.restrictScalars.{u} f).mapDerivedCategory := by
  let W₁ := HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ)
  let W₂ := HomologicalComplex.quasiIso (_root_.ModuleCat.{u} S) (ComplexShape.up ℤ)
  let F' := (_root_.ModuleCat.restrictScalars.{u} f).mapDerivedCategory
  let eF := (_root_.ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
  have : F'.IsRightDerivedFunctor eF.inv W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ F' eF
  have : (G ⋙ F').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α F') W₁ :=
    (derives_extendScalarsCompQ f).isLeftDerivedFunctor_comp F' α
  have : (F' ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight eF.inv G ≫ (Functor.associator _ _ _).hom) W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ (F' ⋙ G)
      (asIso (Functor.whiskerRight eF.inv G ≫ (Functor.associator _ _ _).hom)).symm
  exact ((_root_.ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
    (.up ℤ)).derived W₁ W₂ α eF.inv

/-- Characterization of the unit of `derivedExtendRestrictScalarsAdj` on a complex model `Q.obj K`
in terms of the complex-level extension–restriction unit. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_unit_fac_app
    (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) :
    (derivedExtendRestrictScalarsAdj α).unit.app (DerivedCategory.Q.obj K) ≫
      (_root_.ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (α.app K) =
    DerivedCategory.Q.map
      (((_root_.ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (.up ℤ)).unit.app K) ≫
      (_root_.ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
        (((_root_.ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj K) := by
  simp [derivedExtendRestrictScalarsAdj]

/-- Characterization of the counit of `derivedExtendRestrictScalarsAdj` on a complex model `Q.obj M`
in terms of the complex-level extension–restriction counit. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_counit_fac_app
    (M : CochainComplex (_root_.ModuleCat.{u} S) ℤ) :
    G.map ((_root_.ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app M) ≫
      (derivedExtendRestrictScalarsAdj α).counit.app (DerivedCategory.Q.obj M) =
    α.app (((_root_.ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj M) ≫
      DerivedCategory.Q.map
        (((_root_.ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (.up ℤ)).counit.app M) := by
  simp [derivedExtendRestrictScalarsAdj]

end Adjunction

end CanonicalAndAdjunction

end TauCeti.ModuleCat
