/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivedTensor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport
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
  (`CochainComplex.hasLeftDerivedFunctor_extendScalars`), together with the canonical choice
  `DerivedCategory.derivedExtendScalars f` and its counit
  `DerivedCategory.derivedExtendScalarsCounit f`.
* Universal K-flat and bounded-above flat model comparisons: for any left derived functor `(G, α)`
  of scalar extension along `f`, `α.app K` is an isomorphism whenever `K` is K-flat (in particular
  whenever `K` is bounded above with flat terms).
* The derived extension–restriction adjunction `DerivedCategory.derivedExtendRestrictScalarsAdj α`
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

/-- Degreewise extension followed by degreewise restriction of scalars along `f : R →+* S` on
unbounded cochain complexes is naturally isomorphic to totalized tensoring on the left with `S[0]`
viewed as a complex of `R`-modules. -/
def extendScalarsMapCochainComplexCompRestrictScalarsIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    (extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
      (restrictScalars.{u} f).mapHomologicalComplex (.up ℤ) ≅
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft (.up ℤ) (.up ℤ)
      ((single (ModuleCat.{u} R) (.up ℤ) 0).obj
        ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))) :=
  Functor.mapHomologicalComplexCompIso (extendScalarsCompRestrictScalarsIso f) (.up ℤ) ≪≫
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorSingleRowZeroNatIso
      ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).symm

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

section DerivedExtendScalars

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- Degreewise extension of scalars along `f : R →+* S` followed by localization to
`DerivedCategory (ModuleCat.{u} S)`. -/
abbrev extendScalarsCompQ :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} S) :=
  (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q (C := ModuleCat.{u} S)

/-- The K-flat localizer morphism derives degreewise extension of scalars along `f`. -/
theorem derives_extendScalarsCompQ :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).Derives (extendScalarsCompQ f) := by
  intro K L φ hφ
  have : QuasiIso φ.hom := by simpa [mem_quasiIso_iff] using hφ
  dsimp [extendScalarsCompQ, kFlatLocalizerMorphism]
  infer_instance

/-- **Existence of derived extension of scalars.** For any homomorphism `f : R →+* S` of
commutative rings, degreewise extension of scalars on `CochainComplex (ModuleCat.{u} R) ℤ` followed
by localization to `DerivedCategory (ModuleCat.{u} S)` admits a left derived functor with respect
to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_extendScalars :
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := ModuleCat.{u} S)).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := (derives_extendScalarsCompQ f).hasPointwiseLeftDerivedFunctor
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

section ModelComparison

variable {f}
variable [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
  {G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S)}
  (α : DerivedCategory.Q ⋙ G ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

/-- On any K-flat complex `K`, the counit `α.app K` of any left derived scalar extension functor
along `f` is an isomorphism in `DerivedCategory (ModuleCat.{u} S)`. -/
instance isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso (α.app K) :=
  (derives_extendScalarsCompQ f).isIso' α ⟨K, ‹_›⟩

/-- On any bounded-above complex `K` of flat `R`-modules, the counit `α.app K` of any left derived
scalar extension functor along `f` is an isomorphism. -/
theorem isIso_app_of_isLeftDerivedFunctor_extendScalars_of_boundedAbove_flat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] :
    IsIso (α.app K) :=
  have := K.isKFlat_of_moduleCat_boundedAbove_flat b
  inferInstance

end ModelComparison

end DerivedExtendScalars

end CochainComplex

namespace DerivedCategory

open CochainComplex

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

/-- The canonical left derived scalar extension functor `- ⊗^L_R S` from
`DerivedCategory (ModuleCat.{u} R)` to `DerivedCategory (ModuleCat.{u} S)`. -/
def derivedExtendScalars :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q (C := ModuleCat.{u} S)).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- The canonical counit exhibiting `DerivedCategory.derivedExtendScalars f` as a left derived
functor of degreewise extension of scalars. -/
def derivedExtendScalarsCounit :
    DerivedCategory.Q ⋙ derivedExtendScalars f ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q (C := ModuleCat.{u} S)).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

instance isLeftDerivedFunctor_derivedExtendScalars :
    (derivedExtendScalars f).IsLeftDerivedFunctor (derivedExtendScalarsCounit f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  dsimp [derivedExtendScalars, derivedExtendScalarsCounit]
  infer_instance

section Adjunction

variable {f}
variable {G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S)}
  (α : DerivedCategory.Q ⋙ G ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

/-- **Derived scalar extension–restriction adjunction.** Any left derived functor `(G, α)` of
degreewise scalar extension along `f : R →+* S` is left adjoint to derived restriction of scalars
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
def derivedExtendRestrictScalarsAdj :
    G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory := by
  let W₁ := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let W₂ := HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)
  let F' := (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
  let eF := (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
  have : F'.IsRightDerivedFunctor eF.inv W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ F' eF
  have : (G ⋙ F').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α F') W₁ :=
    (derives_extendScalarsCompQ f).isLeftDerivedFunctor_comp F' α
  have : (F' ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight eF.inv G ≫ (Functor.associator _ _ _).hom) W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ (F' ⋙ G)
      (asIso (Functor.whiskerRight eF.inv G ≫ (Functor.associator _ _ _).hom)).symm
  exact ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).derived
    W₁ W₂ α eF.inv

/-- Characterization of the unit of `derivedExtendRestrictScalarsAdj` on a complex model `Q.obj K`
in terms of the complex-level extension–restriction unit. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_unit_app_Q (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendRestrictScalarsAdj α).unit.app (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (α.app K) =
    DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).unit.app
        K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj K) := by
  simp [derivedExtendRestrictScalarsAdj]

/-- Characterization of the counit of `derivedExtendRestrictScalarsAdj` on a complex model `Q.obj M`
in terms of the complex-level extension–restriction counit. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_counit_app_Q (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    G.map ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app M) ≫
      (derivedExtendRestrictScalarsAdj α).counit.app (DerivedCategory.Q.obj M) =
    α.app (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj M) ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (.up ℤ)).counit.app M) := by
  simp [derivedExtendRestrictScalarsAdj]

end Adjunction

/-- Propositional existence of the derived extension–restriction adjunction for any left derived
functor `(G, α)` of degreewise scalar extension along `f : R →+* S`. -/
theorem nonempty_derivedExtendRestrictScalarsAdj
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    Nonempty (G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory) :=
  ⟨derivedExtendRestrictScalarsAdj α⟩

end DerivedCategory
