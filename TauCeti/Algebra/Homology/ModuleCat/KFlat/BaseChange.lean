/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.Derives
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.Algebra.Homology.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Derived extension of scalars and its adjunction with restriction

Let `f : R →+* S` be a homomorphism of commutative rings in a common universe. Termwise extension of
scalars `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)` sends a cochain complex of
`R`-modules to a cochain complex of `S`-modules. After restricting scalars back to `R`, this functor
is naturally isomorphic to termwise left tensoring by `S` viewed as an `R`-module
(`ModuleCat.extendScalarsCompRestrictScalarsIso`). Since restriction of scalars is exact and
reflects isomorphisms, any quasi-isomorphism between K-flat complexes of `R`-modules remains a
quasi-isomorphism under `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)`
(`CochainComplex.quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat`).

Combining this invariance with `TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure` and
`TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic`, we obtain:
* `TauCeti.hasLeftDerivedFunctor_extendScalars`:
  `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q` admits a left
  derived functor `− ⊗^L_R S : D(R) ⥤ D(S)` with respect to quasi-isomorphisms;
* `TauCeti.isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat`,
  `TauCeti.isIso_app_of_isLeftDerivedFunctor_extendScalars_of_boundedAbove_flat`, and
  `TauCeti.isIso_app_single_obj_of_isLeftDerivedFunctor_extendScalars_of_flat`: any left derived
  functor of scalar extension is computed on the nose on K-flat complexes and, in particular, on
  bounded-above complexes of flat modules and single-degree flat modules;
* `TauCeti.isLeftDerivedFunctor_comp_of_isLeftDerivedFunctor_extendScalars`: any left derived
  functor of scalar extension is absolute, remaining left derived after postcomposition with any
  functor;
* `TauCeti.derivedExtendRestrictScalarsAdj`:
  every left derived functor of `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)` is left
  adjoint to derived restriction of scalars `(ModuleCat.restrictScalars f).mapDerivedCategory`,
  obtained by deriving the degreewise lift of `ModuleCat.extendRestrictScalarsAdj f`;
* `TauCeti.derivedExtendScalars f`: the canonical choice `totalLeftDerived` of `− ⊗^L_R S`, with its
  counit, K-flat object isomorphism, and canonical adjunction `TauCeti.derivedExtendScalarsAdj f`.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) and
  [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT).
* G. Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés, revisité*,
  C. R. Math. Acad. Sci. Paris 344 (2007), 549–552.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor HomologicalComplex

universe u w w'

namespace CochainComplex

/-- Termwise extension of scalars along `f : R →+* S` preserves quasi-isomorphisms between K-flat
complexes of `R`-modules. -/
instance quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKFlat] [Q.IsKFlat] (g : P ⟶ Q) [QuasiIso g] :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map g) := by
  rw [← quasiIso_map_iff_of_preservesHomology _ (ModuleCat.restrictScalars.{u} f)]
  let e := Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsCompRestrictScalarsIso f) (.up ℤ)
  exact quasiIso_of_arrow_mk_iso
    (((MonoidalCategory.tensorLeft
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))).mapHomologicalComplex (.up ℤ)).map g)
    (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).map
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map g))
    (Arrow.isoMk (e.app P).symm (e.app Q).symm (e.inv.naturality g).symm)

end CochainComplex

namespace TauCeti

section GeneralTarget

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {H : Type*} [Category* H]
  (F : CochainComplex (ModuleCat.{u} S) ℤ ⥤ H)
  (hF : (quasiIso (ModuleCat.{u} S) (.up ℤ)).IsInvertedBy F)

include hF in
/-- The K-flat left derivability structure on `R`-module complexes derives the postcomposition of
`(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)` with any functor `F` that inverts
quasi-isomorphisms of `S`-module complexes. -/
theorem derives_extendScalars_of_inverts :
    (CochainComplex.kFlatLocalizerMorphism (ModuleCat.{u} R)).Derives
      ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙ F) := by
  intro P Q g hg
  have : QuasiIso g.hom := (mem_quasiIso_iff _).1 hg
  dsimp
  rw [CochainComplex.kFlatLocalizerMorphism_functor]
  simp only [ObjectProperty.ι_map]
  exact hF _ ((mem_quasiIso_iff _).2
    (CochainComplex.quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat f g.hom))

include hF in
/-- Postcomposing `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)` with any functor `F`
that inverts quasi-isomorphisms of `S`-module complexes yields a functor admitting a left derived
functor with respect to quasi-isomorphisms of `R`-module complexes. -/
theorem hasLeftDerivedFunctor_extendScalars_of_inverts :
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙ F).HasLeftDerivedFunctor
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have := (derives_extendScalars_of_inverts f F hF).hasPointwiseLeftDerivedFunctor
  infer_instance

section Characterization

variable {D : Type*} [Category* D] {L : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D}
  [L.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))] {LF : D ⥤ H}
  (α : L ⋙ LF ⟶ (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙ F)

include hF in
/-- When `F` inverts quasi-isomorphisms of `S`-module complexes, a pair `(LF, α)` is a left derived
functor of `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ F` if and only if `α.app P`
is an isomorphism for every K-flat complex `P` of `R`-modules. -/
theorem isLeftDerivedFunctor_extendScalars_iff_isIso :
    LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ)) ↔
      ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat], IsIso (α.app P) := by
  rw [(derives_extendScalars_of_inverts f F hF).isLeftDerivedFunctor_iff_isIso]
  refine ⟨fun h P hP ↦ ?_, fun h ⟨P, hP⟩ ↦ ?_⟩
  · have h' := h ⟨P, hP⟩
    rwa [CochainComplex.kFlatLocalizerMorphism_functor] at h'
  · rw [CochainComplex.kFlatLocalizerMorphism_functor]
    exact @h P hP

include hF in
/-- When `F` inverts quasi-isomorphisms of `S`-module complexes, any left derived functor `(LF, α)`
of `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ F` is computed by termwise scalar
extension on K-flat complexes. -/
theorem isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat
    [LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] : IsIso (α.app P) :=
  (isLeftDerivedFunctor_extendScalars_iff_isIso f F hF α).1 inferInstance P

include hF in
/-- When `F` inverts quasi-isomorphisms of `S`-module complexes, any left derived functor `(LF, α)`
of `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ F` is computed by termwise scalar
extension on bounded-above complexes of flat `R`-modules. -/
theorem isIso_app_of_isLeftDerivedFunctor_extendScalars_of_boundedAbove_flat
    [LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ n, Module.Flat R (P.X n)) : IsIso (α.app P) :=
  have := CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat P b hP
  isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat f F hF α P

include hF in
/-- When `F` inverts quasi-isomorphisms of `S`-module complexes, any left derived functor `(LF, α)`
of `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ F` is computed by termwise scalar
extension on a flat `R`-module placed in a single cohomological degree `n`. -/
theorem isIso_app_single_obj_of_isLeftDerivedFunctor_extendScalars_of_flat
    [LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (M : ModuleCat.{u} R) [Module.Flat R M] (n : ℤ) :
    IsIso (α.app ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) n).obj M)) :=
  isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat f F hF α _

include hF in
/-- **Left derived scalar extension is absolute.** When `F` inverts quasi-isomorphisms of `S`-module
complexes, postcomposing any left derived functor `(LF, α)` of
`(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ F` with an arbitrary functor
`M : H ⥤ E` yields a left derived functor of
`(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ (F ⋙ M)`. -/
theorem isLeftDerivedFunctor_comp_of_isLeftDerivedFunctor_extendScalars
    {E : Type*} [Category* E] (M : H ⥤ E)
    [LF.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))] :
    (LF ⋙ M).IsLeftDerivedFunctor ((Functor.associator L LF M).inv ≫ whiskerRight α M)
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  (derives_extendScalars_of_inverts f F hF).isLeftDerivedFunctor_comp α M

end Characterization

end GeneralTarget

section DerivedCategory

/-- **Derived extension of scalars exists.** For a homomorphism `f : R →+* S` of commutative rings,
termwise scalar extension of complexes followed by localization to `DerivedCategory (ModuleCat S)`
admits a left derived functor `− ⊗^L_R S` with respect to quasi-isomorphisms of `R`-module
complexes. -/
theorem hasLeftDerivedFunctor_extendScalars {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q (C := ModuleCat.{u} S)).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_extendScalars_of_inverts f (DerivedCategory.Q (C := ModuleCat.{u} S))
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} S) (.up ℤ)))

attribute [instance] hasLeftDerivedFunctor_extendScalars

section Adjunction

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]
  (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
  (α : DerivedCategory.Q ⋙ G ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

private lemma isLeftDerivedFunctor_comp_mapDerivedCategory :
    (G ⋙ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight α (ModuleCat.restrictScalars.{u} f).mapDerivedCategory)
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  isLeftDerivedFunctor_comp_of_isLeftDerivedFunctor_extendScalars f DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} S) (.up ℤ))) α _

private lemma isRightDerivedFunctor_mapDerivedCategory_comp :
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙ G).IsRightDerivedFunctor
      (whiskerRight (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv G ≫
        (Functor.associator _ _ _).hom) (quasiIso (ModuleCat.{u} S) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts (quasiIso (ModuleCat.{u} S) (.up ℤ)) _
    (asIso (whiskerRight (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv G ≫
      (Functor.associator _ _ _).hom)).symm

/-- Every left derived functor `(G, α)` of
`(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q` is left adjoint to
derived restriction of scalars `(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
def derivedExtendRestrictScalarsAdj : G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory :=
  have := Functor.isRightDerivedFunctor_of_inverts (quasiIso (ModuleCat.{u} S) (.up ℤ))
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
  have := isLeftDerivedFunctor_comp_mapDerivedCategory f G α
  have := isRightDerivedFunctor_mapDerivedCategory_comp f G
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).derived
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} S) (.up ℤ)) α
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv

/-- The unit of `derivedExtendRestrictScalarsAdj` on a localized complex `Q.obj K` intertwines the
comparison `α` with the degreewise unit of `ModuleCat.extendRestrictScalarsAdj f`. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_unit_app_comp (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendRestrictScalarsAdj f G α).unit.app (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (α.app K) =
      DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (.up ℤ)).unit.app K) ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj K) := by
  have := isLeftDerivedFunctor_comp_mapDerivedCategory f G α
  dsimp [derivedExtendRestrictScalarsAdj]
  exact Adjunction.derivedη_fac_app
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ))
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) α
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv K

/-- The counit of `derivedExtendRestrictScalarsAdj` on a localized complex `Q.obj M` intertwines
the comparison `α` with the degreewise counit of `ModuleCat.extendRestrictScalarsAdj f`. -/
@[reassoc (attr := simp)]
lemma map_comp_derivedExtendRestrictScalarsAdj_counit_app (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    G.map ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app M) ≫
      (derivedExtendRestrictScalarsAdj f G α).counit.app (DerivedCategory.Q.obj M) =
      α.app (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (.up ℤ)).counit.app M) := by
  have := isRightDerivedFunctor_mapDerivedCategory_comp f G
  dsimp [derivedExtendRestrictScalarsAdj]
  exact Adjunction.derivedε_fac_app
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ))
    (quasiIso (ModuleCat.{u} S) (.up ℤ)) α
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv M

end Adjunction

section Canonical

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

/-- The canonical left derived scalar extension functor `− ⊗^L_R S : D(R) ⥤ D(S)` along
`f : R →+* S`. -/
def derivedExtendScalars : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q (C := ModuleCat.{u} S)).totalLeftDerived DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ))

/-- The universal counit comparing `derivedExtendScalars f` on localized complexes with termwise
scalar extension `(ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)`. -/
def derivedExtendScalarsCounit :
    DerivedCategory.Q ⋙ derivedExtendScalars f ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q (C := ModuleCat.{u} S)).totalLeftDerivedCounit DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ))

instance : (derivedExtendScalars f).IsLeftDerivedFunctor (derivedExtendScalarsCounit f)
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  dsimp [derivedExtendScalars, derivedExtendScalarsCounit]; infer_instance

instance (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso ((derivedExtendScalarsCounit f).app P) :=
  isIso_app_of_isLeftDerivedFunctor_extendScalars_of_isKFlat f DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} S) (.up ℤ)))
    (derivedExtendScalarsCounit f) P

/-- The object isomorphism `(derivedExtendScalars f).obj (DerivedCategory.Q.obj P) ≅
DerivedCategory.Q.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P)` induced
by `derivedExtendScalarsCounit f` at a K-flat complex `P` of `R`-modules. -/
def derivedExtendScalarsKFlatIso (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedExtendScalars f).obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj P) :=
  asIso ((derivedExtendScalarsCounit f).app P)

/-- The forward morphism of `derivedExtendScalarsKFlatIso` is the counit component. -/
@[simp]
lemma derivedExtendScalarsKFlatIso_hom (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedExtendScalarsKFlatIso f P).hom = (derivedExtendScalarsCounit f).app P := (rfl)

/-- The inverse morphism of `derivedExtendScalarsKFlatIso` is the categorical inverse of the counit
component. -/
@[simp]
lemma derivedExtendScalarsKFlatIso_inv (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedExtendScalarsKFlatIso f P).inv = inv ((derivedExtendScalarsCounit f).app P) := (rfl)

/-- The canonical adjunction
`derivedExtendScalars f ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory` between derived
extension and derived restriction of scalars. -/
def derivedExtendScalarsAdj :
    derivedExtendScalars f ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory :=
  derivedExtendRestrictScalarsAdj f (derivedExtendScalars f) (derivedExtendScalarsCounit f)

/-- The unit of `derivedExtendScalarsAdj` intertwines `derivedExtendScalarsCounit` with the
degreewise unit of `ModuleCat.extendRestrictScalarsAdj f`. -/
@[reassoc (attr := simp)]
lemma derivedExtendScalarsAdj_unit_app_comp (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendScalarsAdj f).unit.app (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((derivedExtendScalarsCounit f).app K) =
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (.up ℤ)).unit.app K) ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj K) :=
  derivedExtendRestrictScalarsAdj_unit_app_comp f (derivedExtendScalars f)
    (derivedExtendScalarsCounit f) K

/-- The counit of `derivedExtendScalarsAdj` intertwines `derivedExtendScalarsCounit` with the
degreewise counit of `ModuleCat.extendRestrictScalarsAdj f`. -/
@[reassoc (attr := simp)]
lemma map_comp_derivedExtendScalarsAdj_counit_app (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    (derivedExtendScalars f).map
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app M) ≫
      (derivedExtendScalarsAdj f).counit.app (DerivedCategory.Q.obj M) =
      (derivedExtendScalarsCounit f).app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (.up ℤ)).counit.app M) :=
  map_comp_derivedExtendRestrictScalarsAdj_counit_app f (derivedExtendScalars f)
    (derivedExtendScalarsCounit f) M

end Canonical

end DerivedCategory

end TauCeti
