/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Tensor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The derived tensor product of unbounded complexes of modules

Over a commutative ring `R`, the free-forgetful comonad `forget ⋙ ModuleCat.free R` with its
counit supplies a functorial flat cover of every `R`-module. Together with exactness of countable
coproducts and sequential colimits in `ModuleCat R`, this makes the inclusion of K-flat complexes
into `CochainComplex (ModuleCat R) ℤ` a left derivability structure
(`CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat`).

Taking the product left derivability structure with itself shows that the termwise total tensor
product of cochain complexes of `R`-modules admits a left derived bifunctor on the unbounded
derived category `DerivedCategory (ModuleCat R)` (`CochainComplex.hasLeftDerivedFunctor₂_tensor`).
For any left derived tensor bifunctor `LF` with comparison `α`, the comparison map
`LF (Q P) (Q L) ⟶ Q (P ⊗ L)` is an isomorphism whenever either `P` or `L` is K-flat
(`CochainComplex.isIso_derivedTensorCounit_of_isKFlat_left` and
`CochainComplex.isIso_derivedTensorCounit_of_isKFlat_right`), and in particular whenever either
factor is a bounded-above complex of flat `R`-modules. For a K-flat complex `P`, the partial
functor `LF (Q P)` is naturally isomorphic to `CochainComplex.kFlatTensor P`.

## Main results

* `CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat`: K-flat complexes
  form a left derivability structure on `CochainComplex (ModuleCat R) ℤ`.
* `CochainComplex.hasLeftDerivedFunctor₂_tensor`: the total tensor product of complexes of
  `R`-modules followed by `DerivedCategory.Q` admits a left derived bifunctor.
* `CochainComplex.isIso_derivedTensorCounit_of_isKFlat_left`,
  `CochainComplex.isIso_derivedTensorCounit_of_isKFlat_right`: any left derived tensor bifunctor
  is computed by the ordinary total tensor product when either factor is K-flat.
* `CochainComplex.isIso_derivedTensorCounit_of_boundedAbove_flat_left`,
  `CochainComplex.isIso_derivedTensorCounit_of_boundedAbove_flat_right`: specialization to
  bounded-above complexes of flat modules.
* `CochainComplex.derivedTensorObjIsoKFlatTensor`: natural identification of `LF.obj (Q.obj P)`
  with `P.kFlatTensor` for K-flat `P`.

## References

* The Stacks Project, More on Algebra, Section 15.60, Definition 15.60.13 (Tag 064M), with
  Lemmas 15.60.2, 15.60.10, and 15.60.12 (Tags 06Y0, 06Y4, and 064L).
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace CochainComplex

universe u w

variable (R : Type u) [CommRing R]

/-- **The K-flat left derivability structure for modules.** Over any commutative ring `R`, the
inclusion of K-flat cochain complexes into `CochainComplex (ModuleCat R) ℤ` is a left
derivability structure for quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  let E : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
    CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R
  let p : E ⟶ 𝟭 (ModuleCat.{u} R) := (ModuleCat.adj R).counit
  have (X : ModuleCat.{u} R) : Epi (p.app X) := by
    rw [ModuleCat.epi_iff_surjective]
    intro x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    have h : ((ModuleCat.adj R).homEquiv ((CategoryTheory.forget (ModuleCat.{u} R)).obj X) X)
        ((ModuleCat.adj R).counit.app X) = 𝟙 _ := by
      rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
    simpa [p, ModuleCat.adj_homEquiv, ModuleCat.freeHomEquiv] using congrArg (fun f ↦ f x) h
  have (X : ModuleCat.{u} R) :
      PreservesFiniteLimits (MonoidalCategory.tensorLeft (E.obj X)) :=
    inferInstanceAs (PreservesFiniteLimits
      (MonoidalCategory.tensorLeft (ModuleCat.of R (X →₀ R))))
  have (X : ModuleCat.{u} R) :
      PreservesFiniteColimits (MonoidalCategory.tensorLeft (E.obj X)) :=
    inferInstanceAs (PreservesFiniteColimits
      (MonoidalCategory.tensorLeft (ModuleCat.of R (X →₀ R))))
  exact isLeftDerivabilityStructure_kFlatLocalizerMorphism E p

section DerivedTensor

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The product K-flat left derivability structure derives the uncurried total tensor product of
cochain complexes of `R`-modules. -/
theorem kFlatLocalizerMorphism_prod_derives_tensor :
    ((kFlatLocalizerMorphism (ModuleCat.{u} R)).prod
      (kFlatLocalizerMorphism (ModuleCat.{u} R))).Derives
      (Functor.uncurry.obj
        (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have : QuasiIso f.hom := hf
  have : QuasiIso g.hom := hg
  have : QuasiIso (f.hom ▷ K₂.obj) := by
    rw [HomologicalComplex.whiskerRight_eq_mapBifunctorMap]
    infer_instance
  have : QuasiIso (L₁.obj ◁ g.hom) := by
    rw [HomologicalComplex.whiskerLeft_eq_mapBifunctorMap]
    infer_instance
  dsimp only [Functor.comp_obj, Functor.comp_map, LocalizerMorphism.prod_functor,
    Functor.prod_obj, Functor.prod_map, Functor.uncurry_obj_map,
    Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app,
    kFlatLocalizerMorphism_functor, ObjectProperty.ι_obj, ObjectProperty.ι_map]
  infer_instance

/-- **The derived tensor product exists.** For any commutative ring `R`, the total tensor product
of cochain complexes of `R`-modules followed by `DerivedCategory.Q` admits a left derived
bifunctor with respect to quasi-isomorphisms in both variables. -/
instance hasLeftDerivedFunctor₂_tensor :
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := ModuleCat.{u} R))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have := (kFlatLocalizerMorphism_prod_derives_tensor R).hasPointwiseLeftDerivedFunctor
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

variable {R}
variable (LF : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
  (α : (((Functor.whiskeringLeft₂ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R))).obj
      (DerivedCategory.Q (C := ModuleCat.{u} R))).obj LF ⟶
    MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
  [LF.IsLeftDerivedFunctor₂ α
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]

private lemma isIso_derivedTensorCounit_of_isKFlat
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] [Q.IsKFlat] :
    IsIso ((α.app P).app Q) :=
  (kFlatLocalizerMorphism_prod_derives_tensor R).isIso'
    (Functor.whiskeringLeft₂HomEquiv α) (⟨P, ‹P.IsKFlat›⟩, ⟨Q, ‹Q.IsKFlat›⟩)

/-- **K-flat left model computation.** If `P` is K-flat and `L` is an arbitrary (possibly
unbounded) complex of `R`-modules, the derived tensor comparison `LF (Q P) (Q L) ⟶ Q (P ⊗ L)`
is an isomorphism. -/
theorem isIso_derivedTensorCounit_of_isKFlat_left
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso ((α.app P).app L) := by
  obtain ⟨K, p, hp, hK⟩ := L.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso p := hp
  have : K.IsKFlat := hK
  have hnat :
      (LF.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map p) ≫ (α.app P).app L =
        (α.app P).app K ≫ DerivedCategory.Q.map (P ◁ p) :=
    (α.app P).naturality p
  have : IsIso ((α.app P).app K) := isIso_derivedTensorCounit_of_isKFlat LF α P K
  have : QuasiIso (P ◁ p) := by
    rw [HomologicalComplex.whiskerLeft_eq_mapBifunctorMap]
    infer_instance
  have : IsIso ((LF.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map p) ≫
      (α.app P).app L) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((LF.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map p)) ((α.app P).app L)

/-- **K-flat right model computation.** If `P` is K-flat and `K` is an arbitrary (possibly
unbounded) complex of `R`-modules, the derived tensor comparison `LF (Q K) (Q P) ⟶ Q (K ⊗ P)`
is an isomorphism. -/
theorem isIso_derivedTensorCounit_of_isKFlat_right
    (K P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso ((α.app K).app P) := by
  obtain ⟨Q, p, hp, hQ⟩ := K.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso p := hp
  have : Q.IsKFlat := hQ
  have hnat :
      (LF.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj P) ≫ (α.app K).app P =
        (α.app Q).app P ≫ DerivedCategory.Q.map (p ▷ P) :=
    congrArg (fun τ ↦ τ.app P) (α.naturality p)
  have : IsIso ((α.app Q).app P) := isIso_derivedTensorCounit_of_isKFlat LF α Q P
  have : QuasiIso (p ▷ P) := by
    rw [HomologicalComplex.whiskerRight_eq_mapBifunctorMap]
    infer_instance
  have : IsIso ((LF.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj P)) :=
    NatIso.isIso_app_of_isIso (LF.map (DerivedCategory.Q.map p)) _
  have : IsIso ((LF.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj P) ≫
      (α.app K).app P) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((LF.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj P)) ((α.app K).app P)

/-- **Bounded-above flat left model computation.** If `P` is a bounded-above complex of flat
`R`-modules and `L` is any complex of `R`-modules, the derived tensor comparison
`LF (Q P) (Q L) ⟶ Q (P ⊗ L)` is an isomorphism. -/
theorem isIso_derivedTensorCounit_of_boundedAbove_flat_left
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    [∀ i, Module.Flat R (P.X i)] :
    IsIso ((α.app P).app L) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have : P.IsKFlat := isKFlat_of_boundedAbove_flat P b
  exact isIso_derivedTensorCounit_of_isKFlat_left LF α P L

/-- **Bounded-above flat right model computation.** If `P` is a bounded-above complex of flat
`R`-modules and `K` is any complex of `R`-modules, the derived tensor comparison
`LF (Q K) (Q P) ⟶ Q (K ⊗ P)` is an isomorphism. -/
theorem isIso_derivedTensorCounit_of_boundedAbove_flat_right
    (K P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    [∀ i, Module.Flat R (P.X i)] :
    IsIso ((α.app K).app P) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have : P.IsKFlat := isKFlat_of_boundedAbove_flat P b
  exact isIso_derivedTensorCounit_of_isKFlat_right LF α K P

/-- For a K-flat complex `P`, the partial derived tensor functor `LF.obj (Q.obj P)` is naturally
isomorphic to `CochainComplex.kFlatTensor P`. -/
def derivedTensorObjIsoKFlatTensor
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    LF.obj (DerivedCategory.Q.obj P) ≅ P.kFlatTensor := by
  have (L : CochainComplex (ModuleCat.{u} R) ℤ) : IsIso ((α.app P).app L) :=
    isIso_derivedTensorCounit_of_isKFlat_left LF α P L
  have : IsIso (α.app P) := NatIso.isIso_of_isIso_app (α.app P)
  let hfac : DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P) ⋙
        DerivedCategory.Q :=
    asIso (α.app P) ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
        simp [HomologicalComplex.whiskerLeft_eq_mapBifunctorMap])
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P) ⋙
        DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) := ⟨hfac⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P) ⋙
      DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P) ⋙
      DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor (Iso.refl _)

/-- On a complex model `L`, the identification `derivedTensorObjIsoKFlatTensor` intertwines the
derived tensor counit with `kFlatTensorModelIso`. -/
@[reassoc (attr := simp)]
lemma derivedTensorObjIsoKFlatTensor_hom_app_Q_comp
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedTensorObjIsoKFlatTensor LF α P).hom.app (DerivedCategory.Q.obj L) ≫
        P.kFlatTensorModelIso.hom.app L =
      (α.app P).app L := by
  dsimp only [derivedTensorObjIsoKFlatTensor]
  rw [kFlatTensorModelIso_eq_liftingIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, asIso_hom, Iso.refl_hom, NatTrans.id_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact Category.comp_id ((α.app P).app L)

end DerivedTensor

end CochainComplex
