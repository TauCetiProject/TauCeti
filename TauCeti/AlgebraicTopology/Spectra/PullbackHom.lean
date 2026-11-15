/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.TrivialFibration
public import TauCeti.AlgebraicTopology.Spectra.Cotensor
public import TauCeti.AlgebraicTopology.Spectra.LevelFactorization
public import TauCeti.AlgebraicTopology.Spectra.Limits
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Pushout-products and pullback-hom corners of symmetric spectra

Smashing a symmetric spectrum levelwise with a pointed simplicial set, taking the point-set
cotensor `E^K`, and forming the pointed mapping space `Map(X, E)` assemble into an adjunction of
two variables (`SymmetricSpectrum.levelSmashCotensorAdjunction₂` and
`SymmetricSpectrum.levelSmashMappingSpaceAdjunction₂`), together with an unpointed simplicial
counterpart obtained through `PointedSSet.addBasepoint` and `PointedSSet.forgetBasepoint`.

Combining these parametrized adjunctions
(`Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction`) with the level projective weak
factorization systems on `SymmetricSpectrum`
(`TauCeti.AlgebraicTopology.Spectra.LevelFactorization`) and the based pullback-hom corner theorems
on `PointedSSet` (`TauCeti.AlgebraicTopology.SimplicialSet.Pointed.TrivialFibration`) yields the
three families of corner lifting properties for symmetric spectra (both in pointed form and in
unpointed simplicial form):

1. **Cotensor corners.** For a based map `k : K ⟶ L` and a map of symmetric spectra `p : E ⟶ F`,
   every pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` is a level fibration when `k` is a
   monomorphism and `p` is a level fibration, and is a level trivial fibration when either `k` is
   anodyne and `p` is a level fibration, or `k` is a monomorphism and `p` is a level trivial
   fibration.
2. **Pushout-products.** For a map of symmetric spectra `i : A ⟶ B` and a based map `k : K ⟶ L`,
   every pushout-product corner `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` is a projective cofibration
   when `i` is a projective cofibration and `k` is a monomorphism, and lifts against all level
   fibrations when either `i` is a projective cofibration and `k` is anodyne, or `i` lifts against
   all level fibrations and `k` is a monomorphism.
3. **Mapping-space corners.** For maps of symmetric spectra `i : A ⟶ B` and `p : E ⟶ F`, every
   pullback-hom corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` is a Kan fibration on
   underlying simplicial sets when `i` is a projective cofibration and `p` is a level fibration,
   and lifts against all simplicial monomorphisms when either `i` lifts against all level
   fibrations and `p` is a level fibration, or `i` is a projective cofibration and `p` is a level
   trivial fibration.

Specializing to an initial source or a terminal target gives the single-variable preservation
properties of `cotensor`, `levelSmash`, `levelSmashRight`, and `mappingSpace`, including Kan
fibrancy of `Map(X, E)` when `X` is projective cofibrant and every level of `E` is a Kan complex.
These statements hold for the level projective weak factorization systems without assuming the full
Kan–Quillen model structure on simplicial sets.

## Main definitions

* `SymmetricSpectrum.curriedLevelSmash`, `SymmetricSpectrum.cotensorBifunctor`, and
  `SymmetricSpectrum.mappingSpaceBifunctor`: the pointed tensor, cotensor, and mapping-space
  bifunctors, with parametrized adjunctions `SymmetricSpectrum.levelSmashCotensorAdjunction₂` and
  `SymmetricSpectrum.levelSmashMappingSpaceAdjunction₂`.
* `SymmetricSpectrum.simplicialTensor`, `SymmetricSpectrum.simplicialCotensor`, and
  `SymmetricSpectrum.simplicialMappingSpace`: the unpointed simplicial tensor, cotensor, and
  mapping-space bifunctors, with parametrized adjunctions
  `SymmetricSpectrum.simplicialTensorCotensorAdjunction₂` and
  `SymmetricSpectrum.simplicialTensorMappingSpaceAdjunction₂`.

## Main statements

* `SymmetricSpectrum.levelFibrations_cotensor_pullbackObjObjπ`,
  `SymmetricSpectrum.levelTrivialFibrations_cotensor_pullbackObjObjπ`,
  `SymmetricSpectrum.levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations`,
  and their unpointed `simplicialCotensor` counterparts: lifting for cotensor pullback-hom corners.
* `SymmetricSpectrum.projectiveCofibrations_levelSmash_pushoutObjObjι`,
  `SymmetricSpectrum.llp_levelFibrations_levelSmash_pushoutObjObjι_of_anodyne`,
  `SymmetricSpectrum.llp_levelFibrations_levelSmash_pushoutObjObjι`, and their unpointed
  `simplicialTensor` counterparts: lifting for levelwise-smash pushout-products.
* `SymmetricSpectrum.fibration_mappingSpace_pullbackObjObjπ`,
  `SymmetricSpectrum.rlp_monomorphisms_mappingSpace_pullbackObjObjπ`,
  `SymmetricSpectrum.rlp_monomorphisms_mappingSpace_pullbackObjObjπ_of_levelTrivialFibrations`,
  and their unpointed `simplicialMappingSpace` counterparts: lifting for spectral mapping-space
  pullback-hom corners.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 3.1 and 5.1.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter II, Section 3.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits MorphismProperty HomotopicalAlgebra
  Opposite
open SSet.modelCategoryQuillen
open scoped Simplicial DayFunctor

namespace TauCeti.SymmetricSpectrum

open PointedSSet

/-! ### Two-variable adjunctions of tensors, cotensors, and mapping spaces -/

/-- Levelwise smash `(X, K) ↦ X ∧ K` as a curried bifunctor. Its evaluation at `X` is
`levelSmash X`, and its flipped evaluation at `K` is `levelSmashRight K`. -/
-- An abbreviation so that `PushoutObjObj` squares have carriers `(levelSmash X).obj K` without
-- equality transports.
noncomputable abbrev curriedLevelSmash :
    SymmetricSpectrum ⥤ PointedSSet.{0} ⥤ SymmetricSpectrum where
  obj X := levelSmash X
  map {X Y} f :=
    { app K := (levelSmashRight K).map f
      naturality _ _ g := by
        apply Mod.Hom.ext
        simp only [Mod.comp_hom', Mod.Hom.mk'_hom]
        exact MonoidalCategory.whisker_exchange f.hom ((SymmetricSequence.free 0).map g) }
  map_id X := by
    apply NatTrans.ext
    funext K
    exact (levelSmashRight K).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext K
    exact (levelSmashRight K).map_comp f g

/-- Evaluating `curriedLevelSmash` at a spectrum `X` gives `levelSmash X`. -/
@[simp]
lemma curriedLevelSmash_obj (X : SymmetricSpectrum) :
    curriedLevelSmash.obj X = levelSmash X := (rfl)

/-- On a spectrum map `f`, `curriedLevelSmash` acts at `K` by `(levelSmashRight K).map f`. -/
@[simp]
lemma curriedLevelSmash_map_app {X Y : SymmetricSpectrum} (f : X ⟶ Y) (K : PointedSSet.{0}) :
    (curriedLevelSmash.map f).app K = (levelSmashRight K).map f := (rfl)

/-- Evaluating `curriedLevelSmash.flip` at a pointed simplicial set `K` gives
`levelSmashRight K`. -/
@[simp]
lemma curriedLevelSmash_flip_obj (K : PointedSSet.{0}) :
    curriedLevelSmash.flip.obj K = levelSmashRight K := (rfl)

/-- On a based map `k`, `curriedLevelSmash.flip` acts at `X` by `(levelSmash X).map k`. -/
@[simp]
lemma curriedLevelSmash_flip_map_app {K L : PointedSSet.{0}} (k : K ⟶ L) (X : SymmetricSpectrum) :
    (curriedLevelSmash.flip.map k).app X = (levelSmash X).map k := (rfl)

/-- Point-set cotensors `(op K, E) ↦ E^K` as a curried bifunctor. -/
-- Exposed so `PullbackObjObj` squares reduce through `.obj` and `.map`.
@[expose]
noncomputable def cotensorBifunctor :
    PointedSSet.{0}ᵒᵖ ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum :=
  (free 0).op ⋙ MonoidalClosed.internalHom

/-- Evaluating `cotensorBifunctor` at `op K` gives `cotensor K`. -/
@[simp]
lemma cotensorBifunctor_obj (K : PointedSSet.{0}) :
    cotensorBifunctor.obj (op K) = cotensor K := (rfl)

/-- On `k.op`, `cotensorBifunctor` acts at `E` by precomposition along `(free 0).map k`. -/
@[simp]
lemma cotensorBifunctor_map_app {K L : PointedSSet.{0}} (k : K ⟶ L) (E : SymmetricSpectrum) :
    (cotensorBifunctor.map k.op).app E = (MonoidalClosed.pre ((free 0).map k)).app E := (rfl)

/-- Pointed spectral mapping spaces `(op X, E) ↦ Map(X, E)` as a curried bifunctor: level zero of
the internal function spectrum `Hom_S(X, E)`. -/
-- Exposed so `PullbackObjObj` squares reduce through `.obj` and `.map`.
@[expose]
noncomputable def mappingSpaceBifunctor :
    SymmetricSpectrumᵒᵖ ⥤ SymmetricSpectrum ⥤ PointedSSet.{0} :=
  MonoidalClosed.internalHom ⋙
    (Functor.whiskeringRight SymmetricSpectrum SymmetricSpectrum PointedSSet.{0}).obj
      (Mod.forget SymmetricSequence.sphere ⋙
        (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
          (CategoryTheory.evaluation FiniteBijection PointedSSet.{0}).obj (FiniteBijection.mk 0))

/-- Evaluating `mappingSpaceBifunctor` at `op X` gives `mappingSpace X`. -/
@[simp]
lemma mappingSpaceBifunctor_obj (X : SymmetricSpectrum) :
    mappingSpaceBifunctor.obj (op X) = mappingSpace X := (rfl)

/-- On `i.op`, `mappingSpaceBifunctor` acts at `E` by level zero of internal precomposition along
`i`. -/
@[simp]
lemma mappingSpaceBifunctor_map_app {A B : SymmetricSpectrum} (i : A ⟶ B) (E : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map i.op).app E =
      (((MonoidalClosed.pre i).app E).hom).natTrans.app (FiniteBijection.mk 0) := (rfl)

/-- Levelwise smash with a fixed spectrum preserves colimits of every size. -/
instance levelSmash_preservesColimitsOfSize.{v, w} (X : SymmetricSpectrum) :
    PreservesColimitsOfSize.{v, w} (levelSmash X) :=
  (levelSmashMappingSpaceAdjunction X).leftAdjoint_preservesColimits

/-- Levelwise smash with a fixed pointed simplicial set preserves colimits of every size. -/
instance levelSmashRight_preservesColimitsOfSize.{v, w} (K : PointedSSet.{0}) :
    PreservesColimitsOfSize.{v, w} (levelSmashRight K) :=
  (levelSmashCotensorAdjunction K).leftAdjoint_preservesColimits

/-- The cotensor by a pointed simplicial set preserves limits of every size. -/
instance cotensor_preservesLimitsOfSize.{v, w} (K : PointedSSet.{0}) :
    PreservesLimitsOfSize.{v, w} (cotensor K) :=
  (levelSmashCotensorAdjunction K).rightAdjoint_preservesLimits

/-- The pointed mapping space out of a spectrum preserves limits of every size. -/
instance mappingSpace_preservesLimitsOfSize.{v, w} (X : SymmetricSpectrum) :
    PreservesLimitsOfSize.{v, w} (mappingSpace X) :=
  (levelSmashMappingSpaceAdjunction X).rightAdjoint_preservesLimits

/-- Evaluating `curriedLevelSmash` at `X` preserves colimits of every size. -/
instance curriedLevelSmash_obj_preservesColimitsOfSize.{v, w} (X : SymmetricSpectrum) :
    PreservesColimitsOfSize.{v, w} (curriedLevelSmash.obj X) :=
  levelSmash_preservesColimitsOfSize X

/-- Evaluating `curriedLevelSmash.flip` at `K` preserves colimits of every size. -/
instance curriedLevelSmash_flip_obj_preservesColimitsOfSize.{v, w} (K : PointedSSet.{0}) :
    PreservesColimitsOfSize.{v, w} (curriedLevelSmash.flip.obj K) :=
  levelSmashRight_preservesColimitsOfSize K

/-- Evaluating `cotensorBifunctor` at `K` preserves limits of every size. -/
instance cotensorBifunctor_obj_preservesLimitsOfSize.{v, w} (K : PointedSSet.{0}ᵒᵖ) :
    PreservesLimitsOfSize.{v, w} (cotensorBifunctor.obj K) :=
  cotensor_preservesLimitsOfSize K.unop

/-- Evaluating `mappingSpaceBifunctor` at `X` preserves limits of every size. -/
instance mappingSpaceBifunctor_obj_preservesLimitsOfSize.{v, w} (X : SymmetricSpectrumᵒᵖ) :
    PreservesLimitsOfSize.{v, w} (mappingSpaceBifunctor.obj X) :=
  mappingSpace_preservesLimitsOfSize X.unop

/-- The parametrized adjunction between levelwise smash and point-set cotensors, with parameter in
`PointedSSet.{0}`. -/
noncomputable def levelSmashCotensorAdjunction₂ :
    curriedLevelSmash.flip ⊣₂ cotensorBifunctor :=
  ParametrizedAdjunction.mk' levelSmashCotensorAdjunction fun {K L} k {E F} g ↦ by
    let p : (CategoryTheory.ihom ((free 0).obj L)).obj F ⟶
        (CategoryTheory.ihom ((free 0).obj K)).obj F :=
      (MonoidalClosed.pre ((free 0).map k)).app F
    have hnat : E ◁ ((free 0).map k) ≫
          (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj L) =
        (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj K) ≫
          (levelSmash E).map k :=
      (Mod.tensorFreeIso E).hom.naturality ((SymmetricSequence.free 0).map k)
    have hcur : MonoidalClosed.curry
          ((β_ ((free 0).obj K) E).hom ≫
            (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj K) ≫
            (levelSmash E).map k ≫ g) =
        MonoidalClosed.curry
          ((β_ ((free 0).obj L) E).hom ≫
            (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj L) ≫ g) ≫ p := by
      rw [MonoidalClosed.curry_pre_app]
      congr 1
      calc (β_ ((free 0).obj K) E).hom ≫
            (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj K) ≫
            (levelSmash E).map k ≫ g
        _ = (β_ ((free 0).obj K) E).hom ≫
              ((Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj K) ≫
                (levelSmash E).map k) ≫ g := by simp only [Category.assoc]
        _ = (β_ ((free 0).obj K) E).hom ≫
              (E ◁ ((free 0).map k) ≫
                (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj L)) ≫ g :=
            congrArg ((β_ ((free 0).obj K) E).hom ≫ · ≫ g) hnat.symm
        _ = (free 0).map k ▷ E ≫ (β_ ((free 0).obj L) E).hom ≫
              (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj L) ≫ g := by
            simp only [Category.assoc, BraidedCategory.braiding_naturality_left_assoc]
    exact (levelSmashCotensorAdjunction_homEquiv_apply K ((levelSmash E).map k ≫ g)).trans
      ((Mod.curry_eq_tensorHomEquiv _ _ _ _).symm.trans
        (hcur.trans ((congrArg (· ≫ p) (Mod.curry_eq_tensorHomEquiv _ _ _ _)).trans
          (congrArg (· ≫ p) (levelSmashCotensorAdjunction_homEquiv_apply L g).symm))))

/-- The parametrized adjunction between levelwise smash and pointed spectral mapping spaces, with
parameter in `SymmetricSpectrum`. -/
noncomputable def levelSmashMappingSpaceAdjunction₂ :
    curriedLevelSmash ⊣₂ mappingSpaceBifunctor :=
  ParametrizedAdjunction.mk' levelSmashMappingSpaceAdjunction fun {A B} i {K E} g ↦ by
    -- Bind `p` at `Mod.internalHom` so `p.hom` has domain `(Mod.ihom B).obj E`.
    let p : (Mod.internalHom B).obj E ⟶ (Mod.internalHom A).obj E :=
      (MonoidalClosed.pre i).app E
    have hp : p.hom ≫ Mod.ihomι A E = Mod.ihomι B E ≫ (MonoidalClosed.pre i.hom).app E.X :=
      Mod.pre_app_hom_comp_ihomι i E
    have hseq : Mod.ihomHomEquiv A ((SymmetricSequence.free 0).obj K) E
          ((levelSmashRight K).map i ≫ g) =
        Mod.ihomHomEquiv B ((SymmetricSequence.free 0).obj K) E g ≫ p.hom := by
      apply Mod.ihom_hom_ext
      rw [Mod.ihomHomEquiv_apply_comp_ihomι, Category.assoc, hp,
        Mod.ihomHomEquiv_apply_comp_ihomι_assoc, MonoidalClosed.curry_pre_app]
      simp only [Mod.comp_hom', Mod.Hom.mk'_hom]
    refine (levelSmashMappingSpaceAdjunction_homEquiv_apply A
      ((levelSmashRight K).map i ≫ g)).trans ?_
    refine Eq.trans ?_
      (congrArg (· ≫ p.hom.natTrans.app (FiniteBijection.mk 0))
        (levelSmashMappingSpaceAdjunction_homEquiv_apply B g)).symm
    rw [hseq, DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc]

/-- For a fixed target spectrum `E`, the cotensor `K ↦ E^K` sends colimits of pointed simplicial
sets to limits of symmetric spectra. -/
instance cotensorBifunctor_flip_preservesLimitsOfShape {J : Type*} [Category* J]
    (E : SymmetricSpectrum) : PreservesLimitsOfShape J (cotensorBifunctor.flip.obj E) :=
  have (X : SymmetricSpectrum) : PreservesColimitsOfShape Jᵒᵖ (curriedLevelSmash.flip.flip.obj X) :=
    inferInstanceAs (PreservesColimitsOfShape Jᵒᵖ (levelSmash X))
  levelSmashCotensorAdjunction₂.preservesLimitsOfShape_flip_obj J E

/-- For a fixed target spectrum `E`, the pointed mapping space `X ↦ Map(X, E)` sends colimits of
symmetric spectra to limits of pointed simplicial sets. -/
instance mappingSpaceBifunctor_flip_preservesLimitsOfShape {J : Type*} [Category* J]
    (E : SymmetricSpectrum) : PreservesLimitsOfShape J (mappingSpaceBifunctor.flip.obj E) :=
  levelSmashMappingSpaceAdjunction₂.preservesLimitsOfShape_flip_obj J E

/-- Tensoring a symmetric spectrum with an unpointed simplicial set: `(X, K) ↦ X ∧ K₊`. -/
-- Exposed so `PushoutObjObj` squares reduce through `.obj` and `.map`.
@[expose]
noncomputable def simplicialTensor :
    SymmetricSpectrum ⥤ SSet.{0} ⥤ SymmetricSpectrum :=
  curriedLevelSmash ⋙
    (Functor.whiskeringLeft SSet.{0} PointedSSet.{0} SymmetricSpectrum).obj addBasepoint

/-- Cotensoring a symmetric spectrum by an unpointed simplicial set: `(op K, E) ↦ E^(K₊)`. -/
-- Exposed so `PullbackObjObj` squares reduce through `.obj` and `.map`.
@[expose]
noncomputable def simplicialCotensor :
    SSet.{0}ᵒᵖ ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum :=
  addBasepoint.op ⋙ cotensorBifunctor

/-- Unpointed simplicial mapping spaces `(op X, E) ↦ (Map(X, E)).right` of symmetric spectra. -/
-- Exposed so `PullbackObjObj` squares reduce through `.obj` and `.map`.
@[expose]
noncomputable def simplicialMappingSpace :
    SymmetricSpectrumᵒᵖ ⥤ SymmetricSpectrum ⥤ SSet.{0} :=
  mappingSpaceBifunctor ⋙
    (Functor.whiskeringRight SymmetricSpectrum PointedSSet.{0} SSet.{0}).obj forgetBasepoint

/-- Evaluating `simplicialTensor` on objects gives `(levelSmash X).obj (K₊)`. -/
@[simp]
lemma simplicialTensor_obj_obj (X : SymmetricSpectrum) (K : SSet.{0}) :
    (simplicialTensor.obj X).obj K = (levelSmash X).obj (addBasepoint.obj K) := (rfl)

/-- Evaluating `simplicialCotensor` at `op K` gives `cotensor (K₊)`. -/
@[simp]
lemma simplicialCotensor_obj (K : SSet.{0}) :
    simplicialCotensor.obj (op K) = cotensor (addBasepoint.obj K) := (rfl)

/-- Evaluating `simplicialMappingSpace` at `op X` gives `mappingSpace X ⋙ forgetBasepoint`. -/
@[simp]
lemma simplicialMappingSpace_obj (X : SymmetricSpectrum) :
    simplicialMappingSpace.obj (op X) = mappingSpace X ⋙ forgetBasepoint := (rfl)

/-- The parametrized adjunction between unpointed simplicial tensors and cotensors of symmetric
spectra. -/
noncomputable def simplicialTensorCotensorAdjunction₂ :
    simplicialTensor.flip ⊣₂ simplicialCotensor :=
  ParametrizedAdjunction.mk' (fun K ↦ levelSmashCotensorAdjunction (addBasepoint.obj K))
    fun {_ _} j {_ _} g ↦
      levelSmashCotensorAdjunction₂.homEquiv_naturality_one (addBasepoint.map j) g

/-- The parametrized adjunction between unpointed simplicial tensors and unpointed spectral mapping
spaces. -/
noncomputable def simplicialTensorMappingSpaceAdjunction₂ :
    simplicialTensor ⊣₂ simplicialMappingSpace :=
  ParametrizedAdjunction.mk'
    (fun X ↦ addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X))
    fun {A B} i {K E} g ↦ by
      have hA : (addBasepointForgetAdjunction.comp
            (levelSmashMappingSpaceAdjunction A)).homEquiv K E
            ((simplicialTensor.map i).app K ≫ g) =
          addBasepointHomEquiv K _
            ((levelSmashMappingSpaceAdjunction A).homEquiv (addBasepoint.obj K) E
              ((levelSmashRight (addBasepoint.obj K)).map i ≫ g)) := by
        refine (congrFun (congrArg DFunLike.coe (congrFun (congrFun
          (addBasepointForgetAdjunction.comp_homEquiv
            (levelSmashMappingSpaceAdjunction A)) K) E)) _).trans ?_
        exact congrFun (congrArg DFunLike.coe
          (addBasepointForgetAdjunction_homEquiv K ((mappingSpace A).obj E))) _
      have hB : (addBasepointForgetAdjunction.comp
            (levelSmashMappingSpaceAdjunction B)).homEquiv K E g =
          addBasepointHomEquiv K _
            ((levelSmashMappingSpaceAdjunction B).homEquiv (addBasepoint.obj K) E g) := by
        refine (congrFun (congrArg DFunLike.coe (congrFun (congrFun
          (addBasepointForgetAdjunction.comp_homEquiv
            (levelSmashMappingSpaceAdjunction B)) K) E)) g).trans ?_
        exact congrFun (congrArg DFunLike.coe
          (addBasepointForgetAdjunction_homEquiv K ((mappingSpace B).obj E))) _
      exact hA.trans ((congrArg (addBasepointHomEquiv K _)
        (levelSmashMappingSpaceAdjunction₂.homEquiv_naturality_one i g)).trans
        ((addBasepointHomEquiv_comp _ _).trans
          (congrArg (· ≫ ((mappingSpaceBifunctor.map i.op).app E).right) hB.symm)))

/-- Evaluating `simplicialTensor` at `X` preserves colimits of every size. -/
instance simplicialTensor_obj_preservesColimitsOfSize.{v, w} (X : SymmetricSpectrum) :
    PreservesColimitsOfSize.{v, w} (simplicialTensor.obj X) :=
  (simplicialTensorMappingSpaceAdjunction₂.adj X).leftAdjoint_preservesColimits

/-- Evaluating `simplicialTensor.flip` at `K` preserves colimits of every size. -/
instance simplicialTensor_flip_obj_preservesColimitsOfSize.{v, w} (K : SSet.{0}) :
    PreservesColimitsOfSize.{v, w} (simplicialTensor.flip.obj K) :=
  (simplicialTensorCotensorAdjunction₂.adj K).leftAdjoint_preservesColimits

/-- Evaluating `simplicialCotensor` at `K` preserves limits of every size. -/
instance simplicialCotensor_obj_preservesLimitsOfSize.{v, w} (K : SSet.{0}ᵒᵖ) :
    PreservesLimitsOfSize.{v, w} (simplicialCotensor.obj K) :=
  (simplicialTensorCotensorAdjunction₂.adj K.unop).rightAdjoint_preservesLimits

/-- Evaluating `simplicialMappingSpace` at `X` preserves limits of every size. -/
instance simplicialMappingSpace_obj_preservesLimitsOfSize.{v, w} (X : SymmetricSpectrumᵒᵖ) :
    PreservesLimitsOfSize.{v, w} (simplicialMappingSpace.obj X) :=
  (simplicialTensorMappingSpaceAdjunction₂.adj X.unop).rightAdjoint_preservesLimits

/-! ### Level fibrancy and cotensor pullback-hom corners -/

/-- Level `n` of `cotensorBifunctor` is naturally isomorphic to the pointed internal hom applied to
level `n`. -/
noncomputable def cotensorEvaluationNatIso (n : ℕ) :
    cotensorBifunctor ⋙
        (Functor.whiskeringRight SymmetricSpectrum SymmetricSpectrum PointedSSet.{0}).obj
          (evaluation n) ≅
      MonoidalClosed.internalHom ⋙
        (Functor.whiskeringLeft SymmetricSpectrum PointedSSet.{0} PointedSSet.{0}).obj
          (evaluation n) :=
  NatIso.ofComponents
    (fun K ↦ NatIso.ofComponents (fun E ↦ cotensorLevelIso K.unop E n)
      (fun f ↦ cotensorLevelIso_hom_naturality K.unop f n))
    (fun {K L} k ↦ by
      ext E : 2
      exact cotensorLevelIso_hom_naturality_left k.unop E n)

/-- On objects, `cotensorEvaluationNatIso n` is `cotensorLevelIso`. -/
@[simp]
lemma cotensorEvaluationNatIso_hom_app_app (n : ℕ) (K : PointedSSet.{0}) (E : SymmetricSpectrum) :
    ((cotensorEvaluationNatIso n).hom.app (op K)).app E = (cotensorLevelIso K E n).hom := (rfl)

/-- On objects, the inverse of `cotensorEvaluationNatIso n` is `(cotensorLevelIso K E n).inv`. -/
@[simp]
lemma cotensorEvaluationNatIso_inv_app_app (n : ℕ) (K : PointedSSet.{0}) (E : SymmetricSpectrum) :
    ((cotensorEvaluationNatIso n).inv.app (op K)).app E = (cotensorLevelIso K E n).inv := (rfl)

/-- The canonical map `E ⟶ ⊤_ SymmetricSpectrum` is a level fibration if and only if the
underlying simplicial set of every level of `E` is a Kan complex. -/
lemma levelFibrations_terminal_from_iff (E : SymmetricSpectrum) :
    levelFibrations (terminal.from E) ↔ ∀ n, SSet.KanComplex ((evaluation n).obj E).right := by
  rw [levelFibrations_iff]
  refine forall_congr' fun n ↦ ?_
  have hT := terminalIsTerminal.isTerminalObj (evaluation n ⋙ forgetBasepoint)
    (⊤_ SymmetricSpectrum)
  have hmap : ((evaluation n).map (terminal.from E)).right =
      hT.from ((evaluation n).obj E).right :=
    hT.hom_ext _ _
  rw [hmap]
  exact (isFibrant_iff_of_isTerminal _ hT).symm

/-- A map of symmetric spectra is a projective cofibration if and only if it has the left lifting
property against all level trivial fibrations. -/
lemma mem_projectiveCofibrations_iff {A B : SymmetricSpectrum} (i : A ⟶ B) :
    projectiveCofibrations i ↔ levelTrivialFibrations.llp i := by
  rw [← llp_eq_of_wfs (W₁ := projectiveCofibrations) (W₂ := levelTrivialFibrations)]

section CotensorCorners

variable {K L : PointedSSet.{0}} {U V : SSet.{0}} {E F : SymmetricSpectrum}

/-- The cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of a based monomorphism and a level
fibration is a level fibration. -/
theorem levelFibrations_cotensor_pullbackObjObjπ (k : K ⟶ L) (p : E ⟶ F)
    [Mono k.right] (hp : levelFibrations p) (P : cotensorBifunctor.PullbackObjObj k p) :
    levelFibrations P.π := by
  rw [levelFibrations_iff]
  intro n
  have := (levelFibrations_iff p).1 hp n
  let Q := ((P.map (evaluation n)).ofNatIso (cotensorEvaluationNatIso n)).ofWhiskeringLeft
  have hQ : Fibration Q.π.right := PointedSSet.fibration_pullbackObjObjπ k ((evaluation n).map p) Q
  let e := ((cotensorEvaluationNatIso n).app (op L)).app E
  have heq : ((evaluation n).map P.π).right = e.hom.right ≫ Q.π.right :=
    congrArg Under.Hom.right
      (Functor.PullbackObjObj.hom_comp_ofNatIso_π (P.map (evaluation n))
        (cotensorEvaluationNatIso n)).symm
  have : IsIso e.hom.right := ⟨⟨e.inv.right,
    by rw [← Under.comp_right, e.hom_inv_id, Under.id_right],
    by rw [← Under.comp_right, e.inv_hom_id, Under.id_right]⟩⟩
  rw [HomotopicalAlgebra.fibration_iff, heq]
  exact ((fibrations SSet.{0}).cancel_left_of_respectsIso _ _).2 hQ.mem

/-- The cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of an anodyne based map and a level
fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_cotensor_pullbackObjObjπ (k : K ⟶ L) (p : E ⟶ F)
    (hk : SSet.anodyneExtensions k.right) (hp : levelFibrations p)
    (P : cotensorBifunctor.PullbackObjObj k p) :
    levelTrivialFibrations P.π := by
  rw [levelTrivialFibrations_iff]
  intro n
  have := (levelFibrations_iff p).1 hp n
  let Q := ((P.map (evaluation n)).ofNatIso (cotensorEvaluationNatIso n)).ofWhiskeringLeft
  have hQ := PointedSSet.rlp_monomorphisms_pullbackObjObjπ k ((evaluation n).map p) hk Q
  let e := ((cotensorEvaluationNatIso n).app (op L)).app E
  have heq : ((evaluation n).map P.π).right = e.hom.right ≫ Q.π.right :=
    congrArg Under.Hom.right
      (Functor.PullbackObjObj.hom_comp_ofNatIso_π (P.map (evaluation n))
        (cotensorEvaluationNatIso n)).symm
  have : IsIso e.hom.right := ⟨⟨e.inv.right,
    by rw [← Under.comp_right, e.hom_inv_id, Under.id_right],
    by rw [← Under.comp_right, e.inv_hom_id, Under.id_right]⟩⟩
  rw [heq]
  exact ((monomorphisms SSet.{0}).rlp.cancel_left_of_respectsIso _ _).2 hQ

/-- The cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of a based monomorphism and a level
trivial fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations
    (k : K ⟶ L) (p : E ⟶ F) [Mono k.right] (hp : levelTrivialFibrations p)
    (P : cotensorBifunctor.PullbackObjObj k p) :
    levelTrivialFibrations P.π := by
  rw [levelTrivialFibrations_iff]
  intro n
  let Q := ((P.map (evaluation n)).ofNatIso (cotensorEvaluationNatIso n)).ofWhiskeringLeft
  have hQ := PointedSSet.rlp_monomorphisms_pullbackObjObjπ_of_rlp k ((evaluation n).map p)
    ((levelTrivialFibrations_iff p).1 hp n) Q
  let e := ((cotensorEvaluationNatIso n).app (op L)).app E
  have heq : ((evaluation n).map P.π).right = e.hom.right ≫ Q.π.right :=
    congrArg Under.Hom.right
      (Functor.PullbackObjObj.hom_comp_ofNatIso_π (P.map (evaluation n))
        (cotensorEvaluationNatIso n)).symm
  have : IsIso e.hom.right := ⟨⟨e.inv.right,
    by rw [← Under.comp_right, e.hom_inv_id, Under.id_right],
    by rw [← Under.comp_right, e.inv_hom_id, Under.id_right]⟩⟩
  rw [heq]
  exact ((monomorphisms SSet.{0}).rlp.cancel_left_of_respectsIso _ _).2 hQ

/-- The unpointed simplicial cotensor pullback-hom corner `E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of a
simplicial monomorphism and a level fibration is a level fibration. -/
theorem levelFibrations_simplicialCotensor_pullbackObjObjπ (j : U ⟶ V) (p : E ⟶ F)
    [Mono j] (hp : levelFibrations p) (P : simplicialCotensor.PullbackObjObj j p) :
    levelFibrations P.π :=
  levelFibrations_cotensor_pullbackObjObjπ (addBasepoint.map j) p hp P.ofOpComp

/-- The unpointed simplicial cotensor pullback-hom corner `E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of an
anodyne extension and a level fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ (j : U ⟶ V) (p : E ⟶ F)
    (hj : SSet.anodyneExtensions j) (hp : levelFibrations p)
    (P : simplicialCotensor.PullbackObjObj j p) :
    levelTrivialFibrations P.π :=
  levelTrivialFibrations_cotensor_pullbackObjObjπ (addBasepoint.map j) p
    (addBasepoint_map_right_mem_of_isStableUnderCobaseChange SSet.anodyneExtensions hj) hp
    P.ofOpComp

/-- The unpointed simplicial cotensor pullback-hom corner `E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of a
simplicial monomorphism and a level trivial fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_levelTrivialFibrations
    (j : U ⟶ V) (p : E ⟶ F) [Mono j] (hp : levelTrivialFibrations p)
    (P : simplicialCotensor.PullbackObjObj j p) :
    levelTrivialFibrations P.π :=
  levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations (addBasepoint.map j) p
    hp P.ofOpComp

/-- Point-set cotensors preserve level fibrations in the spectrum variable, with no hypothesis on
the pointed simplicial set `K`. -/
theorem levelFibrations_cotensor_map (K : PointedSSet.{0}) {p : E ⟶ F} (hp : levelFibrations p) :
    levelFibrations ((cotensor K).map p) := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact levelFibrations_cotensor_pullbackObjObjπ i p hp
    (Functor.PullbackObjObj.ofIsInitial cotensorBifunctor i p Under.mkIdInitial)

/-- Point-set cotensors preserve level trivial fibrations in the spectrum variable, with no
hypothesis on the pointed simplicial set `K`. -/
theorem levelTrivialFibrations_cotensor_map (K : PointedSSet.{0}) {p : E ⟶ F}
    (hp : levelTrivialFibrations p) :
    levelTrivialFibrations ((cotensor K).map p) := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations i p hp
    (Functor.PullbackObjObj.ofIsInitial cotensorBifunctor i p Under.mkIdInitial)

/-- If every level of `E` is a Kan complex, then every level of the cotensor `E^K` is a Kan
complex. -/
theorem kanComplex_cotensor (K : PointedSSet.{0}) (E : SymmetricSpectrum)
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) (n : ℕ) :
    SSet.KanComplex ((evaluation n).obj ((cotensor K).obj E)).right := by
  have hcot := levelFibrations_cotensor_map K ((levelFibrations_terminal_from_iff E).2 hE)
  have hT := terminalIsTerminal.isTerminalObj (cotensor K) (⊤_ SymmetricSpectrum)
  -- Transport along the unique isomorphism `(cotensor K).obj ⊤_ ≅ ⊤_`.
  have hterm : levelFibrations (terminal.from ((cotensor K).obj E)) := by
    have he : (cotensor K).map (terminal.from E) ≫ (hT.uniqueUpToIso terminalIsTerminal).hom =
        terminal.from ((cotensor K).obj E) := terminalIsTerminal.hom_ext _ _
    rw [← he, levelFibrations_iff]
    intro m
    have hiso : IsIso ((evaluation m).map (hT.uniqueUpToIso terminalIsTerminal).hom).right :=
      inferInstanceAs
        (IsIso ((evaluation m ⋙ forgetBasepoint).map (hT.uniqueUpToIso terminalIsTerminal).hom))
    rw [HomotopicalAlgebra.fibration_iff, Functor.map_comp, Under.comp_right]
    exact ((fibrations SSet.{0}).cancel_right_of_respectsIso _ _).2
      ((levelFibrations_iff _).1 hcot m).mem
  exact (levelFibrations_terminal_from_iff ((cotensor K).obj E)).1 hterm n

/-- Precomposition `E^L ⟶ E^K` along a based monomorphism is a level fibration whenever every
level of `E` is a Kan complex. -/
theorem levelFibrations_pre_free_zero_map (k : K ⟶ L) [Mono k.right] (E : SymmetricSpectrum)
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    levelFibrations ((MonoidalClosed.pre ((free 0).map k)).app E) :=
  levelFibrations_cotensor_pullbackObjObjπ k (terminal.from E)
    ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal cotensorBifunctor k (terminal.from E) terminalIsTerminal)

/-- Precomposition `E^L ⟶ E^K` along an anodyne based map is a level trivial fibration whenever
every level of `E` is a Kan complex. -/
theorem levelTrivialFibrations_pre_free_zero_map (k : K ⟶ L) (hk : SSet.anodyneExtensions k.right)
    (E : SymmetricSpectrum) (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    levelTrivialFibrations ((MonoidalClosed.pre ((free 0).map k)).app E) :=
  levelTrivialFibrations_cotensor_pullbackObjObjπ k (terminal.from E) hk
    ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal cotensorBifunctor k (terminal.from E) terminalIsTerminal)

end CotensorCorners

/-! ### Pushout-products for levelwise smash and simplicial tensors -/

section PushoutProducts

variable {A B : SymmetricSpectrum} {K L : PointedSSet.{0}} {U V : SSet.{0}}

/-- The pushout-product `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` of a projective cofibration and a
based monomorphism is a projective cofibration. -/
theorem projectiveCofibrations_levelSmash_pushoutObjObjι {i : A ⟶ B} {k : K ⟶ L}
    (hi : projectiveCofibrations i) [Mono k.right] (Q : curriedLevelSmash.PushoutObjObj i k) :
    projectiveCofibrations Q.ι := by
  rw [mem_projectiveCofibrations_iff] at hi ⊢
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor k p
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations k p hp P))

/-- The pushout-product `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` of a projective cofibration and an
anodyne based map lifts against every level fibration. -/
theorem llp_levelFibrations_levelSmash_pushoutObjObjι_of_anodyne {i : A ⟶ B} {k : K ⟶ L}
    (hi : projectiveCofibrations i) (hk : SSet.anodyneExtensions k.right)
    (Q : curriedLevelSmash.PushoutObjObj i k) :
    levelFibrations.llp Q.ι := by
  rw [mem_projectiveCofibrations_iff] at hi
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor k p
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelTrivialFibrations_cotensor_pullbackObjObjπ k p hk hp P))

/-- The pushout-product `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` of a map lifting against all level
fibrations and a based monomorphism again lifts against all level fibrations. -/
theorem llp_levelFibrations_levelSmash_pushoutObjObjι {i : A ⟶ B} {k : K ⟶ L}
    (hi : levelFibrations.llp i) [Mono k.right] (Q : curriedLevelSmash.PushoutObjObj i k) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor k p
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelFibrations_cotensor_pullbackObjObjπ k p hp P))

/-- The unpointed simplicial pushout-product `(A ∧ V₊) ⨿_(A ∧ U₊) (B ∧ U₊) ⟶ B ∧ V₊` of a
projective cofibration and a simplicial monomorphism is a projective cofibration. -/
theorem projectiveCofibrations_simplicialTensor_pushoutObjObjι {i : A ⟶ B} {j : U ⟶ V}
    (hi : projectiveCofibrations i) [Mono j] (Q : simplicialTensor.PushoutObjObj i j) :
    projectiveCofibrations Q.ι := by
  rw [mem_projectiveCofibrations_iff] at hi ⊢
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor j p
  exact (simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π
      (levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_levelTrivialFibrations j p hp
        P))

/-- The unpointed simplicial pushout-product `(A ∧ V₊) ⨿_(A ∧ U₊) (B ∧ U₊) ⟶ B ∧ V₊` of a
projective cofibration and an anodyne extension lifts against every level fibration. -/
theorem llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_anodyne {i : A ⟶ B} {j : U ⟶ V}
    (hi : projectiveCofibrations i) (hj : SSet.anodyneExtensions j)
    (Q : simplicialTensor.PushoutObjObj i j) :
    levelFibrations.llp Q.ι := by
  rw [mem_projectiveCofibrations_iff] at hi
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor j p
  exact (simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ j p hj hp P))

/-- The unpointed simplicial pushout-product `(A ∧ V₊) ⨿_(A ∧ U₊) (B ∧ U₊) ⟶ B ∧ V₊` of a map
lifting against all level fibrations and a simplicial monomorphism again lifts against all level
fibrations. -/
theorem llp_levelFibrations_simplicialTensor_pushoutObjObjι {i : A ⟶ B} {j : U ⟶ V}
    (hi : levelFibrations.llp i) [Mono j] (Q : simplicialTensor.PushoutObjObj i j) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor j p
  exact (simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelFibrations_simplicialCotensor_pullbackObjObjπ j p hp P))

/-- Levelwise smash with any pointed simplicial set `K` preserves projective cofibrations. -/
theorem projectiveCofibrations_levelSmashRight_map (K : PointedSSet.{0}) {i : A ⟶ B}
    (hi : projectiveCofibrations i) :
    projectiveCofibrations ((levelSmashRight K).map i) := by
  let k : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono k.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact projectiveCofibrations_levelSmash_pushoutObjObjι hi
    (Functor.PushoutObjObj.ofIsInitialRight curriedLevelSmash i k Under.mkIdInitial)

/-- Levelwise smash with any pointed simplicial set `K` preserves maps lifting against all level
fibrations. -/
theorem llp_levelFibrations_levelSmashRight_map (K : PointedSSet.{0}) {i : A ⟶ B}
    (hi : levelFibrations.llp i) :
    levelFibrations.llp ((levelSmashRight K).map i) := by
  let k : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono k.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact llp_levelFibrations_levelSmash_pushoutObjObjι hi
    (Functor.PushoutObjObj.ofIsInitialRight curriedLevelSmash i k Under.mkIdInitial)

/-- Smashing a projective-cofibrant spectrum with a based monomorphism gives a projective
cofibration. -/
theorem projectiveCofibrations_levelSmash_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) (k : K ⟶ L) [Mono k.right] :
    projectiveCofibrations ((levelSmash X).map k) :=
  projectiveCofibrations_levelSmash_pushoutObjObjι hX
    (Functor.PushoutObjObj.ofIsInitialLeft curriedLevelSmash (initial.to X) k initialIsInitial)

/-- Smashing a projective-cofibrant spectrum with an anodyne based map gives a map lifting against
all level fibrations. -/
theorem llp_levelFibrations_levelSmash_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {k : K ⟶ L} (hk : SSet.anodyneExtensions k.right) :
    levelFibrations.llp ((levelSmash X).map k) :=
  llp_levelFibrations_levelSmash_pushoutObjObjι_of_anodyne hX hk
    (Functor.PushoutObjObj.ofIsInitialLeft curriedLevelSmash (initial.to X) k initialIsInitial)

end PushoutProducts

/-! ### Mapping-space pullback-hom corners -/

section MappingSpaceCorners

variable {A B E F : SymmetricSpectrum}

/-- The unpointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of
a projective cofibration and a level fibration is a Kan fibration. -/
theorem fibration_simplicialMappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    Fibration P.π := by
  rw [HomotopicalAlgebra.fibration_iff,
    ← rlp_eq_of_wfs (W₁ := SSet.anodyneExtensions.{0}) (W₂ := fibrations SSet.{0})]
  intro U V j hj
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor i j
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q P]
  exact llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_anodyne hi hj Q p hp

/-- The unpointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of
a map lifting against all level fibrations and a level fibration lifts against every simplicial
monomorphism. -/
theorem rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π := by
  intro U V j (_ : Mono j)
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor i j
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q P]
  exact llp_levelFibrations_simplicialTensor_pushoutObjObjι hi Q p hp

/-- The unpointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of
a projective cofibration and a level trivial fibration lifts against every simplicial
monomorphism. -/
theorem rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations
    {i : A ⟶ B} {p : E ⟶ F} (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π := by
  intro U V j (_ : Mono j)
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor i j
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q P]
  exact ((mem_projectiveCofibrations_iff _).1
    (projectiveCofibrations_simplicialTensor_pushoutObjObjι hi Q)) p hp

/-- The pointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of a
projective cofibration and a level fibration is a Kan fibration on underlying simplicial sets. -/
theorem fibration_mappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    Fibration P.π.right :=
  fibration_simplicialMappingSpace_pullbackObjObjπ hi hp (P.map forgetBasepoint)

/-- The pointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of a
map lifting against all level fibrations and a level fibration lifts against every simplicial
monomorphism on underlying simplicial sets. -/
theorem rlp_monomorphisms_mappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π.right :=
  rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ hi hp (P.map forgetBasepoint)

/-- The pointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of a
projective cofibration and a level trivial fibration lifts against every simplicial monomorphism on
underlying simplicial sets. -/
theorem rlp_monomorphisms_mappingSpace_pullbackObjObjπ_of_levelTrivialFibrations
    {i : A ⟶ B} {p : E ⟶ F} (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π.right :=
  rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations hi hp
    (P.map forgetBasepoint)

/-- Mapping out of a projective-cofibrant spectrum carries level fibrations to Kan fibrations. -/
theorem fibration_mappingSpace_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelFibrations p) :
    Fibration ((mappingSpace X).map p).right :=
  fibration_mappingSpace_pullbackObjObjπ hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceBifunctor (initial.to X) p initialIsInitial)

/-- Mapping out of a projective-cofibrant spectrum carries level trivial fibrations to maps lifting
against all simplicial monomorphisms. -/
theorem rlp_monomorphisms_mappingSpace_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelTrivialFibrations p) :
    (monomorphisms SSet.{0}).rlp ((mappingSpace X).map p).right :=
  rlp_monomorphisms_mappingSpace_pullbackObjObjπ_of_levelTrivialFibrations hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceBifunctor (initial.to X) p initialIsInitial)

/-- Mapping out of a projective-cofibrant spectrum carries level trivial fibrations to weak
equivalences of simplicial sets. -/
theorem weakEquivalence_mappingSpace_map_of_levelTrivialFibrations {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelTrivialFibrations p) :
    WeakEquivalence ((mappingSpace X).map p).right :=
  weakEquivalence_of_rlp_monomorphisms (rlp_monomorphisms_mappingSpace_map hX hp)

/-- For a projective-cofibrant spectrum `X` and a spectrum `E` whose levels are Kan complexes, the
mapping space `Map(X, E)` is a Kan complex. -/
theorem kanComplex_mappingSpace {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) (E : SymmetricSpectrum)
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    SSet.KanComplex ((mappingSpace X).obj E).right := by
  have hT := terminalIsTerminal.isTerminalObj (mappingSpace X ⋙ forgetBasepoint)
    (⊤_ SymmetricSpectrum)
  have hf : Fibration (hT.from ((mappingSpace X).obj E).right) := by
    have heq : ((mappingSpace X).map (terminal.from E)).right =
        hT.from ((mappingSpace X).obj E).right := hT.hom_ext _ _
    rw [← heq]
    exact fibration_mappingSpace_map hX ((levelFibrations_terminal_from_iff E).2 hE)
  exact (isFibrant_iff_of_isTerminal _ hT).2 hf

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a projective cofibration is a Kan fibration
whenever every level of `E` is a Kan complex. -/
theorem fibration_mappingSpaceBifunctor_map_app {i : A ⟶ B} (hi : projectiveCofibrations i)
    (E : SymmetricSpectrum) (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    Fibration ((mappingSpaceBifunctor.map i.op).app E).right :=
  fibration_mappingSpace_pullbackObjObjπ hi ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceBifunctor i (terminal.from E)
      terminalIsTerminal)

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a map lifting against all level fibrations lifts
against every simplicial monomorphism whenever every level of `E` is a Kan complex. -/
theorem rlp_monomorphisms_mappingSpaceBifunctor_map_app {i : A ⟶ B} (hi : levelFibrations.llp i)
    (E : SymmetricSpectrum) (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    (monomorphisms SSet.{0}).rlp ((mappingSpaceBifunctor.map i.op).app E).right :=
  rlp_monomorphisms_mappingSpace_pullbackObjObjπ hi ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceBifunctor i (terminal.from E)
      terminalIsTerminal)

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a map lifting against all level fibrations is a
weak equivalence of simplicial sets whenever every level of `E` is a Kan complex. -/
theorem weakEquivalence_mappingSpaceBifunctor_map_app {i : A ⟶ B} (hi : levelFibrations.llp i)
    (E : SymmetricSpectrum) (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    WeakEquivalence ((mappingSpaceBifunctor.map i.op).app E).right :=
  weakEquivalence_of_rlp_monomorphisms
    (rlp_monomorphisms_mappingSpaceBifunctor_map_app hi E hE)

end MappingSpaceCorners

end TauCeti.SymmetricSpectrum
