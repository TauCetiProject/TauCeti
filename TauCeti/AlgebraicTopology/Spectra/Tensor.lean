/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
public import TauCeti.AlgebraicTopology.Spectra.Cotensor

/-!
# Two-variable tensors, cotensors, and mapping spaces of symmetric spectra

Smashing a symmetric spectrum levelwise with a pointed simplicial set, taking the point-set
cotensor `E^K`, and forming the pointed mapping space `Map(X, E)` assemble into curried bifunctors
linked by parametrized adjunctions (`Mathlib.CategoryTheory.Adjunction.Parametrized`):

* `SymmetricSpectrum.levelSmashCotensorAdjunction₂ : curriedLevelSmash.flip ⊣₂ cotensorBifunctor`,
  with parameter in `PointedSSet.{0}`;
* `SymmetricSpectrum.levelSmashMappingSpaceAdjunction₂ :
  curriedLevelSmash ⊣₂ mappingSpaceBifunctor`, with parameter in `SymmetricSpectrum`.

Precomposing in the simplicial-set variable with `PointedSSet.addBasepoint` and postcomposing in
the mapping-space target with `PointedSSet.forgetBasepoint` yields the unpointed simplicial
counterparts `simplicialTensor`, `simplicialCotensor`, and `simplicialMappingSpace`, together with
their parametrized adjunctions `simplicialTensorCotensorAdjunction₂` and
`simplicialTensorMappingSpaceAdjunction₂`. From these adjunctions and
`Mathlib.CategoryTheory.Adjunction.ParametrizedLimits`, each bifunctor preserves colimits or limits
of every size separately in each variable, and `cotensorEvaluationNatIso` packages the level
formula `(E^K)_n ≅ Map_*(K, E_n)` as a natural isomorphism of bifunctors.

These are point-set constructions; no weak factorization system or model structure is assumed.

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
* `SymmetricSpectrum.cotensorEvaluationNatIso`: natural isomorphism identifying level `n` of
  `cotensorBifunctor` with the pointed internal hom on level `n`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1–3.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite
open scoped DayFunctor

namespace TauCeti.SymmetricSpectrum

open PointedSSet

/-! ### Pointed two-variable bifunctors and parametrized adjunctions -/

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

/-- At `op K`, `cotensorBifunctor` acts on spectrum maps by `(cotensor K).map`. -/
@[simp]
lemma cotensorBifunctor_obj_map (K : PointedSSet.{0}) {E F : SymmetricSpectrum} (p : E ⟶ F) :
    (cotensorBifunctor.obj (op K)).map p = (cotensor K).map p := (rfl)

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

/-- At `op X`, `mappingSpaceBifunctor` acts on spectrum maps by `(mappingSpace X).map`. -/
@[simp]
lemma mappingSpaceBifunctor_obj_map (X : SymmetricSpectrum) {E F : SymmetricSpectrum} (p : E ⟶ F) :
    (mappingSpaceBifunctor.obj (op X)).map p = (mappingSpace X).map p := (rfl)

/-- On `i.op`, `mappingSpaceBifunctor` acts at `E` by level zero of internal precomposition along
`i`. -/
@[simp]
lemma mappingSpaceBifunctor_map_app {A B : SymmetricSpectrum} (i : A ⟶ B) (E : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map i.op).app E =
      (((MonoidalClosed.pre i).app E).hom).natTrans.app (FiniteBijection.mk 0) := (rfl)

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

/-- At parameter `K`, `levelSmashCotensorAdjunction₂` is `levelSmashCotensorAdjunction K`. -/
@[simp]
lemma levelSmashCotensorAdjunction₂_adj (K : PointedSSet.{0}) :
    levelSmashCotensorAdjunction₂.adj K = levelSmashCotensorAdjunction K := (rfl)

/-- The hom-set equivalence of `levelSmashCotensorAdjunction₂` is that of
`levelSmashCotensorAdjunction`. -/
@[simp]
lemma levelSmashCotensorAdjunction₂_homEquiv {K : PointedSSet.{0}} {E F : SymmetricSpectrum} :
    levelSmashCotensorAdjunction₂.homEquiv (X₁ := K) (X₂ := E) (X₃ := F) =
      (levelSmashCotensorAdjunction K).homEquiv E F := (rfl)

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

/-- At parameter `X`, `levelSmashMappingSpaceAdjunction₂` is
`levelSmashMappingSpaceAdjunction X`. -/
@[simp]
lemma levelSmashMappingSpaceAdjunction₂_adj (X : SymmetricSpectrum) :
    levelSmashMappingSpaceAdjunction₂.adj X = levelSmashMappingSpaceAdjunction X := (rfl)

/-- The hom-set equivalence of `levelSmashMappingSpaceAdjunction₂` is that of
`levelSmashMappingSpaceAdjunction`. -/
@[simp]
lemma levelSmashMappingSpaceAdjunction₂_homEquiv {X : SymmetricSpectrum} {K : PointedSSet.{0}}
    {E : SymmetricSpectrum} :
    levelSmashMappingSpaceAdjunction₂.homEquiv (X₁ := X) (X₂ := K) (X₃ := E) =
      (levelSmashMappingSpaceAdjunction X).homEquiv K E := (rfl)

/-- For a fixed target spectrum `E`, the cotensor `K ↦ E^K` sends colimits of pointed simplicial
sets to limits of symmetric spectra of every size. -/
instance cotensorBifunctor_flip_obj_preservesLimitsOfSize.{v, w} (E : SymmetricSpectrum) :
    PreservesLimitsOfSize.{v, w} (cotensorBifunctor.flip.obj E) where
  preservesLimitsOfShape {J} _ := by
    have (X : SymmetricSpectrum) :
        PreservesColimitsOfShape Jᵒᵖ (curriedLevelSmash.flip.flip.obj X) := by
      rw [Functor.flip_flip, curriedLevelSmash_obj]
      infer_instance
    exact levelSmashCotensorAdjunction₂.preservesLimitsOfShape_flip_obj J E

/-- For a fixed target spectrum `E`, the pointed mapping space `X ↦ Map(X, E)` sends colimits of
symmetric spectra to limits of pointed simplicial sets of every size. -/
instance mappingSpaceBifunctor_flip_obj_preservesLimitsOfSize.{v, w} (E : SymmetricSpectrum) :
    PreservesLimitsOfSize.{v, w} (mappingSpaceBifunctor.flip.obj E) where
  preservesLimitsOfShape {J} _ :=
    levelSmashMappingSpaceAdjunction₂.preservesLimitsOfShape_flip_obj J E

/-! ### Unpointed simplicial tensors, cotensors, and mapping spaces -/

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

/-- At `X`, `simplicialTensor` acts on a simplicial map `j` by `(levelSmash X).map (j₊)`. -/
@[simp]
lemma simplicialTensor_obj_map (X : SymmetricSpectrum) {K L : SSet.{0}} (j : K ⟶ L) :
    (simplicialTensor.obj X).map j = (levelSmash X).map (addBasepoint.map j) := (rfl)

/-- On a spectrum map `f`, `simplicialTensor` acts at `K` by `(levelSmashRight (K₊)).map f`. -/
@[simp]
lemma simplicialTensor_map_app {X Y : SymmetricSpectrum} (f : X ⟶ Y) (K : SSet.{0}) :
    (simplicialTensor.map f).app K = (levelSmashRight (addBasepoint.obj K)).map f := (rfl)

/-- Evaluating `simplicialCotensor` at `op K` gives `cotensor (K₊)`. -/
@[simp]
lemma simplicialCotensor_obj (K : SSet.{0}) :
    simplicialCotensor.obj (op K) = cotensor (addBasepoint.obj K) := (rfl)

/-- At `op K`, `simplicialCotensor` acts on spectrum maps by `(cotensor (K₊)).map`. -/
@[simp]
lemma simplicialCotensor_obj_map (K : SSet.{0}) {E F : SymmetricSpectrum} (p : E ⟶ F) :
    (simplicialCotensor.obj (op K)).map p = (cotensor (addBasepoint.obj K)).map p := (rfl)

/-- On `j.op`, `simplicialCotensor` acts at `E` by precomposition along `(free 0).map (j₊)`. -/
@[simp]
lemma simplicialCotensor_map_app {K L : SSet.{0}} (j : K ⟶ L) (E : SymmetricSpectrum) :
    (simplicialCotensor.map j.op).app E =
      (MonoidalClosed.pre ((free 0).map (addBasepoint.map j))).app E := (rfl)

/-- Evaluating `simplicialMappingSpace` at `op X` gives `mappingSpace X ⋙ forgetBasepoint`. -/
@[simp]
lemma simplicialMappingSpace_obj (X : SymmetricSpectrum) :
    simplicialMappingSpace.obj (op X) = mappingSpace X ⋙ forgetBasepoint := (rfl)

/-- At `op X`, `simplicialMappingSpace` acts on spectrum maps by the underlying simplicial map of
`(mappingSpace X).map`. -/
@[simp]
lemma simplicialMappingSpace_obj_map (X : SymmetricSpectrum) {E F : SymmetricSpectrum} (p : E ⟶ F) :
    (simplicialMappingSpace.obj (op X)).map p = ((mappingSpace X).map p).right := (rfl)

/-- On `i.op`, `simplicialMappingSpace` acts at `E` by the underlying simplicial map of level zero
of internal precomposition along `i`. -/
@[simp]
lemma simplicialMappingSpace_map_app {A B : SymmetricSpectrum} (i : A ⟶ B) (E : SymmetricSpectrum) :
    (simplicialMappingSpace.map i.op).app E =
      ((((MonoidalClosed.pre i).app E).hom).natTrans.app (FiniteBijection.mk 0)).right := (rfl)

/-- The parametrized adjunction between unpointed simplicial tensors and cotensors of symmetric
spectra. -/
noncomputable def simplicialTensorCotensorAdjunction₂ :
    simplicialTensor.flip ⊣₂ simplicialCotensor :=
  ParametrizedAdjunction.mk' (fun K ↦ levelSmashCotensorAdjunction (addBasepoint.obj K))
    fun {_ _} j {_ _} g ↦
      levelSmashCotensorAdjunction₂.homEquiv_naturality_one (addBasepoint.map j) g

/-- At parameter `K`, `simplicialTensorCotensorAdjunction₂` is
`levelSmashCotensorAdjunction (K₊)`. -/
@[simp]
lemma simplicialTensorCotensorAdjunction₂_adj (K : SSet.{0}) :
    simplicialTensorCotensorAdjunction₂.adj K =
      levelSmashCotensorAdjunction (addBasepoint.obj K) := (rfl)

/-- The hom-set equivalence of `simplicialTensorCotensorAdjunction₂` is that of
`levelSmashCotensorAdjunction (K₊)`. -/
@[simp]
lemma simplicialTensorCotensorAdjunction₂_homEquiv {K : SSet.{0}} {E F : SymmetricSpectrum} :
    simplicialTensorCotensorAdjunction₂.homEquiv (X₁ := K) (X₂ := E) (X₃ := F) =
      (levelSmashCotensorAdjunction (addBasepoint.obj K)).homEquiv E F := (rfl)

/-- The parametrized adjunction between unpointed simplicial tensors and unpointed spectral mapping
spaces. -/
noncomputable def simplicialTensorMappingSpaceAdjunction₂ :
    simplicialTensor ⊣₂ simplicialMappingSpace where
  adj X := addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X)
  unit_whiskerRight_map {A B} i := NatTrans.ext <| funext fun K ↦ by
    have hu (X : SymmetricSpectrum) :
        dsimp% (addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X)).unit.app K =
          addBasepointForgetAdjunction.unit.app K ≫
            ((levelSmashMappingSpaceAdjunction X).unit.app (addBasepoint.obj K)).right :=
      Adjunction.comp_unit_app addBasepointForgetAdjunction (levelSmashMappingSpaceAdjunction X) K
    exact (congrArg (· ≫ _) (hu A)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (addBasepointForgetAdjunction.unit.app K ≫ Under.Hom.right ·)
          (NatTrans.congr_app (levelSmashMappingSpaceAdjunction₂.unit_whiskerRight_map i)
            (addBasepoint.obj K))).trans <|
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hu B).symm)

/-- At parameter `X`, `simplicialTensorMappingSpaceAdjunction₂` is the composite of
`addBasepointForgetAdjunction` with `levelSmashMappingSpaceAdjunction X`. -/
@[simp]
lemma simplicialTensorMappingSpaceAdjunction₂_adj (X : SymmetricSpectrum) :
    simplicialTensorMappingSpaceAdjunction₂.adj X =
      addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X) := (rfl)

/-- The hom-set equivalence of `simplicialTensorMappingSpaceAdjunction₂` composes
`(levelSmashMappingSpaceAdjunction X).homEquiv` with `addBasepointHomEquiv`. -/
@[simp]
lemma simplicialTensorMappingSpaceAdjunction₂_homEquiv {X : SymmetricSpectrum} {K : SSet.{0}}
    {E : SymmetricSpectrum} :
    simplicialTensorMappingSpaceAdjunction₂.homEquiv (X₁ := X) (X₂ := K) (X₃ := E) =
      ((levelSmashMappingSpaceAdjunction X).homEquiv (addBasepoint.obj K) E).trans
        (addBasepointHomEquiv K ((mappingSpace X).obj E)) :=
  (congrFun (congrFun (addBasepointForgetAdjunction.comp_homEquiv
    (levelSmashMappingSpaceAdjunction X)) K) E).trans
    (congrArg _ (addBasepointForgetAdjunction_homEquiv K ((mappingSpace X).obj E)))

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

/-- For a fixed target spectrum `E`, the unpointed simplicial cotensor `K ↦ E^(K₊)` sends colimits
of simplicial sets to limits of symmetric spectra of every size. -/
instance simplicialCotensor_flip_obj_preservesLimitsOfSize.{v, w} (E : SymmetricSpectrum) :
    PreservesLimitsOfSize.{v, w} (simplicialCotensor.flip.obj E) where
  preservesLimitsOfShape {J} _ := by
    have (X : SymmetricSpectrum) :
        PreservesColimitsOfShape Jᵒᵖ (simplicialTensor.flip.flip.obj X) := by
      rw [Functor.flip_flip]
      infer_instance
    exact simplicialTensorCotensorAdjunction₂.preservesLimitsOfShape_flip_obj J E

/-- For a fixed target spectrum `E`, the unpointed simplicial mapping space `X ↦ (Map(X, E)).right`
sends colimits of symmetric spectra to limits of simplicial sets of every size. -/
instance simplicialMappingSpace_flip_obj_preservesLimitsOfSize.{v, w} (E : SymmetricSpectrum) :
    PreservesLimitsOfSize.{v, w} (simplicialMappingSpace.flip.obj E) where
  preservesLimitsOfShape {J} _ :=
    simplicialTensorMappingSpaceAdjunction₂.preservesLimitsOfShape_flip_obj J E

/-! ### Levelwise identification of the cotensor bifunctor -/

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

end TauCeti.SymmetricSpectrum
