/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Tensor
public import TauCeti.AlgebraicTopology.Spectra.Cotensor
public import Mathlib.CategoryTheory.Adjunction.Parametrized

import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits

/-!
# Simplicial tensors, cotensors, and mapping-space bifunctors of symmetric spectra

The levelwise smash product `X ∧ K`, the point-set cotensor `E^K`, and the pointed mapping space
`Map(X, Y)` of symmetric spectra assemble into bifunctors connected by two-variable adjunctions:

* `SymmetricSpectrum.levelSmashBifunctor : SymmetricSpectrum ⥤ PointedSSet.{0} ⥤ SymmetricSpectrum`
  sends `(X, K)` to `X ∧ K`;
* `SymmetricSpectrum.cotensorBifunctor : PointedSSet.{0}ᵒᵖ ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum`
  sends `(K, E)` to `E^K`;
* `SymmetricSpectrum.mappingSpaceBifunctor :`
  `SymmetricSpectrumᵒᵖ ⥤ SymmetricSpectrum ⥤ PointedSSet.{0}` sends `(X, Y)` to `Map(X, Y)`.

These satisfy the parametrized adjunctions `levelSmashBifunctor ⊣₂ mappingSpaceBifunctor` and
`levelSmashBifunctor.flip ⊣₂ cotensorBifunctor`. Precomposing with the disjoint-basepoint functor
`PointedSSet.addBasepoint` and forgetting basepoints on mapping spaces yields the unpointed
simplicial structure on symmetric spectra:

* `SymmetricSpectrum.simplicialTensor`: `(K, X) ↦ X ∧ K₊`;
* `SymmetricSpectrum.simplicialCotensor`: `(K, E) ↦ E^(K₊)`;
* `SymmetricSpectrum.simplicialMappingSpace`: `(X, Y) ↦ Map(X, Y)` as an unpointed simplicial set,

together with their parametrized adjunctions `simplicialTensor ⊣₂ simplicialCotensor` and
`simplicialTensor.flip ⊣₂ simplicialMappingSpace`, hom-set equivalences, and colimit/limit
preservation instances in each variable.

All constructions here are point-set constructions on `SymmetricSpectrum`; deriving them requires
a model structure.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1.3 and 2.2.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

namespace TauCeti.SymmetricSpectrum

open PointedSSet

/-! ### Pointed smash, cotensor, and mapping-space bifunctors -/

/-- The bifunctor `(X, K) ↦ X ∧ K` smashing a symmetric spectrum levelwise with a pointed
simplicial set. Fixing `X` recovers `levelSmash X`, and fixing `K` recovers `levelSmashRight K`. -/
@[expose]
noncomputable def levelSmashBifunctor :
    SymmetricSpectrum ⥤ PointedSSet.{0} ⥤ SymmetricSpectrum where
  obj X := levelSmash X
  map {X Y} f :=
    { app K := (levelSmashRight K).map f
      naturality {K L} g := by
        apply Mod.Hom.ext
        simp only [Mod.comp_hom', Mod.Hom.mk'_hom]
        exact whisker_exchange f.hom ((SymmetricSequence.free 0).map g) }
  map_id X := by
    apply NatTrans.ext
    funext K
    exact (levelSmashRight K).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext K
    exact (levelSmashRight K).map_comp f g

@[simp]
lemma levelSmashBifunctor_obj (X : SymmetricSpectrum) :
    levelSmashBifunctor.obj X = levelSmash X :=
  rfl

@[simp]
lemma levelSmashBifunctor_flip_obj (K : PointedSSet.{0}) :
    levelSmashBifunctor.flip.obj K = levelSmashRight K :=
  rfl

@[simp]
lemma levelSmashBifunctor_map_app {X Y : SymmetricSpectrum} (f : X ⟶ Y) (K : PointedSSet.{0}) :
    (levelSmashBifunctor.map f).app K = (levelSmashRight K).map f :=
  rfl

lemma levelSmashBifunctor_flip_map_app {K L : PointedSSet.{0}} (g : K ⟶ L)
    (X : SymmetricSpectrum) :
    (levelSmashBifunctor.flip.map g).app X = (levelSmash X).map g :=
  rfl

/-- The point-set cotensor bifunctor `(K, E) ↦ E^K`, contravariant in the pointed simplicial set
`K` and covariant in the symmetric spectrum `E`. -/
@[expose]
noncomputable def cotensorBifunctor :
    PointedSSet.{0}ᵒᵖ ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum :=
  (free 0).op ⋙ MonoidalClosed.internalHom

@[simp]
lemma cotensorBifunctor_obj_op (K : PointedSSet.{0}) :
    cotensorBifunctor.obj (op K) = cotensor K :=
  rfl

@[simp]
lemma cotensorBifunctor_map_app {K L : PointedSSet.{0}} (g : K ⟶ L) (E : SymmetricSpectrum) :
    (cotensorBifunctor.map g.op).app E = (MonoidalClosed.pre ((free 0).map g)).app E :=
  rfl

/-- The pointed mapping-space bifunctor `(X, Y) ↦ Map(X, Y)` of symmetric spectra, contravariant
in the source spectrum `X` and covariant in the target spectrum `Y`. Fixing `X` recovers
`mappingSpace X`, while a map `f : X ⟶ X'` acts by level-zero internal-hom precomposition. -/
@[expose]
noncomputable def mappingSpaceBifunctor :
    SymmetricSpectrumᵒᵖ ⥤ SymmetricSpectrum ⥤ PointedSSet.{0} where
  obj X := mappingSpace X.unop
  map {X X'} f :=
    { app Y := (evaluation 0).map ((MonoidalClosed.pre f.unop).app Y)
      naturality {Y Y'} g :=
        ((evaluation 0).map_comp ((CategoryTheory.ihom X.unop).map g)
          ((MonoidalClosed.pre f.unop).app Y')).symm.trans <|
          (congrArg (evaluation 0).map ((MonoidalClosed.pre f.unop).naturality g)).trans <|
            (evaluation 0).map_comp ((MonoidalClosed.pre f.unop).app Y)
              ((CategoryTheory.ihom X'.unop).map g) }
  map_id X := by
    apply NatTrans.ext
    funext Y
    simp only [unop_id, MonoidalClosed.pre_id, NatTrans.id_app]
    rfl
  map_comp {X Y Z} f g := by
    apply NatTrans.ext
    funext W
    have h := congrArg (fun p : ihom X.unop ⟶ ihom Z.unop ↦ (evaluation 0).map (p.app W))
      (MonoidalClosed.pre_map g.unop f.unop)
    exact h.trans ((evaluation 0).map_comp _ _)

@[simp]
lemma mappingSpaceBifunctor_obj (X : SymmetricSpectrumᵒᵖ) :
    mappingSpaceBifunctor.obj X = mappingSpace X.unop :=
  rfl

@[simp]
lemma mappingSpaceBifunctor_map_app {X X' : SymmetricSpectrum} (f : X ⟶ X')
    (Y : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map f.op).app Y = (evaluation 0).map ((MonoidalClosed.pre f).app Y) :=
  rfl

/-- The parametrized adjunction `levelSmashBifunctor ⊣₂ mappingSpaceBifunctor`: spectrum maps
`X ∧ K ⟶ Y` correspond naturally in all three variables to based maps `K ⟶ Map(X, Y)`. -/
noncomputable def levelSmashMappingSpaceAdjunction₂ :
    levelSmashBifunctor ⊣₂ mappingSpaceBifunctor :=
  ParametrizedAdjunction.mk' levelSmashMappingSpaceAdjunction fun {X Y} f {K} {Z} g ↦ by
    let g' : (levelSmash Y).obj K ⟶ Z := g
    let p : (Mod.internalHom Y).obj Z ⟶ (Mod.internalHom X).obj Z := (MonoidalClosed.pre f).app Z
    have hp : p.hom ≫ Mod.ihomι X Z = Mod.ihomι Y Z ≫ (MonoidalClosed.pre f.hom).app Z.X :=
      Mod.pre_app_hom_comp_ihomι f Z
    refine (levelSmashMappingSpaceAdjunction_homEquiv_apply X
      ((levelSmashRight K).map f ≫ g')).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ (evaluation 0).map p)
      (levelSmashMappingSpaceAdjunction_homEquiv_apply Y g').symm)
    change SymmetricSequence.freeι 0 K ≫
        (Mod.ihomHomEquiv X _ Z ((levelSmashRight K).map f ≫ g')).natTrans.app
          (FiniteBijection.mk 0) =
      SymmetricSequence.freeι 0 K ≫
        ((Mod.ihomHomEquiv Y _ Z g' ≫ p.hom).natTrans.app (FiniteBijection.mk 0))
    congr 1
    refine congrArg
      (fun h : (SymmetricSequence.free 0).obj K ⟶ (Mod.ihom X).obj Z ↦
        h.natTrans.app (FiniteBijection.mk 0)) ?_
    apply Mod.ihom_hom_ext
    rw [Mod.ihomHomEquiv_apply_comp_ihomι, Category.assoc, hp,
      Mod.ihomHomEquiv_apply_comp_ihomι_assoc, MonoidalClosed.curry_pre_app]
    rfl

/-- The parametrized adjunction `levelSmashBifunctor.flip ⊣₂ cotensorBifunctor`: spectrum maps
`E ∧ K ⟶ F` correspond naturally in all three variables to spectrum maps `E ⟶ F^K`. -/
noncomputable def levelSmashCotensorAdjunction₂ :
    levelSmashBifunctor.flip ⊣₂ cotensorBifunctor :=
  ParametrizedAdjunction.mk' levelSmashCotensorAdjunction fun {K L} j {E} {F} g ↦ by
    let g' : (levelSmashRight L).obj E ⟶ F := g
    refine (levelSmashCotensorAdjunction_homEquiv_apply K ((levelSmash E).map j ≫ g')).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ (MonoidalClosed.pre ((free 0).map j)).app F)
      (levelSmashCotensorAdjunction_homEquiv_apply L g').symm)
    refine (Mod.curry_eq_tensorHomEquiv ((free 0).obj K) E F _).symm.trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ (MonoidalClosed.pre ((free 0).map j)).app F)
      (Mod.curry_eq_tensorHomEquiv ((free 0).obj L) E F _))
    refine Eq.trans ?_ (MonoidalClosed.curry_pre_app ((free 0).map j) _).symm
    refine congrArg MonoidalClosed.curry ?_
    have hnat : (E ◁ (free 0).map j) ≫
        (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj L) =
      (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj K) ≫ (levelSmash E).map j :=
      (Mod.tensorFreeIso E).hom.naturality ((SymmetricSequence.free 0).map j)
    rw [← Category.assoc ((Mod.tensorFreeIso E).hom.app _), ← hnat, Category.assoc,
      ← BraidedCategory.braiding_naturality_left_assoc ((free 0).map j) E]

/-! ### Unpointed simplicial tensor, cotensor, and mapping-space bifunctors -/

/-- Tensoring a symmetric spectrum with an unpointed simplicial set: `(K, X) ↦ X ∧ K₊`. -/
@[expose]
noncomputable def simplicialTensor :
    SSet.{0} ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum :=
  addBasepoint ⋙ levelSmashBifunctor.flip

/-- Cotensoring a symmetric spectrum by an unpointed simplicial set: `(K, E) ↦ E^(K₊)`. -/
@[expose]
noncomputable def simplicialCotensor :
    SSet.{0}ᵒᵖ ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum :=
  addBasepoint.op ⋙ cotensorBifunctor

/-- The unpointed mapping simplicial set `(X, Y) ↦ Map(X, Y)` of symmetric spectra, obtained by
forgetting the basepoint of `mappingSpaceBifunctor`. -/
@[expose]
noncomputable def simplicialMappingSpace :
    SymmetricSpectrumᵒᵖ ⥤ SymmetricSpectrum ⥤ SSet.{0} :=
  mappingSpaceBifunctor ⋙
    (Functor.whiskeringRight SymmetricSpectrum PointedSSet.{0} SSet.{0}).obj forgetBasepoint

@[simp]
lemma simplicialTensor_obj (K : SSet.{0}) :
    simplicialTensor.obj K = levelSmashRight (addBasepoint.obj K) :=
  rfl

@[simp]
lemma simplicialTensor_map_app {K L : SSet.{0}} (g : K ⟶ L) (X : SymmetricSpectrum) :
    (simplicialTensor.map g).app X = (levelSmash X).map (addBasepoint.map g) :=
  rfl

@[simp]
lemma simplicialCotensor_obj_op (K : SSet.{0}) :
    simplicialCotensor.obj (op K) = cotensor (addBasepoint.obj K) :=
  rfl

@[simp]
lemma simplicialCotensor_map_app {K L : SSet.{0}} (g : K ⟶ L) (E : SymmetricSpectrum) :
    (simplicialCotensor.map g.op).app E =
      (MonoidalClosed.pre ((free 0).map (addBasepoint.map g))).app E :=
  rfl

@[simp]
lemma simplicialMappingSpace_obj_obj (X : SymmetricSpectrumᵒᵖ) (Y : SymmetricSpectrum) :
    (simplicialMappingSpace.obj X).obj Y = ((mappingSpace X.unop).obj Y).right :=
  rfl

@[simp]
lemma simplicialMappingSpace_obj_map (X : SymmetricSpectrumᵒᵖ) {Y Y' : SymmetricSpectrum}
    (g : Y ⟶ Y') :
    (simplicialMappingSpace.obj X).map g = ((mappingSpace X.unop).map g).right :=
  rfl

@[simp]
lemma simplicialMappingSpace_map_app {X X' : SymmetricSpectrum} (f : X ⟶ X')
    (Y : SymmetricSpectrum) :
    (simplicialMappingSpace.map f.op).app Y =
      ((evaluation 0).map ((MonoidalClosed.pre f).app Y)).right :=
  rfl

/-- For each simplicial set `K`, tensoring a symmetric spectrum with `K` is left adjoint to
cotensoring by `K`. -/
noncomputable def simplicialTensorCotensorAdjunction (K : SSet.{0}) :
    simplicialTensor.obj K ⊣ simplicialCotensor.obj (op K) :=
  levelSmashCotensorAdjunction (addBasepoint.obj K)

/-- For each symmetric spectrum `X`, smashing `X` with `(-)₊` is left adjoint to the unpointed
mapping space `Map(X, -)`. -/
noncomputable def simplicialTensorMappingSpaceAdjunction (X : SymmetricSpectrum) :
    simplicialTensor.flip.obj X ⊣ simplicialMappingSpace.obj (op X) :=
  addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X)

/-- The parametrized adjunction `simplicialTensor ⊣₂ simplicialCotensor`: spectrum maps
`X ∧ K₊ ⟶ Y` correspond naturally in all three variables to spectrum maps `X ⟶ Y^(K₊)`. -/
noncomputable def simplicialTensorCotensorAdjunction₂ :
    simplicialTensor ⊣₂ simplicialCotensor :=
  ParametrizedAdjunction.mk' simplicialTensorCotensorAdjunction fun {_ _} f {_} {_} g ↦
    levelSmashCotensorAdjunction₂.homEquiv_naturality_one (addBasepoint.map f) g

/-- The parametrized adjunction `simplicialTensor.flip ⊣₂ simplicialMappingSpace`: spectrum maps
`X ∧ K₊ ⟶ Y` correspond naturally in all three variables to simplicial maps `K ⟶ Map(X, Y)`. -/
noncomputable def simplicialTensorMappingSpaceAdjunction₂ :
    simplicialTensor.flip ⊣₂ simplicialMappingSpace :=
  ParametrizedAdjunction.mk' simplicialTensorMappingSpaceAdjunction fun {X Y} f {K} {Z} g ↦ by
    let g' : (levelSmash Y).obj (addBasepoint.obj K) ⟶ Z := g
    have h1 := levelSmashMappingSpaceAdjunction₂.homEquiv_naturality_one f g'
    have h2 := addBasepointForgetAdjunction.homEquiv_naturality_right
      ((levelSmashMappingSpaceAdjunction Y).homEquiv (addBasepoint.obj K) Z g')
      ((mappingSpaceBifunctor.map f.op).app Z)
    have hX := congrFun (congrFun (addBasepointForgetAdjunction.comp_homEquiv
      (levelSmashMappingSpaceAdjunction X)) K) Z
    have hY := congrFun (congrFun (addBasepointForgetAdjunction.comp_homEquiv
      (levelSmashMappingSpaceAdjunction Y)) K) Z
    refine (congrFun (congrArg DFunLike.coe hX)
      ((levelSmashRight (addBasepoint.obj K)).map f ≫ g')).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ ((mappingSpaceBifunctor.map f.op).app Z).right)
      (congrFun (congrArg DFunLike.coe hY) g').symm)
    exact (congrArg (addBasepointForgetAdjunction.homEquiv K _) h1).trans h2

/-! ### Hom-set equivalences and naturality -/

/-- The universal property of the simplicial tensor on symmetric spectra: maps `X ∧ K₊ ⟶ Y`
correspond to maps of simplicial sets `K ⟶ Map(X, Y)`. -/
noncomputable def simplicialTensorHomEquiv (K : SSet.{0}) (X Y : SymmetricSpectrum) :
    ((simplicialTensor.obj K).obj X ⟶ Y) ≃
      (K ⟶ ((mappingSpace X).obj Y).right) :=
  simplicialTensorMappingSpaceAdjunction₂.homEquiv

/-- The universal property of the simplicial cotensor on symmetric spectra: maps `X ⟶ Y^(K₊)`
correspond to maps of simplicial sets `K ⟶ Map(X, Y)`. -/
noncomputable def homSimplicialCotensorEquiv (K : SSet.{0}) (X Y : SymmetricSpectrum) :
    (X ⟶ (simplicialCotensor.obj (op K)).obj Y) ≃
      (K ⟶ ((mappingSpace X).obj Y).right) :=
  simplicialTensorCotensorAdjunction₂.homEquiv.symm.trans (simplicialTensorHomEquiv K X Y)

/-- `simplicialTensorHomEquiv` is natural in the simplicial set `K`. -/
lemma simplicialTensorHomEquiv_naturality_simplicial {K' K : SSet.{0}} (g : K' ⟶ K)
    {X Y : SymmetricSpectrum} (f : (levelSmashRight (addBasepoint.obj K)).obj X ⟶ Y) :
    simplicialTensorHomEquiv K' X Y ((levelSmash X).map (addBasepoint.map g) ≫ f) =
      g ≫ simplicialTensorHomEquiv K X Y f :=
  simplicialTensorMappingSpaceAdjunction₂.homEquiv_naturality_two g f

/-- `simplicialTensorHomEquiv` is natural in the source spectrum `X`. -/
lemma simplicialTensorHomEquiv_naturality_left {K : SSet.{0}} {X' X Y : SymmetricSpectrum}
    (h : X' ⟶ X) (f : (levelSmashRight (addBasepoint.obj K)).obj X ⟶ Y) :
    simplicialTensorHomEquiv K X' Y ((levelSmashRight (addBasepoint.obj K)).map h ≫ f) =
      simplicialTensorHomEquiv K X Y f ≫
        ((evaluation 0).map ((MonoidalClosed.pre h).app Y)).right :=
  simplicialTensorMappingSpaceAdjunction₂.homEquiv_naturality_one h f

/-- `simplicialTensorHomEquiv` is natural in the target spectrum `Y`. -/
@[simp]
lemma simplicialTensorHomEquiv_comp {K : SSet.{0}} {X Y Y' : SymmetricSpectrum}
    (f : (levelSmashRight (addBasepoint.obj K)).obj X ⟶ Y) (g : Y ⟶ Y') :
    dsimp% simplicialTensorHomEquiv K X Y' (f ≫ g) =
      simplicialTensorHomEquiv K X Y f ≫ ((mappingSpace X).map g).right :=
  simplicialTensorMappingSpaceAdjunction₂.homEquiv_naturality_three g f

/-- `homSimplicialCotensorEquiv` is natural in the simplicial set `K`. -/
lemma homSimplicialCotensorEquiv_naturality_simplicial {K' K : SSet.{0}} (g : K' ⟶ K)
    {X Y : SymmetricSpectrum} (f : X ⟶ (cotensor (addBasepoint.obj K)).obj Y) :
    homSimplicialCotensorEquiv K' X Y
        (f ≫ (MonoidalClosed.pre ((free 0).map (addBasepoint.map g))).app Y) =
      g ≫ homSimplicialCotensorEquiv K X Y f :=
  (congrArg (simplicialTensorHomEquiv K' X Y)
    (simplicialTensorCotensorAdjunction₂.homEquiv_symm_naturality_one g f)).trans
    (simplicialTensorHomEquiv_naturality_simplicial g _)

/-- `homSimplicialCotensorEquiv` is natural in the source spectrum `X`. -/
@[simp]
lemma homSimplicialCotensorEquiv_comp {K : SSet.{0}} {X' X Y : SymmetricSpectrum}
    (h : X' ⟶ X) (f : X ⟶ (cotensor (addBasepoint.obj K)).obj Y) :
    dsimp% homSimplicialCotensorEquiv K X' Y (h ≫ f) =
      homSimplicialCotensorEquiv K X Y f ≫
        ((evaluation 0).map ((MonoidalClosed.pre h).app Y)).right :=
  (congrArg (simplicialTensorHomEquiv K X' Y)
    (simplicialTensorCotensorAdjunction₂.homEquiv_symm_naturality_two h f)).trans
    (simplicialTensorHomEquiv_naturality_left h _)

/-- `homSimplicialCotensorEquiv` is natural in the target spectrum `Y`. -/
lemma homSimplicialCotensorEquiv_naturality_right {K : SSet.{0}} {X Y Y' : SymmetricSpectrum}
    (f : X ⟶ (cotensor (addBasepoint.obj K)).obj Y) (g : Y ⟶ Y') :
    homSimplicialCotensorEquiv K X Y' (f ≫ (cotensor (addBasepoint.obj K)).map g) =
      homSimplicialCotensorEquiv K X Y f ≫ ((mappingSpace X).map g).right :=
  (congrArg (simplicialTensorHomEquiv K X Y')
    (simplicialTensorCotensorAdjunction₂.homEquiv_symm_naturality_three g f)).trans
    (simplicialTensorHomEquiv_comp _ g)

/-! ### Colimit and limit preservation in each variable -/

instance (X : SymmetricSpectrum) : PreservesColimitsOfSize.{0, 0} (levelSmash X) :=
  (levelSmashMappingSpaceAdjunction X).leftAdjoint_preservesColimits

instance (X : SymmetricSpectrum) : PreservesColimitsOfSize.{0, 0} (levelSmashBifunctor.obj X) :=
  (levelSmashMappingSpaceAdjunction X).leftAdjoint_preservesColimits

instance (K : PointedSSet.{0}) : PreservesColimitsOfSize.{0, 0} (levelSmashRight K) :=
  (levelSmashCotensorAdjunction K).leftAdjoint_preservesColimits

instance (K : PointedSSet.{0}) :
    PreservesColimitsOfSize.{0, 0} (levelSmashBifunctor.flip.obj K) :=
  (levelSmashCotensorAdjunction K).leftAdjoint_preservesColimits

instance (X : SymmetricSpectrum) :
    PreservesLimitsOfSize.{0, 0} (mappingSpace X) :=
  (levelSmashMappingSpaceAdjunction X).rightAdjoint_preservesLimits

instance (X : SymmetricSpectrumᵒᵖ) :
    PreservesLimitsOfSize.{0, 0} (mappingSpaceBifunctor.obj X) :=
  (levelSmashMappingSpaceAdjunction X.unop).rightAdjoint_preservesLimits

instance (Y : SymmetricSpectrum) (J : Type) [Category.{0} J] :
    PreservesLimitsOfShape J (mappingSpaceBifunctor.flip.obj Y) :=
  levelSmashMappingSpaceAdjunction₂.preservesLimitsOfShape_flip_obj J Y

instance (K : PointedSSet.{0}) :
    PreservesLimitsOfSize.{0, 0} (cotensor K) :=
  (levelSmashCotensorAdjunction K).rightAdjoint_preservesLimits

instance (K : PointedSSet.{0}ᵒᵖ) :
    PreservesLimitsOfSize.{0, 0} (cotensorBifunctor.obj K) :=
  (levelSmashCotensorAdjunction K.unop).rightAdjoint_preservesLimits

instance (E : SymmetricSpectrum) (J : Type) [Category.{0} J] :
    PreservesLimitsOfShape J (cotensorBifunctor.flip.obj E) :=
  have : ∀ X : SymmetricSpectrum,
      PreservesColimitsOfShape Jᵒᵖ (levelSmashBifunctor.flip.flip.obj X) :=
    fun X ↦ (levelSmashMappingSpaceAdjunction X).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  levelSmashCotensorAdjunction₂.preservesLimitsOfShape_flip_obj J E

instance (K : SSet.{0}) : PreservesColimitsOfSize.{0, 0} (simplicialTensor.obj K) :=
  (simplicialTensorCotensorAdjunction K).leftAdjoint_preservesColimits

instance (X : SymmetricSpectrum) : PreservesColimitsOfSize.{0, 0} (simplicialTensor.flip.obj X) :=
  (simplicialTensorMappingSpaceAdjunction X).leftAdjoint_preservesColimits

instance (K : SSet.{0}ᵒᵖ) : PreservesLimitsOfSize.{0, 0} (simplicialCotensor.obj K) :=
  (simplicialTensorCotensorAdjunction K.unop).rightAdjoint_preservesLimits

instance (E : SymmetricSpectrum) (J : Type) [Category.{0} J] :
    PreservesLimitsOfShape J (simplicialCotensor.flip.obj E) :=
  simplicialTensorCotensorAdjunction₂.preservesLimitsOfShape_flip_obj J E

instance (X : SymmetricSpectrumᵒᵖ) :
    PreservesLimitsOfSize.{0, 0} (simplicialMappingSpace.obj X) :=
  (simplicialTensorMappingSpaceAdjunction X.unop).rightAdjoint_preservesLimits

instance (Y : SymmetricSpectrum) (J : Type) [Category.{0} J] :
    PreservesLimitsOfShape J (simplicialMappingSpace.flip.obj Y) :=
  have : ∀ K : SSet.{0}, PreservesColimitsOfShape Jᵒᵖ (simplicialTensor.flip.flip.obj K) :=
    fun K ↦ (simplicialTensorCotensorAdjunction K).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  simplicialTensorMappingSpaceAdjunction₂.preservesLimitsOfShape_flip_obj J Y

end TauCeti.SymmetricSpectrum
