/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

The two-variable adjunctions and flipped limit-preservation instances use Mathlib's parametrized
adjunctions (`CategoryTheory.ParametrizedAdjunction`) by Joël Riou. All constructions here are
point-set constructions on `SymmetricSpectrum`; deriving them requires a model structure.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1.3 and 2.2.
-/

public section

universe w w'

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite
open scoped DayFunctor

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
lemma cotensorBifunctor_obj (K : PointedSSet.{0}ᵒᵖ) :
    cotensorBifunctor.obj K = cotensor K.unop :=
  rfl

@[simp]
lemma cotensorBifunctor_map_app {K L : PointedSSet.{0}ᵒᵖ} (g : K ⟶ L) (E : SymmetricSpectrum) :
    (cotensorBifunctor.map g).app E = (MonoidalClosed.pre ((free 0).map g.unop)).app E :=
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
    have h := congrArg (fun p : ihom X.unop ⟶ ihom X.unop ↦ (evaluation 0).map (p.app Y))
      (by simp only [unop_id, MonoidalClosed.pre_id] : MonoidalClosed.pre (𝟙 X).unop = 𝟙 _)
    exact h.trans ((evaluation 0).map_id _)
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
lemma mappingSpaceBifunctor_map_app {X X' : SymmetricSpectrumᵒᵖ} (f : X ⟶ X')
    (Y : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map f).app Y = (evaluation 0).map ((MonoidalClosed.pre f.unop).app Y) :=
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
    have hcur : Mod.ihomHomEquiv X _ Z ((levelSmashRight K).map f ≫ g') =
        Mod.ihomHomEquiv Y _ Z g' ≫ p.hom := by
      apply Mod.ihom_hom_ext
      rw [Mod.ihomHomEquiv_apply_comp_ihomι, Category.assoc, hp,
        Mod.ihomHomEquiv_apply_comp_ihomι_assoc, MonoidalClosed.curry_pre_app]
      simp only [Mod.comp_hom', Mod.Hom.mk'_hom]
    refine (levelSmashMappingSpaceAdjunction_homEquiv_apply X
      ((levelSmashRight K).map f ≫ g')).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ (evaluation 0).map p)
      (levelSmashMappingSpaceAdjunction_homEquiv_apply Y g').symm)
    rw [hcur, DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc]

/-- At each spectrum `X`, `levelSmashMappingSpaceAdjunction₂` specializes to
`levelSmashMappingSpaceAdjunction X`. -/
@[simp]
lemma levelSmashMappingSpaceAdjunction₂_adj (X : SymmetricSpectrum) :
    dsimp% levelSmashMappingSpaceAdjunction₂.adj X = levelSmashMappingSpaceAdjunction X :=
  (rfl)

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

/-- At each pointed simplicial set `K`, `levelSmashCotensorAdjunction₂` specializes to
`levelSmashCotensorAdjunction K`. -/
@[simp]
lemma levelSmashCotensorAdjunction₂_adj (K : PointedSSet.{0}) :
    dsimp% levelSmashCotensorAdjunction₂.adj K = levelSmashCotensorAdjunction K :=
  (rfl)

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
lemma simplicialCotensor_obj (K : SSet.{0}ᵒᵖ) :
    simplicialCotensor.obj K = cotensor (addBasepoint.obj K.unop) :=
  rfl

@[simp]
lemma simplicialCotensor_map_app {K L : SSet.{0}ᵒᵖ} (g : K ⟶ L) (E : SymmetricSpectrum) :
    (simplicialCotensor.map g).app E =
      (MonoidalClosed.pre ((free 0).map (addBasepoint.map g.unop))).app E :=
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
lemma simplicialMappingSpace_map_app {X X' : SymmetricSpectrumᵒᵖ} (f : X ⟶ X')
    (Y : SymmetricSpectrum) :
    (simplicialMappingSpace.map f).app Y =
      ((evaluation 0).map ((MonoidalClosed.pre f.unop).app Y)).right :=
  rfl

/-- For each simplicial set `K`, tensoring a symmetric spectrum with `K` is left adjoint to
cotensoring by `K`. -/
noncomputable def simplicialTensorCotensorAdjunction (K : SSet.{0}) :
    simplicialTensor.obj K ⊣ simplicialCotensor.obj (op K) :=
  levelSmashCotensorAdjunction (addBasepoint.obj K)

/-- `simplicialTensorCotensorAdjunction K` is the pointed cotensor adjunction on `K₊`. -/
lemma simplicialTensorCotensorAdjunction_def (K : SSet.{0}) :
    dsimp% simplicialTensorCotensorAdjunction K =
      levelSmashCotensorAdjunction (addBasepoint.obj K) :=
  (rfl)

/-- For each symmetric spectrum `X`, smashing `X` with `(-)₊` is left adjoint to the unpointed
mapping space `Map(X, -)`. -/
noncomputable def simplicialTensorMappingSpaceAdjunction (X : SymmetricSpectrum) :
    simplicialTensor.flip.obj X ⊣ simplicialMappingSpace.obj (op X) :=
  addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X)

/-- `simplicialTensorMappingSpaceAdjunction X` is the composite of `(-)₊ ⊣ forget` with
`levelSmashMappingSpaceAdjunction X`. -/
lemma simplicialTensorMappingSpaceAdjunction_def (X : SymmetricSpectrum) :
    simplicialTensorMappingSpaceAdjunction X =
      addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X) :=
  (rfl)

/-- The parametrized adjunction `simplicialTensor ⊣₂ simplicialCotensor`: spectrum maps
`X ∧ K₊ ⟶ Y` correspond naturally in all three variables to spectrum maps `X ⟶ Y^(K₊)`. -/
noncomputable def simplicialTensorCotensorAdjunction₂ :
    simplicialTensor ⊣₂ simplicialCotensor :=
  ParametrizedAdjunction.mk' simplicialTensorCotensorAdjunction fun {_ _} f {_} {_} g ↦
    levelSmashCotensorAdjunction₂.homEquiv_naturality_one (addBasepoint.map f) g

/-- At each simplicial set `K`, `simplicialTensorCotensorAdjunction₂` specializes to
`simplicialTensorCotensorAdjunction K`. -/
@[simp]
lemma simplicialTensorCotensorAdjunction₂_adj (K : SSet.{0}) :
    simplicialTensorCotensorAdjunction₂.adj K = simplicialTensorCotensorAdjunction K :=
  (rfl)

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

/-- At each spectrum `X`, `simplicialTensorMappingSpaceAdjunction₂` specializes to
`simplicialTensorMappingSpaceAdjunction X`. -/
@[simp]
lemma simplicialTensorMappingSpaceAdjunction₂_adj (X : SymmetricSpectrum) :
    simplicialTensorMappingSpaceAdjunction₂.adj X = simplicialTensorMappingSpaceAdjunction X :=
  (rfl)

/-! ### Hom-set equivalences and naturality -/

/-- The universal property of the simplicial tensor on symmetric spectra: maps `X ∧ K₊ ⟶ Y`
correspond to maps of simplicial sets `K ⟶ Map(X, Y)`. -/
noncomputable def simplicialTensorHomEquiv (K : SSet.{0}) (X Y : SymmetricSpectrum) :
    ((simplicialTensor.obj K).obj X ⟶ Y) ≃
      (K ⟶ ((mappingSpace X).obj Y).right) :=
  simplicialTensorMappingSpaceAdjunction₂.homEquiv

/-- The hom-set bijection of `simplicialTensorMappingSpaceAdjunction X` is
`simplicialTensorHomEquiv K X Y`. -/
@[simp]
lemma simplicialTensorMappingSpaceAdjunction_homEquiv (X : SymmetricSpectrum) (K : SSet.{0})
    (Y : SymmetricSpectrum) :
    dsimp% (simplicialTensorMappingSpaceAdjunction X).homEquiv K Y =
      simplicialTensorHomEquiv K X Y :=
  (rfl)

/-- `simplicialTensorHomEquiv` sends a spectrum map `X ∧ K₊ ⟶ Y` to its pointed adjoint
`K₊ ⟶ Map(X, Y)` restricted along `K ⟶ K₊`. -/
lemma simplicialTensorHomEquiv_apply (K : SSet.{0}) (X Y : SymmetricSpectrum)
    (f : (simplicialTensor.obj K).obj X ⟶ Y) :
    simplicialTensorHomEquiv K X Y f =
      addBasepointHomEquiv K ((mappingSpace X).obj Y)
        ((levelSmashMappingSpaceAdjunction X).homEquiv (addBasepoint.obj K) Y f) := by
  let f' : (addBasepoint ⋙ levelSmash X).obj K ⟶ Y := f
  have h := congrFun (congrFun (addBasepointForgetAdjunction.comp_homEquiv
    (levelSmashMappingSpaceAdjunction X)) K) Y
  refine (congrArg (fun e ↦ e f') h).trans ?_
  rw [Equiv.trans_apply, addBasepointForgetAdjunction_homEquiv]

/-- The inverse of `simplicialTensorHomEquiv` extends a simplicial map `K ⟶ Map(X, Y)` to a based
map `K₊ ⟶ Map(X, Y)` and takes its pointed smash-mapping adjoint. -/
lemma simplicialTensorHomEquiv_symm_apply (K : SSet.{0}) (X Y : SymmetricSpectrum)
    (g : K ⟶ ((mappingSpace X).obj Y).right) :
    (simplicialTensorHomEquiv K X Y).symm g =
      ((levelSmashMappingSpaceAdjunction X).homEquiv (addBasepoint.obj K) Y).symm
        ((addBasepointHomEquiv K ((mappingSpace X).obj Y)).symm g) := by
  have h := congrFun (congrFun (addBasepointForgetAdjunction.comp_homEquiv
    (levelSmashMappingSpaceAdjunction X)) K) Y
  refine (congrArg (fun e ↦ e.symm g) h).trans ?_
  rw [Equiv.symm_trans_apply, addBasepointForgetAdjunction_homEquiv]

/-- The universal property of the simplicial cotensor on symmetric spectra: maps `X ⟶ Y^(K₊)`
correspond to maps of simplicial sets `K ⟶ Map(X, Y)`. -/
noncomputable def homSimplicialCotensorEquiv (K : SSet.{0}) (X Y : SymmetricSpectrum) :
    (X ⟶ (simplicialCotensor.obj (op K)).obj Y) ≃
      (K ⟶ ((mappingSpace X).obj Y).right) :=
  simplicialTensorCotensorAdjunction₂.homEquiv.symm.trans (simplicialTensorHomEquiv K X Y)

/-- `homSimplicialCotensorEquiv` uncurries a spectrum map `X ⟶ Y^(K₊)` to `X ∧ K₊ ⟶ Y` and applies
`simplicialTensorHomEquiv`. -/
lemma homSimplicialCotensorEquiv_apply (K : SSet.{0}) (X Y : SymmetricSpectrum)
    (f : X ⟶ (simplicialCotensor.obj (op K)).obj Y) :
    homSimplicialCotensorEquiv K X Y f =
      simplicialTensorHomEquiv K X Y
        (((levelSmashCotensorAdjunction (addBasepoint.obj K)).homEquiv X Y).symm f) :=
  (rfl)

/-- The inverse of `homSimplicialCotensorEquiv` sends `K ⟶ Map(X, Y)` to `X ∧ K₊ ⟶ Y` via
`(simplicialTensorHomEquiv K X Y).symm` and curries into `Y^(K₊)`. -/
lemma homSimplicialCotensorEquiv_symm_apply (K : SSet.{0}) (X Y : SymmetricSpectrum)
    (g : K ⟶ ((mappingSpace X).obj Y).right) :
    (homSimplicialCotensorEquiv K X Y).symm g =
      (levelSmashCotensorAdjunction (addBasepoint.obj K)).homEquiv X Y
        ((simplicialTensorHomEquiv K X Y).symm g) :=
  (rfl)

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

/-! ### Adjointness and limit preservation in each variable -/

instance (X : SymmetricSpectrum) : (levelSmashBifunctor.obj X).IsLeftAdjoint :=
  (levelSmashMappingSpaceAdjunction X).isLeftAdjoint

instance (K : PointedSSet.{0}) : (levelSmashBifunctor.flip.obj K).IsLeftAdjoint :=
  (levelSmashCotensorAdjunction K).isLeftAdjoint

instance (X : SymmetricSpectrumᵒᵖ) : (mappingSpaceBifunctor.obj X).IsRightAdjoint :=
  (levelSmashMappingSpaceAdjunction X.unop).isRightAdjoint

/-- Fixing the target spectrum `Y`, the contravariant functor `X ↦ Map(X, Y)` sends colimits of
symmetric spectra to limits of pointed simplicial sets. -/
instance (Y : SymmetricSpectrum) :
    PreservesLimitsOfSize.{w', w} (mappingSpaceBifunctor.flip.obj Y) where
  preservesLimitsOfShape := levelSmashMappingSpaceAdjunction₂.preservesLimitsOfShape_flip_obj _ Y

instance (K : PointedSSet.{0}ᵒᵖ) : (cotensorBifunctor.obj K).IsRightAdjoint :=
  (levelSmashCotensorAdjunction K.unop).isRightAdjoint

/-- Fixing the target spectrum `E`, the contravariant functor `K ↦ E^K` sends colimits of pointed
simplicial sets to limits of symmetric spectra. -/
instance (E : SymmetricSpectrum) :
    PreservesLimitsOfSize.{w', w} (cotensorBifunctor.flip.obj E) where
  preservesLimitsOfShape {J} _ :=
    have : ∀ X : SymmetricSpectrum,
        PreservesColimitsOfShape Jᵒᵖ (levelSmashBifunctor.flip.flip.obj X) :=
      fun X ↦ inferInstanceAs (PreservesColimitsOfShape Jᵒᵖ (levelSmashBifunctor.obj X))
    levelSmashCotensorAdjunction₂.preservesLimitsOfShape_flip_obj J E

instance (K : SSet.{0}) : (simplicialTensor.obj K).IsLeftAdjoint :=
  (simplicialTensorCotensorAdjunction K).isLeftAdjoint

instance (X : SymmetricSpectrum) : (simplicialTensor.flip.obj X).IsLeftAdjoint :=
  (simplicialTensorMappingSpaceAdjunction X).isLeftAdjoint

instance (K : SSet.{0}ᵒᵖ) : (simplicialCotensor.obj K).IsRightAdjoint :=
  (simplicialTensorCotensorAdjunction K.unop).isRightAdjoint

/-- Fixing the target spectrum `E`, the contravariant functor `K ↦ E^(K₊)` sends colimits of
simplicial sets to limits of symmetric spectra. -/
instance (E : SymmetricSpectrum) :
    PreservesLimitsOfSize.{w', w} (simplicialCotensor.flip.obj E) where
  preservesLimitsOfShape := simplicialTensorCotensorAdjunction₂.preservesLimitsOfShape_flip_obj _ E

instance (X : SymmetricSpectrumᵒᵖ) : (simplicialMappingSpace.obj X).IsRightAdjoint :=
  (simplicialTensorMappingSpaceAdjunction X.unop).isRightAdjoint

/-- Fixing the target spectrum `Y`, the contravariant functor `X ↦ Map(X, Y)` sends colimits of
symmetric spectra to limits of simplicial sets. -/
instance (Y : SymmetricSpectrum) :
    PreservesLimitsOfSize.{w', w} (simplicialMappingSpace.flip.obj Y) where
  preservesLimitsOfShape {J} _ :=
    have : ∀ K : SSet.{0}, PreservesColimitsOfShape Jᵒᵖ (simplicialTensor.flip.flip.obj K) :=
      fun K ↦ inferInstanceAs (PreservesColimitsOfShape Jᵒᵖ (simplicialTensor.obj K))
    simplicialTensorMappingSpaceAdjunction₂.preservesLimitsOfShape_flip_obj J Y

end TauCeti.SymmetricSpectrum
