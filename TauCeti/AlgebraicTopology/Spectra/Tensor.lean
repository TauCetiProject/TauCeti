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

Using the pointed smash and mapping-space bifunctors (`SymmetricSpectrum.levelSmashBifunctor`,
`SymmetricSpectrum.mappingSpaceBifunctor`) from `MappingSpace`, this file defines the pointed
cotensor bifunctor

* `SymmetricSpectrum.cotensorBifunctor : PointedSSet.{0}ᵒᵖ ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum`
  sending `(K, E)` to `E^K`,

together with the parametrized adjunction `levelSmashBifunctor.flip ⊣₂ cotensorBifunctor`.
Precomposing with the disjoint-basepoint functor `PointedSSet.addBasepoint` and forgetting
basepoints on mapping spaces yields the unpointed simplicial structure on symmetric spectra:

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

/-! ### Pointed cotensor bifunctor -/

-- The four bifunctors in this file carry `@[expose]` (matching `PointedSSet.simplicialTensor`,
-- `PointedSSet.simplicialCotensor`, `levelSmashBifunctor`, and `mappingSpaceBifunctor`) so that
-- dependently typed morphisms, adjunctions, and `PullbackObjObj`/`PushoutObjObj` corners over
-- them share carriers with `levelSmash`, `levelSmashRight`, `cotensor`, `mappingSpace`,
-- `addBasepoint`, and `forgetBasepoint` in public signatures without `eqToHom` transports.

/-- The point-set cotensor bifunctor `(K, E) ↦ E^K`, contravariant in the pointed simplicial set
`K` and covariant in the symmetric spectrum `E`. -/
@[expose]
noncomputable def cotensorBifunctor :
    PointedSSet.{0}ᵒᵖ ⥤ SymmetricSpectrum ⥤ SymmetricSpectrum :=
  (free 0).op ⋙ MonoidalClosed.internalHom

@[simp]
lemma cotensorBifunctor_obj (K : PointedSSet.{0}ᵒᵖ) :
    cotensorBifunctor.obj K = cotensor K.unop :=
  (rfl)

@[simp]
lemma cotensorBifunctor_map_app {K L : PointedSSet.{0}ᵒᵖ} (g : K ⟶ L) (E : SymmetricSpectrum) :
    (cotensorBifunctor.map g).app E = (MonoidalClosed.pre ((free 0).map g.unop)).app E :=
  (rfl)

/-- The parametrized adjunction `levelSmashBifunctor.flip ⊣₂ cotensorBifunctor`: spectrum maps
`E ∧ K ⟶ F` correspond naturally in all three variables to spectrum maps `E ⟶ F^K`. -/
noncomputable def levelSmashCotensorAdjunction₂ :
    levelSmashBifunctor.flip ⊣₂ cotensorBifunctor :=
  ParametrizedAdjunction.mk' levelSmashCotensorAdjunction fun {K L} j {E} {F} g ↦ by
    -- Unfold `levelSmashBifunctor.flip` and `cotensorBifunctor` on objects and maps.
    change (levelSmashRight L).obj E ⟶ F at g
    change (levelSmashCotensorAdjunction K).homEquiv E F ((levelSmash E).map j ≫ g) =
      (levelSmashCotensorAdjunction L).homEquiv E F g ≫
        (MonoidalClosed.pre ((free 0).map j)).app F
    rw [levelSmashCotensorAdjunction_homEquiv_apply, levelSmashCotensorAdjunction_homEquiv_apply,
      ← Mod.curry_eq_tensorHomEquiv, ← Mod.curry_eq_tensorHomEquiv]
    -- `cotensor K` (`Mod.internalHom ((free 0).obj K)`) is definitionally `ihom ((free 0).obj K)`.
    change MonoidalClosed.curry _ =
      MonoidalClosed.curry _ ≫ (MonoidalClosed.pre ((free 0).map j)).app F
    rw [MonoidalClosed.curry_pre_app]
    congr 1
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
    levelSmashCotensorAdjunction₂.adj K = levelSmashCotensorAdjunction K :=
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
  (rfl)

@[simp]
lemma simplicialTensor_map_app {K L : SSet.{0}} (g : K ⟶ L) (X : SymmetricSpectrum) :
    (simplicialTensor.map g).app X = (levelSmash X).map (addBasepoint.map g) :=
  (rfl)

@[simp]
lemma simplicialCotensor_obj (K : SSet.{0}ᵒᵖ) :
    simplicialCotensor.obj K = cotensor (addBasepoint.obj K.unop) :=
  (rfl)

@[simp]
lemma simplicialCotensor_map_app {K L : SSet.{0}ᵒᵖ} (g : K ⟶ L) (E : SymmetricSpectrum) :
    (simplicialCotensor.map g).app E =
      (MonoidalClosed.pre ((free 0).map (addBasepoint.map g.unop))).app E :=
  (rfl)

@[simp]
lemma simplicialMappingSpace_obj_obj (X : SymmetricSpectrumᵒᵖ) (Y : SymmetricSpectrum) :
    (simplicialMappingSpace.obj X).obj Y = ((mappingSpace X.unop).obj Y).right :=
  (rfl)

@[simp]
lemma simplicialMappingSpace_obj_map (X : SymmetricSpectrumᵒᵖ) {Y Y' : SymmetricSpectrum}
    (g : Y ⟶ Y') :
    (simplicialMappingSpace.obj X).map g = ((mappingSpace X.unop).map g).right :=
  (rfl)

@[simp]
lemma simplicialMappingSpace_map_app {X X' : SymmetricSpectrumᵒᵖ} (f : X ⟶ X')
    (Y : SymmetricSpectrum) :
    (simplicialMappingSpace.map f).app Y =
      ((evaluation 0).map ((MonoidalClosed.pre f.unop).app Y)).right :=
  (rfl)

/-- For each simplicial set `K`, tensoring a symmetric spectrum with `K` is left adjoint to
cotensoring by `K`. -/
noncomputable def simplicialTensorCotensorAdjunction (K : SSet.{0}) :
    simplicialTensor.obj K ⊣ simplicialCotensor.obj (op K) :=
  levelSmashCotensorAdjunction (addBasepoint.obj K)

/-- `simplicialTensorCotensorAdjunction K` is the pointed cotensor adjunction on `K₊`. -/
lemma simplicialTensorCotensorAdjunction_def (K : SSet.{0}) :
    simplicialTensorCotensorAdjunction K =
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
    -- Unfold `simplicialTensor.flip` and `mappingSpaceBifunctor` on objects and maps.
    change (addBasepoint ⋙ levelSmash Y).obj K ⟶ Z at g
    let m : (mappingSpace Y).obj Z ⟶ (mappingSpace X).obj Z :=
      (mappingSpaceBifunctor.map f.op).app Z
    change (addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X)).homEquiv K Z
      ((levelSmashRight (addBasepoint.obj K)).map f ≫ g) =
      (addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction Y)).homEquiv K Z g ≫
        forgetBasepoint.map m
    rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv, Equiv.trans_apply, Equiv.trans_apply,
      ← addBasepointForgetAdjunction.homEquiv_naturality_right]
    let g' : (levelSmashBifunctor.obj Y).obj (addBasepoint.obj K) ⟶ Z := g
    have h := levelSmashMappingSpaceAdjunction₂.homEquiv_naturality_one f g'
    rw [levelSmashMappingSpaceAdjunction₂_homEquiv_apply,
      levelSmashMappingSpaceAdjunction₂_homEquiv_apply] at h
    exact congrArg (addBasepointForgetAdjunction.homEquiv K _) h

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
  -- `(simplicialTensor.obj K).obj X` unfolds to `(addBasepoint ⋙ levelSmash X).obj K`.
  change (addBasepoint ⋙ levelSmash X).obj K ⟶ Y at f
  change (addBasepointForgetAdjunction.comp (levelSmashMappingSpaceAdjunction X)).homEquiv K Y f =
    _
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, addBasepointForgetAdjunction_homEquiv]

/-- The inverse of `simplicialTensorHomEquiv` extends a simplicial map `K ⟶ Map(X, Y)` to a based
map `K₊ ⟶ Map(X, Y)` and takes its pointed smash-mapping adjoint. -/
lemma simplicialTensorHomEquiv_symm_apply (K : SSet.{0}) (X Y : SymmetricSpectrum)
    (g : K ⟶ ((mappingSpace X).obj Y).right) :
    (simplicialTensorHomEquiv K X Y).symm g =
      ((levelSmashMappingSpaceAdjunction X).homEquiv (addBasepoint.obj K) Y).symm
        ((addBasepointHomEquiv K ((mappingSpace X).obj Y)).symm g) := by
  -- `((mappingSpace X).obj Y).right` unfolds to `(mappingSpace X ⋙ forgetBasepoint).obj Y`.
  change K ⟶ (mappingSpace X ⋙ forgetBasepoint).obj Y at g
  change ((addBasepointForgetAdjunction.comp
    (levelSmashMappingSpaceAdjunction X)).homEquiv K Y).symm g = _
  rw [Adjunction.comp_homEquiv, Equiv.symm_trans_apply, addBasepointForgetAdjunction_homEquiv]

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
