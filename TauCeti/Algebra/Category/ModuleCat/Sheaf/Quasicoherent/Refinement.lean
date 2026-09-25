/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.GeneratingSections

/-!
# Refining quasi-coherent data

Quasi-coherent data for a sheaf of modules `M` consists of a covering family `X i` together with
a presentation of each restriction `M.over (X i)`. Given a second covering family `Y j` refining
the first one, meaning that each `Y j` comes with an arrow to some `X i`, restricting the
presentations along these arrows gives quasi-coherent data for `M` on the family `Y j`.

Restriction along an arrow `f : Y ⟶ X` is Mathlib's `SheafOfModules.overMap`. On a site with
pullbacks it is a left adjoint, so it maps presentations to presentations
(`SheafOfModules.Presentation.map`); `SheafOfModules.overFunctorMap` identifies the restriction of
`M.over X` with `M.over Y`.

The same restriction applies to local generators (`SheafOfModules.LocalGeneratorsData`), and it
preserves local freeness and finiteness of the generating families. Both restriction along an
arrow and the transport of the next paragraph are instances of one construction,
`SheafOfModules.GeneratingSections.mapIso`, from the lower-level generating-sections transport
module: generating sections are carried along a colimit-preserving functor by Mathlib's
`SheafOfModules.GeneratingSections.map` and then read through an isomorphism by
`SheafOfModules.GeneratingSections.equivOfIso`.

This lets two quasi-coherent sheaves be presented on a common refinement of their covers, which is
how the tensor product and the biproduct of quasi-coherent sheaves are shown to be quasi-coherent.

Restricting a presentation preserves finiteness, and it preserves presentations whose generating
morphism is an isomorphism, that is, presentations exhibiting a free sheaf. Hence refining finite
quasi-coherent data or locally free data gives data of the same kind.

## Main declarations

* `SheafOfModules.QuasicoherentData.ofRefinement`;
* `SheafOfModules.QuasicoherentData.isIso_ofRefinement_presentation_generators_π`: refinement
  preserves presentations with an invertible generating morphism;
* `SheafOfModules.LocalGeneratorsData.ofRefinement`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe w u v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

section IsIso

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}

/-- Generating sections pushed forward along an isomorphism exhibit a free sheaf if the original
ones do. -/
theorem _root_.SheafOfModules.GeneratingSections.isIso_ofEpi_π
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (σ : M.GeneratingSections) (p : M ⟶ N) [IsIso p] (h : IsIso σ.π) :
    IsIso (σ.ofEpi p).π := by
  rw [GeneratingSections.ofEpi_π]
  exact IsIso.comp_isIso' h inferInstance

/-- A presentation transported along an isomorphism has an invertible generating morphism if the
original one does. -/
theorem _root_.SheafOfModules.Presentation.isIso_ofIsIso_generators_π
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (f : M ⟶ N) [hf : IsIso f] (σ : M.Presentation) (h : IsIso σ.generators.π) :
    IsIso (σ.ofIsIso f).generators.π := by
  rw [Presentation.ofIsIso_generators]
  exact σ.generators.isIso_ofEpi_π f h

end IsIso

section Map

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R} (P : M.Presentation)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : unit S ≅ F.obj (unit R))

/-- The image of a finite presentation under a colimit-preserving functor is finite. -/
instance _root_.SheafOfModules.Presentation.isFinite_map [P.IsFinite] :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by simp only [Presentation.map_generators_I]; infer_instance⟩
  isFiniteType_relations := ⟨by simp only [Presentation.map_relations_I]; infer_instance⟩

/-- The image under a colimit-preserving functor of a presentation with an invertible generating
morphism has an invertible generating morphism. -/
theorem _root_.SheafOfModules.Presentation.isIso_map_generators_π (h : IsIso P.generators.π) :
    IsIso (P.map F η).generators.π := by
  rw [Presentation.map_π_eq]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (Functor.map_isIso F _)

end Map

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Quasi-coherent data for `M` transported to a refining covering family `Y`: each `Y i` maps to
the member `q.X (index i)` of the original cover by `map i`, and the presentation of
`M.over (Y i)` is the restriction of the presentation of `M.over (q.X (index i))` along
`map i`. -/
@[expose, simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.ofRefinement {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y)
    (index : I → q.I) (map : ∀ i, Y i ⟶ q.X (index i)) : M.QuasicoherentData where
  I := I
  X := Y
  coversTop := coversTop
  presentation i :=
    ((q.presentation (index i)).map (overMap R (map i)) (overMapUnitIso (map i)).symm).ofIsIso
      ((overFunctorMap R (map i)).hom.app M)

/-- Generating sections of `M.over X` restricted along `f : Y ⟶ X` to generating sections of
`M.over Y`: they are carried by the restriction functor `overMap R f`, which is identified with
restriction to `Y` by `overFunctorMap`. -/
def _root_.SheafOfModules.GeneratingSections.restrict {M : SheafOfModules.{u} R} {X Y : C}
    (G : (M.over X).GeneratingSections) (f : Y ⟶ X) : (M.over Y).GeneratingSections :=
  G.mapIso (overMap R f) (overMapUnitIso f).symm ((overFunctorMap R f).app M)

/-- Restricting generating sections preserves their index type. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.restrict_I {M : SheafOfModules.{u} R} {X Y : C}
    (G : (M.over X).GeneratingSections) (f : Y ⟶ X) : (G.restrict f).I = G.I :=
  GeneratingSections.mapIso_I _ _ _ _

/-- The generating morphism of restricted generating sections is obtained by mapping the original
generating morphism and then applying the comparison with restriction to `Y`, read along the
identification `restrict_I` of the index types. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.restrict_π {M : SheafOfModules.{u} R} {X Y : C}
    (G : (M.over X).GeneratingSections) (f : Y ⟶ X) :
    eqToHom (congrArg free (GeneratingSections.restrict_I G f).symm) ≫ (G.restrict f).π =
      ((mapFreeIso (overMap R f) G.I (overMapUnitIso f).symm).hom ≫
        (overMap R f).map G.π) ≫ ((overFunctorMap R f).app M).hom :=
  GeneratingSections.mapIso_π _ _ _ _

/-- Restricting generating sections preserves an invertible generating morphism. -/
instance _root_.SheafOfModules.GeneratingSections.isIso_restrict_π {M : SheafOfModules.{u} R}
    {X Y : C} (G : (M.over X).GeneratingSections) (f : Y ⟶ X) [IsIso G.π] :
    IsIso (G.restrict f).π :=
  GeneratingSections.isIso_mapIso_π _ _ _ _

/-- Restricting generating sections preserves finiteness. -/
instance _root_.SheafOfModules.GeneratingSections.isFiniteType_restrict
    {M : SheafOfModules.{u} R} {X Y : C} (G : (M.over X).GeneratingSections) (f : Y ⟶ X)
    [hG : G.IsFiniteType] : (G.restrict f).IsFiniteType :=
  GeneratingSections.isFiniteType_mapIso _ _ _ _

/-- Local generators for `M` transported to a refining covering family `Y`: each `Y i` maps to the
member `q.X (index i)` of the original cover by `map i`, and the generators of `M.over (Y i)` are
the restrictions of the generators of `M.over (q.X (index i))` along `map i`. -/
@[expose, simps I X generators]
def _root_.SheafOfModules.LocalGeneratorsData.ofRefinement {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y)
    (index : I → q.I) (map : ∀ i, Y i ⟶ q.X (index i)) : M.LocalGeneratorsData where
  I := I
  X := Y
  coversTop := coversTop
  generators i := (q.generators (index i)).restrict (map i)

/-- Restricting locally free data to a refinement gives locally free data. -/
instance {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) :
    (q.ofRefinement Y coversTop index map).IsLocallyFreeData where
  isIso _ := GeneratingSections.isIso_restrict_π _ _

/-- Restricting local generators of finite type to a refinement gives local generators of finite
type. -/
instance {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsFiniteType]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) :
    (q.ofRefinement Y coversTop index map).IsFiniteType where
  isFiniteType i := GeneratingSections.isFiniteType_restrict _ _
    (hG := LocalGeneratorsData.IsFiniteType.isFiniteType (index i))

/-- Refining quasi-coherent data preserves presentations with an invertible generating
morphism. -/
theorem _root_.SheafOfModules.QuasicoherentData.isIso_ofRefinement_presentation_generators_π
    {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) {I : Type w} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → q.I) (map : ∀ i, Y i ⟶ q.X (index i)) (i : I)
    (h : IsIso (q.presentation (index i)).generators.π) :
    IsIso ((q.ofRefinement Y coversTop index map).presentation i).generators.π := by
  rw [QuasicoherentData.ofRefinement_presentation]
  exact Presentation.isIso_ofIsIso_generators_π (hf := ((overFunctorMap R (map i)).app M).isIso_hom)
    _ _ (Presentation.isIso_map_generators_π _ _ _ h)

/-- Refining finite quasi-coherent data gives finite presentations. -/
theorem _root_.SheafOfModules.QuasicoherentData.isFinite_ofRefinement_presentation
    {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) (i : I) :
    ((q.ofRefinement Y coversTop index map).presentation i).IsFinite := by
  rw [QuasicoherentData.ofRefinement_presentation]
  -- Instance search does not find the invertibility of the component of `overFunctorMap`, so
  -- Mathlib's instance for presentations transported along an isomorphism is applied explicitly.
  exact @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _
    (((overFunctorMap R (map i)).app M).isIso_hom) _ inferInstance

/-- Refining finite quasi-coherent data gives finite quasi-coherent data. -/
instance {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) :
    (q.ofRefinement Y coversTop index map).IsFinitePresentation where
  isFinite_presentation := q.isFinite_ofRefinement_presentation Y coversTop index map

end SheafOfModules

end

end TauCeti
