/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

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

This lets two quasi-coherent sheaves be presented on a common refinement of their covers, which is
how the tensor product of quasi-coherent sheaves is shown to be quasi-coherent.

Restricting a presentation preserves finiteness, and it preserves presentations whose generating
morphism is an isomorphism, that is, presentations exhibiting a free sheaf. Hence refining finite
quasi-coherent data or locally free data gives data of the same kind.

## Main declarations

* `SheafOfModules.QuasicoherentData.ofRefinement`;
* `SheafOfModules.QuasicoherentData.isIso_ofRefinement_presentation_generators_π`: refinement
  preserves presentations with an invertible generating morphism.
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
instance [P.IsFinite] : (P.map F η).IsFinite where
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
