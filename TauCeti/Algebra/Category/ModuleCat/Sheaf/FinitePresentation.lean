/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Biprod
public import TauCeti.CategoryTheory.ObjectProperty

/-!
# Finite presentation of sheaves of modules

A finite global presentation yields finite presentations on the trivial cover. This file also
supplies a general site-level criterion for a locally free sheaf of modules to be
finitely presented. Locally free data gives presentations with the chosen bases as generators
and no relations, so finiteness of the local bases is enough.

The main result is
`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation`. In particular, when
the site has binary products, the free sheaf of modules on a finite type is finitely presented
(`TauCeti.SheafOfModules.isFinitePresentation_free`). Finitely presented sheaves contain the
zero sheaf and are closed under binary and finite products, which are direct sums.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- A finite global presentation gives finite presentations on the trivial covering family. -/
instance Presentation.isFinitePresentation_quasicoherentData
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [Limits.HasBinaryProducts C] (P : M.Presentation) [P.IsFinite] :
    P.quasicoherentData.IsFinitePresentation where
  isFinite_presentation X := by
    dsimp only [_root_.SheafOfModules.Presentation.quasicoherentData]
    apply +allowSynthFailures _root_.SheafOfModules.Presentation.isFinite_map

/-- Locally free data with finite local bases exhibits a finitely presented sheaf.

Mathlib's presentation associated to locally free data uses the local bases as generators and
has no relations. -/
theorem _root_.SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation
    {q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M} (hfree : q.IsLocallyFreeData)
    (hfinite : q.IsFiniteType) :
    M.IsFinitePresentation := by
  let : q.IsLocallyFreeData := hfree
  refine ⟨q.quasiCoherentData, ⟨fun i ↦ ?_⟩⟩
  refine
    { isFiniteType_generators := ?_
      isFiniteType_relations := ?_ }
  · -- `quasiCoherentData` retains `q.generators i`, but the goal displays it through the
    -- generated presentation projection, for which there is no rewriting lemma.
    change (q.generators i).IsFiniteType
    exact hfinite.isFiniteType i
  · refine ⟨?_⟩
    -- Typeclass synthesis does not unfold the relation-index projection through
    -- `quasiCoherentData`, and there is no rewriting lemma exposing it as `ULift Empty`.
    change Finite (ULift Empty)
    infer_instance

/-- The free sheaf of modules on a finite type is finitely presented. -/
instance isFinitePresentation_free [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Limits.HasBinaryProducts C] (I : Type u)
    [Finite I] : (_root_.SheafOfModules.free (R := R) I).IsFinitePresentation :=
  -- Each local generating family is the image of the `I`-indexed basis of `free I`, so its index
  -- type is `I` by definition; no rewriting lemma exposes this through `localGeneratorsData`,
  -- whose generators live over a dependent covering object.
  _root_.SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation
    (q := (_root_.SheafOfModules.free.generatingSections I).localGeneratorsData)
    inferInstance ⟨fun _ ↦ ⟨inferInstanceAs (Finite I)⟩⟩

section DirectSum

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Finitely presented sheaves of modules are closed under binary products, which are direct
sums. -/
instance isClosedUnderBinaryProducts_isFinitePresentation :
    (isFinitePresentation R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ hM hN ↦ by
    let := hM
    let := hN
    exact isFinitePresentation_biprod

variable [HasBinaryProducts C]

/-- The zero sheaf of modules is finitely presented, being free on the empty type. -/
instance containsZero_isFinitePresentation : (isFinitePresentation R).ContainsZero where
  exists_zero := ⟨_, isZero_free PEmpty, isFinitePresentation_free PEmpty⟩

/-- Finitely presented sheaves of modules are closed under finite products, which are finite
direct sums. -/
instance isClosedUnderFiniteProducts_isFinitePresentation :
    (isFinitePresentation R).IsClosedUnderFiniteProducts :=
  .mk'

end DirectSum

end SheafOfModules

end

end TauCeti
