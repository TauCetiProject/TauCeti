/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Finite presentation of locally free sheaves

This file supplies a general site-level criterion for a locally free sheaf of modules to be
finitely presented. Locally free data gives presentations with the chosen bases as generators
and no relations, so finiteness of the local bases is enough.

The main result is `SheafOfModules.LocalGeneratorsData.isFinitePresentation`. In particular, when
the site has binary products, the free sheaf of modules on a finite type is finitely presented
(`TauCeti.SheafOfModules.isFinitePresentation_free`).

The presentations used are those of Mathlib's
`SheafOfModules.LocalGeneratorsData.quasiCoherentData`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- Locally free data with finite local bases exhibits a finitely presented sheaf.

Mathlib's presentation associated to locally free data uses the local bases as generators and
has no relations. -/
theorem _root_.SheafOfModules.LocalGeneratorsData.isFinitePresentation
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M) [q.IsLocallyFreeData]
    [hq : q.IsFiniteType] : M.IsFinitePresentation :=
  -- The `simps` lemmas for `quasiCoherentData` identify its generators with `q.generators i` and
  -- its relation index type with `ULift Empty`, but they cannot rewrite these goals: the types
  -- depend on the covering object `q.quasiCoherentData.X i`. Both hold by definition.
  ⟨q.quasiCoherentData, ⟨fun i ↦
    { isFiniteType_generators := hq.isFiniteType i
      isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift Empty))⟩ }⟩⟩

/-- The free sheaf of modules on a finite type is finitely presented. -/
instance isFinitePresentation_free [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Limits.HasBinaryProducts C] (I : Type u)
    [Finite I] : (_root_.SheafOfModules.free (R := R) I).IsFinitePresentation :=
  -- Each local generating family is the image of the `I`-indexed basis of `free I`, so its index
  -- type is `I` by definition; no rewriting lemma exposes this through `localGeneratorsData`,
  -- whose generators live over a dependent covering object.
  (_root_.SheafOfModules.free.generatingSections I).localGeneratorsData.isFinitePresentation
    (hq := ⟨fun _ ↦ ⟨inferInstanceAs (Finite I)⟩⟩)

end SheafOfModules

end

end TauCeti
