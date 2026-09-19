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

The main result is
`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation`. In particular the
free sheaf of modules on a finite type is finitely presented
(`TauCeti.SheafOfModules.isFinitePresentation_free`).

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, item "Coherent sheaves and
cohomology `Hⁱ(X, ℱ)`". No formalization is vendored. The proof reuses Mathlib's
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

end SheafOfModules

end

end TauCeti
