/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Descent of finite presentation along a covering family

If the restrictions of a sheaf of modules to the members of a cover are finitely presented, then
the original sheaf is finitely presented. Mathlib's `SheafOfModules.QuasicoherentData.bind`
assembles local presentations; the
generators and relations of each assembled presentation have the same finite index types as the
corresponding local presentation. This supplies a descent criterion used for finite locally free
sheaves, whose defining condition includes finite presentation.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Shrinking the index type of a finite local presentation retains finiteness of its
generators and relations. -/
instance _root_.SheafOfModules.QuasicoherentData.isFinitePresentation_shrink
    {M : _root_.SheafOfModules.{u} R} (q : M.QuasicoherentData)
    [q.IsFinitePresentation] : q.shrink.IsFinitePresentation where
  isFinite_presentation i := by
    -- `shrink` chooses an original covering index for each object in the range of the cover.
    change (q.presentation i.2.choose).IsFinite
    infer_instance

/-- Assembling finite local presentations along a cover gives a finite presentation on the
resulting common cover. -/
instance _root_.SheafOfModules.QuasicoherentData.isFinitePresentation_bind
    (M : _root_.SheafOfModules.{u} R) {I : Type u} (X : I → C)
    (hX : J.CoversTop X) (D : ∀ i, (M.over (X i)).QuasicoherentData)
    [∀ i, (D i).IsFinitePresentation] :
    (_root_.SheafOfModules.QuasicoherentData.bind M X hX D).IsFinitePresentation where
  isFinite_presentation i := by
    have h := _root_.SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation
      (q := D i.1) i.2
    constructor
    · constructor
      -- `bind` transports a presentation through an equivalence and an isomorphism; neither
      -- changes the generator index type.
      change Finite ((D i.1).presentation i.2).generators.I
      exact h.isFiniteType_generators.finite
    · constructor
      -- The relation index type is unchanged by the same transport.
      change Finite ((D i.1).presentation i.2).relations.I
      exact h.isFiniteType_relations.finite

omit [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A sheaf of modules is finitely presented if its restrictions to a covering family are
finitely presented. -/
theorem _root_.SheafOfModules.IsFinitePresentation.of_coversTop
    (M : _root_.SheafOfModules.{u} R) {I : Type u} (X : I → C)
    (hX : J.CoversTop X) [∀ i, (M.over (X i)).IsFinitePresentation] :
    M.IsFinitePresentation := by
  let D (i : I) : (M.over (X i)).QuasicoherentData :=
    (_root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (X i))).choose
  let _ : ∀ i, (D i).IsFinitePresentation := fun i =>
    (_root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (X i))).choose_spec
  exact ⟨(_root_.SheafOfModules.QuasicoherentData.bind M X hX D).shrink,
    inferInstance⟩

end SheafOfModules

end

end TauCeti
