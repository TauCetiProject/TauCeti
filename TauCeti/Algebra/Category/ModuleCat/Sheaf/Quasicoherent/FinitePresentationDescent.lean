/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement

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

section Shrink

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Shrinking the covering family of finite quasicoherent data keeps each selected local
presentation, so the generators and relations of the shrunk data remain finite. -/
instance _root_.SheafOfModules.QuasicoherentData.isFinitePresentation_shrink
    {M : _root_.SheafOfModules.{u} R} (q : M.QuasicoherentData)
    [q.IsFinitePresentation] : q.shrink.IsFinitePresentation where
  isFinite_presentation i := by
    dsimp only [_root_.SheafOfModules.QuasicoherentData.shrink]
    exact _root_.SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation _

end Shrink

variable {C : Type u₁} [Category.{v} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Assembling finite local presentations along a cover gives a finite presentation on the
resulting common cover. -/
instance _root_.SheafOfModules.QuasicoherentData.isFinitePresentation_bind
    (M : _root_.SheafOfModules.{u} R) {I : Type u} (X : I → C)
    (hX : J.CoversTop X) (D : ∀ i, (M.over (X i)).QuasicoherentData)
    [∀ i, (D i).IsFinitePresentation] :
    (_root_.SheafOfModules.QuasicoherentData.bind M X hX D).IsFinitePresentation where
  -- Each assembled presentation is a local presentation mapped along an equivalence and then
  -- transported along an isomorphism; both steps preserve finiteness.
  isFinite_presentation i := by
    dsimp only [_root_.SheafOfModules.QuasicoherentData.bind]
    apply +allowSynthFailures _root_.SheafOfModules.instIsFiniteOfIsIso
    apply +allowSynthFailures _root_.SheafOfModules.Presentation.isFinite_map

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
