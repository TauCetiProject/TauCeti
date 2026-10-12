/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Dualizable

/-!
# Quasicoherence of internal Hom from a finite locally free sheaf

For a locally free sheaf of finite type `M` and a quasicoherent sheaf `N`, the sheaf
`𝓗om(M, N)` is quasicoherent. The target need not be of finite type. This allows the ordinary
sheaf internal Hom from a finite locally free source to restrict to quasicoherent sheaves.

The proof uses the canonical dual-tensor comparison from `TauCeti.dualTensorIhom`, the finite
local freeness of `𝓗om(M, 𝒪)` from `SheafOfModules.isFiniteLocallyFree_ihom_unit`, and closure
of quasicoherence under tensor products.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti

open _root_.SheafOfModules TauCeti.SheafOfModules

universe u

variable {C : Type u} [SmallCategory C] [HasPullbacks C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- Internal Hom from a locally free sheaf of finite type into a quasicoherent sheaf is
quasicoherent. No finiteness hypothesis is required on the target. -/
instance _root_.SheafOfModules.isQuasicoherent_ihom_of_isLocallyFree
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R))
    [M.IsLocallyFree] [M.IsFiniteType] [N.IsQuasicoherent] :
    ((ihom M).obj N).IsQuasicoherent := by
  have hdual := _root_.SheafOfModules.isFiniteLocallyFree_ihom_unit (R := R) M
  have := hdual.1
  have h : (((ihom M).obj (𝟙_ _)) ⊗ N).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_tensorObj
  exact (_root_.SheafOfModules.isQuasicoherent (ringCatSheaf R)).prop_of_iso
    (asIso ((dualTensorIhom M).app N)) h

end TauCeti
