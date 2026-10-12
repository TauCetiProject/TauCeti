/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import TauCeti.CategoryTheory.Monoidal.Rigid.OfClosed

/-!
# Local duality of finite locally free sheaves

A finite basis of a sheaf of modules gives an exact self-pairing, transported from the standard
pairing on a finite free sheaf, and makes its dual-tensor comparison invertible. A finite locally
free sheaf admits such bases on a cover. The pairing depends on the chosen basis; global duality
uses the canonical internal Hom into the unit instead.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}
  {M : _root_.SheafOfModules.{u} (ringCatSheaf R)}

variable [HasPullbacks C]

/-- The monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance localMonoidalCategory (X : C) : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

/-- The closed monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance localMonoidalClosed (X : C) : MonoidalClosed
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalClosed (R.over X)

/-- A finite basis gives an exact self-pairing, transported from the standard finite free pairing.
The pairing depends on the chosen basis. -/
-- This controls reducibility of the class-valued definition; it does not register an instance.
@[instance_reducible]
noncomputable def _root_.SheafOfModules.GeneratingSections.exactPairing
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] : ExactPairing M M := by
  letI : ExactPairing
      (free (R := ringCatSheaf R) σ.I) (free (R := ringCatSheaf R) σ.I) :=
    exactPairingFree (R := R) σ.I
  exact exactPairingCongr (asIso σ.π).symm (asIso σ.π).symm

omit [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasPullbacks C] in
/-- Evaluation in a finite basis is the standard finite free pairing transported along the
inverse of its basis isomorphism. -/
@[reassoc]
theorem _root_.SheafOfModules.GeneratingSections.exactPairing_evaluation
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] :
    @ExactPairing.evaluation _ _ _ M M σ.exactPairing =
      M ◁ (asIso σ.π).symm.hom ≫
        (asIso σ.π).symm.hom ▷ (free (R := ringCatSheaf R) σ.I) ≫
        @ExactPairing.evaluation _ _ _
          (free (R := ringCatSheaf R) σ.I) (free (R := ringCatSheaf R) σ.I)
          (exactPairingFree (R := R) σ.I) := by
  exact exactPairingCongr_evaluation (asIso σ.π).symm (asIso σ.π).symm

omit [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasPullbacks C] in
/-- Coevaluation in a finite basis is the standard finite free coevaluation transported along
its basis isomorphism. -/
@[reassoc]
theorem _root_.SheafOfModules.GeneratingSections.exactPairing_coevaluation
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] :
    @ExactPairing.coevaluation _ _ _ M M σ.exactPairing =
      @ExactPairing.coevaluation _ _ _
          (free (R := ringCatSheaf R) σ.I) (free (R := ringCatSheaf R) σ.I)
          (exactPairingFree (R := R) σ.I) ≫
        (free (R := ringCatSheaf R) σ.I) ◁ (asIso σ.π).symm.inv ≫
        (asIso σ.π).symm.inv ▷ M := by
  exact exactPairingCongr_coevaluation (asIso σ.π).symm (asIso σ.π).symm

omit [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasPullbacks C] in
/-- A finite basis makes the dual-tensor comparison invertible. -/
theorem _root_.SheafOfModules.GeneratingSections.isIso_dualTensorIhom
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] :
    IsIso (dualTensorIhom M) := by
  exact @isIso_dualTensorIhom_of_exactPairing _ _ _ _ _ M σ.exactPairing

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A finite locally free sheaf has a cover of finite free charts, each equipped with the local
dual-tensor comparison isomorphism. -/
theorem
    _root_.SheafOfModules.IsLocallyFree.exists_isLocallyFreeData_isFiniteType_isIso_dualTensorIhom
    [M.IsLocallyFree] [M.IsFiniteType] :
    ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧ q.IsFiniteType ∧
      ∀ i : q.I, IsIso (dualTensorIhom (M.over (q.X i))) := by
  obtain ⟨q, hq, hq'⟩ :=
    _root_.SheafOfModules.IsLocallyFree.exists_isLocallyFreeData_isFiniteType M
  refine ⟨q, hq, hq', fun i ↦ ?_⟩
  exact @GeneratingSections.isIso_dualTensorIhom _ _ _ _ _ _ (R.over (q.X i))
    (M.over (q.X i)) (q.generators i) (hq.isIso i) ((hq'.isFiniteType i).finite)

end SheafOfModules

end

end TauCeti
