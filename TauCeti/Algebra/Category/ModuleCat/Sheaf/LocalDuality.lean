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

A finite locally free sheaf admits a cover on which its restrictions are finite free. Each
restriction therefore has an exact pairing with itself, transported from the standard pairing
on a finite free sheaf. This makes its dual-tensor comparison invertible. The pairing depends on
the chosen local basis; global duality uses the canonical internal Hom into the unit instead.
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

/-- On each finite free chart, a locally free sheaf has an exact self-pairing. This pairing is
transported from the standard basis pairing and depends on the chosen chart. -/
@[instance_reducible]
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.exactPairing
    (q : M.LocalGeneratorsData) (i : q.I)
    [IsIso (q.generators i).π] [Finite (q.generators i).I] :
    ExactPairing (M.over (q.X i)) (M.over (q.X i)) := by
  letI : ExactPairing
      (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I)
      (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I) :=
    exactPairingFree (R := R.over (q.X i)) (q.generators i).I
  exact exactPairingCongr (asIso (q.generators i).π).symm
    (asIso (q.generators i).π).symm

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasPullbacks C] in
/-- Evaluation on a finite free chart is the standard finite free pairing transported along
the inverse of its basis isomorphism. -/
@[reassoc]
theorem _root_.SheafOfModules.LocalGeneratorsData.exactPairing_evaluation
    (q : M.LocalGeneratorsData) (i : q.I)
    [IsIso (q.generators i).π] [Finite (q.generators i).I] :
    @ExactPairing.evaluation _ _ _ (M.over (q.X i)) (M.over (q.X i))
        (q.exactPairing i) =
      (M.over (q.X i)) ◁ (asIso (q.generators i).π).symm.hom ≫
        (asIso (q.generators i).π).symm.hom ▷
          (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I) ≫
        @ExactPairing.evaluation _ _ _
          (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I)
          (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I)
          (exactPairingFree (R := R.over (q.X i)) (q.generators i).I) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasPullbacks C] in
/-- Coevaluation on a finite free chart is the standard finite free coevaluation transported
along its basis isomorphism. -/
@[reassoc]
theorem _root_.SheafOfModules.LocalGeneratorsData.exactPairing_coevaluation
    (q : M.LocalGeneratorsData) (i : q.I)
    [IsIso (q.generators i).π] [Finite (q.generators i).I] :
    @ExactPairing.coevaluation _ _ _ (M.over (q.X i)) (M.over (q.X i))
        (q.exactPairing i) =
      @ExactPairing.coevaluation _ _ _
          (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I)
          (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I)
          (exactPairingFree (R := R.over (q.X i)) (q.generators i).I) ≫
        (free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I) ◁
          (asIso (q.generators i).π).symm.inv ≫
        (asIso (q.generators i).π).symm.inv ▷ (M.over (q.X i)) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasPullbacks C] in
/-- The dual-tensor comparison is invertible on every finite free chart of a finite locally
free sheaf. -/
theorem _root_.SheafOfModules.LocalGeneratorsData.isIso_dualTensorIhom
    (q : M.LocalGeneratorsData) (i : q.I)
    [IsIso (q.generators i).π] [Finite (q.generators i).I] :
    IsIso (dualTensorIhom (M.over (q.X i))) := by
  exact @isIso_dualTensorIhom_of_exactPairing _ _ _ _ _ (M.over (q.X i))
    (q.exactPairing i)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A finite locally free sheaf has a cover of finite free charts, each equipped with the local
dual-tensor comparison isomorphism. -/
theorem _root_.SheafOfModules.IsLocallyFree.exists_isIso_dualTensorIhom_on_finite_free_charts
    [M.IsLocallyFree] [M.IsFiniteType] :
    ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧ q.IsFiniteType ∧
      ∀ i : q.I, IsIso (dualTensorIhom (M.over (q.X i))) := by
  obtain ⟨q, hq, hq'⟩ :=
    _root_.SheafOfModules.IsLocallyFree.exists_isLocallyFreeData_isFiniteType M
  refine ⟨q, hq, hq', fun i ↦ ?_⟩
  exact @LocalGeneratorsData.isIso_dualTensorIhom C _ J _ _ _ _ R M q i
    (hq.isIso i) ((hq'.isFiniteType i).finite)

end SheafOfModules

end

end TauCeti
