/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Flasque.Resolution
public import TauCeti.Topology.Sheaves.Godement.Total

/-!
# Derived global sections via Godement totals

For a bounded-below complex of module sheaves, the totalized Godement resolution computes
derived global sections. The comparison `TauCeti.Topology.rightDerivedΓPlusIsoGodementTotalAt`
uses the augmentation and the derived sections unit on the flasque total and is natural for
maps of complexes at a common lower bound.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [HasDerivedCategory (X.Sheaf (ModuleCat.{u} R))]

local notation "Sh" => X.Sheaf (ModuleCat R)
local notation "Γ" => CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat R)
local notation "G" => godementTotalAtPlus (ModuleCat R) X

variable (b : ℤ) (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{u} R)))

private lemma isIso_Q_map_toGodementTotalAtPlus [K.obj.IsStrictlyGE b] :
    IsIso ((DerivedCategory.Plus.Q (C := Sh)).map (toGodementTotalAtPlus _ _ b K)) := by
  apply Localization.inverts _ (CochainComplex.Plus.quasiIso Sh)
  exact (CochainComplex.Plus.quasiIso_iff _ _).2
    (quasiIso_toGodementTotalAtPlus_hom _ _ b K)

variable [HasDerivedCategory (ModuleCat.{u} R)]

local notation "QΓ" => DerivedCategory.Plus.Q ⋙ Functor.rightDerivedFunctorPlus Γ
local notation "ΓQ" => Functor.mapCochainComplexPlus Γ ⋙ DerivedCategory.Plus.Q

private lemma isIso_rightDerivedFunctorPlusUnit_godementTotalAt :
    IsIso ((Γ).rightDerivedFunctorPlusUnit.app ((G b).obj K.obj)) :=
  CategoryTheory.Sheaf.isIso_rightDerivedFunctorPlusUnit_app_Γ_of_isFlasque _
    (isFlasque_godementTotalAt_obj_X (ModuleCat.{u} R) X b K.obj)

variable [K.obj.IsStrictlyGE b]

/-- The global sections of the bounded-below Godement total compute the native derived global
sections of a complex of module sheaves. The isomorphism is induced by the augmentation and
the derived sections unit on the flasque total. -/
def rightDerivedΓPlusIsoGodementTotalAt :
    (QΓ).obj K ≅ (ΓQ).obj ((G b).obj K.obj) := by
  have := isIso_Q_map_toGodementTotalAtPlus b K
  have := isIso_rightDerivedFunctorPlusUnit_godementTotalAt b K
  exact (Γ).rightDerivedFunctorPlus.mapIso
      (asIso (DerivedCategory.Plus.Q.map (toGodementTotalAtPlus _ _ b K))) ≪≫
    (asIso ((Γ).rightDerivedFunctorPlusUnit.app ((G b).obj K.obj))).symm

/-- After the derived sections unit of the Godement total, the comparison is the native
derived map of the augmentation. -/
@[reassoc (attr := simp)]
lemma rightDerivedΓPlusIsoGodementTotalAt_hom_comp_unit :
    (rightDerivedΓPlusIsoGodementTotalAt b K).hom ≫
      (Γ).rightDerivedFunctorPlusUnit.app ((G b).obj K.obj) =
    (QΓ).map (toGodementTotalAtPlus _ _ b K) := by
  have := isIso_Q_map_toGodementTotalAtPlus b K
  have := isIso_rightDerivedFunctorPlusUnit_godementTotalAt b K
  simp [rightDerivedΓPlusIsoGodementTotalAt]

/-- The derived sections comparison is natural for maps of complexes with the same chosen
lower bound. -/
@[reassoc]
lemma rightDerivedΓPlusIsoGodementTotalAt_hom_naturality
    {L : CochainComplex.Plus (X.Sheaf (ModuleCat.{u} R))} [L.obj.IsStrictlyGE b] (f : K ⟶ L) :
    (QΓ).map f ≫ (rightDerivedΓPlusIsoGodementTotalAt b L).hom =
      (rightDerivedΓPlusIsoGodementTotalAt b K).hom ≫ (ΓQ).map ((G b).map f.hom) := by
  have := isIso_rightDerivedFunctorPlusUnit_godementTotalAt b L
  apply (cancel_mono ((Γ).rightDerivedFunctorPlusUnit.app ((G b).obj L.obj))).1
  simp only [Category.assoc, rightDerivedΓPlusIsoGodementTotalAt_hom_comp_unit,
    (Γ).rightDerivedFunctorPlusUnit.naturality]
  rw [rightDerivedΓPlusIsoGodementTotalAt_hom_comp_unit_assoc]
  simpa only [Functor.map_comp, Functor.comp_map] using
    congrArg (QΓ).map (toGodementTotalAtPlus_naturality _ _ b f)

end TauCeti.Topology
