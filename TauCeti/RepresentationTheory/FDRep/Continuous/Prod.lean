/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Continuous
public import TauCeti.RepresentationTheory.Continuous.Prod
public import TauCeti.RepresentationTheory.FDRep.Prod

/-!
# Concrete products as biproducts of continuous finite-dimensional representations

`ContRepresentation.nonempty_contFDRepIso_prod` compares the product on representation carriers
with the categorical biproduct, preserving the actions and allowing different carrier universes.
It uses `FDRep.ofShrinkEquiv` and Mathlib's concrete product in `Rep`.

This supplies the categorical comparison in the direct-sum argument adapted from
[AtiyahSinger/Analysis/EquivariantIndexOperations.lean][source] in Lean-Atiyah-Singer.

[source]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/EquivariantIndexOperations.lean
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

namespace ContRepresentation

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- A componentwise product of continuous finite-dimensional representations is the categorical
biproduct of their objects, with the actual actions retained through universe shrinking. -/
theorem nonempty_contFDRepIso_prod
    (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
    (hπ : Continuous π) (hρ : Continuous ρ) :
    Nonempty (ContFDRep.ofContRepresentation (π.prod ρ) (π.continuous_prod ρ hπ hρ) ≅
      ContFDRep.ofContRepresentation π hπ ⊞ ContFDRep.ofContRepresentation ρ hρ) := by
  let X := ContFDRep.ofContRepresentation π hπ
  let Y := ContFDRep.ofContRepresentation ρ hρ
  let F := (FDRep.isContinuous 𝕜 G).ι
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  obtain ⟨e⟩ := π.toRepresentation.nonempty_fdRepIso_ofShrink_prod ρ.toRepresentation
  refine ⟨F.preimageIso (?_ ≪≫ (F.mapBiprod X Y).symm)⟩
  exact eqToIso (ContFDRep.ofContRepresentation_obj _ _) ≪≫
    eqToIso (congrArg FDRep.ofShrink (ContRepresentation.toRepresentation_prod π ρ)) ≪≫
    e ≪≫
    biprod.mapIso (eqToIso (ContFDRep.ofContRepresentation_obj π hπ)).symm
      (eqToIso (ContFDRep.ofContRepresentation_obj ρ hρ)).symm

end ContRepresentation
