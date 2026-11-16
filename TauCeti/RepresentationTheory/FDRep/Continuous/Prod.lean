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

`TauCeti.ContFDRep.ofContRepresentationProdIso` compares the product on representation carriers
with the categorical biproduct, preserving the actions and allowing different carrier universes.
This module lifts the `FDRep` product–biproduct isomorphism to `ContFDRep` for use in
`contRepRing`, and records its compatibility with the forgetful functor.

This supplies the categorical comparison in the direct-sum argument adapted from
[AtiyahSinger/Analysis/EquivariantIndexOperations.lean][source] in Lean-Atiyah-Singer.

[source]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/EquivariantIndexOperations.lean
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

namespace TauCeti.ContFDRep

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- A componentwise product of continuous finite-dimensional representations is the categorical
biproduct of their objects, with the actual actions retained through universe shrinking. -/
noncomputable def ofContRepresentationProdIso
    (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
    (hπ : Continuous π) (hρ : Continuous ρ) :
    ofContRepresentation (π.prod ρ) (π.continuous_prod ρ hπ hρ) ≅
      ofContRepresentation π hπ ⊞ ofContRepresentation ρ hρ := by
  let X := ContFDRep.ofContRepresentation π hπ
  let Y := ContFDRep.ofContRepresentation ρ hρ
  let F := (FDRep.isContinuous 𝕜 G).ι
  exact F.preimageIso (
    eqToIso (ofContRepresentation_obj _ _) ≪≫
      eqToIso (congrArg FDRep.ofShrink (ContRepresentation.toRepresentation_prod π ρ)) ≪≫
      FDRep.ofShrinkProdIso π.toRepresentation ρ.toRepresentation ≪≫
      biprod.mapIso (eqToIso (ofContRepresentation_obj π hπ)).symm
        (eqToIso (ofContRepresentation_obj ρ hρ)).symm ≪≫
      (F.mapBiprod X Y).symm)

/-- Forgetting the continuous product comparison gives the finite-representation comparison,
with the named object transports and the canonical biproduct comparison. -/
@[simp]
theorem ι_mapIso_ofContRepresentationProdIso
    (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
    (hπ : Continuous π) (hρ : Continuous ρ) :
    (FDRep.isContinuous 𝕜 G).ι.mapIso (ofContRepresentationProdIso π ρ hπ hρ) =
      eqToIso (ofContRepresentation_obj (π.prod ρ) (π.continuous_prod ρ hπ hρ)) ≪≫
        eqToIso (congrArg FDRep.ofShrink (ContRepresentation.toRepresentation_prod π ρ)) ≪≫
        FDRep.ofShrinkProdIso π.toRepresentation ρ.toRepresentation ≪≫
        biprod.mapIso (eqToIso (ofContRepresentation_obj π hπ)).symm
          (eqToIso (ofContRepresentation_obj ρ hρ)).symm ≪≫
        ((FDRep.isContinuous 𝕜 G).ι.mapBiprod (ofContRepresentation π hπ)
          (ofContRepresentation ρ hρ)).symm := by
  apply Iso.ext
  simp only [Functor.mapIso_hom, ofContRepresentationProdIso,
    Functor.preimageIso_hom, Functor.map_preimage]

end TauCeti.ContFDRep
