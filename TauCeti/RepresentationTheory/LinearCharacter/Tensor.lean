/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.CharacterTwist

/-!
# Tensor products of one-dimensional representations

The one-dimensional representations `FDRep.ofLinearCharacter χ` multiply like their characters:
`χ ⊗ ψ ≅ χψ` along the multiplication `k ⊗ k ≃ k`, and the trivial character is the monoidal
unit.  So a character whose square is trivial, such as the sign of a permutation, gives an object
`L` of `FDRep k G` with `L ⊗ L ≅ 𝟙_ (FDRep k G)`, and tensoring with `L` is then an autoequivalence
(`CategoryTheory.MonoidalCategory.tensorRightEquivalenceOfIso`).

## Main definitions

* `FDRep.ofLinearCharacterTensorIso`: `χ ⊗ ψ ≅ χψ`.
* `FDRep.ofLinearCharacterOneIso`: the trivial character is the monoidal unit.
* `FDRep.ofLinearCharacterTensorIsoOfMulEqOne`: `χ ⊗ ψ ≅ 𝟙_ (FDRep k G)` when `χψ = 1`.
-/

public section

namespace FDRep

open CategoryTheory MonoidalCategory

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- The multiplication `k ⊗ k ≃ k` intertwines `χ ⊗ ψ` with `χψ`, on the unbundled lines. -/
private noncomputable def ofTensorOfIso (χ ψ : G →* kˣ) :
    FDRep.of (Representation.ofLinearCharacter χ) ⊗ FDRep.of (Representation.ofLinearCharacter ψ) ≅
      FDRep.of (Representation.ofLinearCharacter (χ * ψ)) :=
  (TensorProduct.lid k k).toFDRepIso fun g x => by
    refine (Representation.lid_ofLinearCharacter_tprod_apply χ
      (Representation.ofLinearCharacter ψ) g x).trans ?_
    simp [of_ρ', Representation.ofLinearCharacter_apply, mul_assoc]

/-- **The tensor product of two one-dimensional representations is the representation of the
product character**, along the multiplication `TensorProduct.lid k k : k ⊗ k ≃ k`. -/
noncomputable def ofLinearCharacterTensorIso (χ ψ : G →* kˣ) :
    ofLinearCharacter χ ⊗ ofLinearCharacter ψ ≅ ofLinearCharacter (χ * ψ) :=
  (eqToIso (ofLinearCharacter_def χ) ⊗ᵢ eqToIso (ofLinearCharacter_def ψ)) ≪≫
    ofTensorOfIso χ ψ ≪≫ eqToIso (ofLinearCharacter_def (χ * ψ)).symm

/-- The line of the trivial character is the monoidal unit, on the unbundled line. -/
private noncomputable def ofOneIso :
    FDRep.of (Representation.ofLinearCharacter (1 : G →* kˣ)) ≅ 𝟙_ (FDRep k G) :=
  (LinearEquiv.refl k k).toFDRepIso fun g x => by
    rw [tensorUnit_ρ, of_ρ', Representation.ofLinearCharacter_one, LinearMap.id_apply,
      Representation.trivial_apply]

/-- **The one-dimensional representation of the trivial character is the monoidal unit** of
`FDRep k G`; both are the line `k` with the trivial action. -/
noncomputable def ofLinearCharacterOneIso : ofLinearCharacter (1 : G →* kˣ) ≅ 𝟙_ (FDRep k G) :=
  eqToIso (ofLinearCharacter_def 1) ≪≫ ofOneIso

/-- **Two linear characters with trivial product give mutually inverse lines**:
`χ ⊗ ψ ≅ 𝟙_ (FDRep k G)` when `χ * ψ = 1`. -/
noncomputable def ofLinearCharacterTensorIsoOfMulEqOne {χ ψ : G →* kˣ} (h : χ * ψ = 1) :
    ofLinearCharacter χ ⊗ ofLinearCharacter ψ ≅ 𝟙_ (FDRep k G) :=
  ofLinearCharacterTensorIso χ ψ ≪≫ eqToIso (congrArg ofLinearCharacter h) ≪≫
    ofLinearCharacterOneIso

end FDRep
