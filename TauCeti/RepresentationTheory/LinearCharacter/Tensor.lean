/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Character.Twist

/-!
# Tensor products of one-dimensional representations

The one-dimensional representations `FDRep.ofLinearCharacter χ` multiply like their characters:
`χ ⊗ ψ ≅ χψ` along the multiplication `k ⊗ k ≃ k`, and the trivial character is the monoidal
unit.  So a character whose square is trivial, such as the sign of a permutation, gives an object
`L` of `FDRep k G` with `L ⊗ L ≅ 𝟙_ (FDRep k G)`, and more generally a character `χ` and its
inverse give mutually inverse lines, so tensoring with `L` is then an autoequivalence
(`CategoryTheory.MonoidalCategory.tensorRightEquivalenceOfIso`).

## Main definitions

* `FDRep.ofTensorOfIso`: `χ ⊗ ψ ≅ χψ` on the unbundled lines, along `k ⊗ k ≃ k`.
* `FDRep.ofLinearCharacterTensorIso`: `χ ⊗ ψ ≅ χψ`.
* `FDRep.ofLinearCharacterTensorIsoOfMulEqOne`: `χ ⊗ ψ ≅ 𝟙_ (FDRep k G)` when `χψ = 1`.

## Main results

* `FDRep.ofLinearCharacter_one`: the trivial character is the monoidal unit.
-/

public section

namespace FDRep

open CategoryTheory MonoidalCategory

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- The multiplication `k ⊗ k ≃ k` carries the action of `χ ⊗ ψ` to that of `χψ`. -/
private theorem lid_tensor_ρ_apply (χ ψ : G →* kˣ) (g : G)
    (x : (FDRep.of (Representation.ofLinearCharacter χ) ⊗
      FDRep.of (Representation.ofLinearCharacter ψ) : FDRep k G)) :
    TensorProduct.lid k k ((FDRep.of (Representation.ofLinearCharacter χ) ⊗
        FDRep.of (Representation.ofLinearCharacter ψ)).ρ g x) =
      (FDRep.of (Representation.ofLinearCharacter (χ * ψ))).ρ g (TensorProduct.lid k k x) := by
  rw [tensor_ρ, of_ρ', of_ρ', ← Representation.tprod_apply,
    Representation.lid_ofLinearCharacter_tprod_apply]
  simp [mul_assoc]

/-- **The multiplication `k ⊗ k ≃ k` intertwines `χ ⊗ ψ` with `χψ`**, on the unbundled lines
`FDRep.of (Representation.ofLinearCharacter χ)`. -/
noncomputable def ofTensorOfIso (χ ψ : G →* kˣ) :
    FDRep.of (Representation.ofLinearCharacter χ) ⊗ FDRep.of (Representation.ofLinearCharacter ψ) ≅
      FDRep.of (Representation.ofLinearCharacter (χ * ψ)) :=
  Action.mkIso (TensorProduct.lid k k).toFGModuleCatIso fun g =>
    FGModuleCat.hom_ext (by simpa using LinearMap.ext (lid_tensor_ρ_apply χ ψ g))

/-- The linear equivalence underlying `FDRep.ofTensorOfIso` is the multiplication
`TensorProduct.lid k k`. -/
@[simp]
theorem isoToLinearEquiv_ofTensorOfIso (χ ψ : G →* kˣ) :
    isoToLinearEquiv (ofTensorOfIso χ ψ) = TensorProduct.lid k k :=
  (rfl)

-- Not `@[simp]`: `simp` rewrites the carrier in the left-hand side, so it would violate `simpNF`.
/-- `FDRep.ofTensorOfIso` multiplies the two coordinates of a pure tensor. -/
theorem ofTensorOfIso_hom_hom_hom_hom_tmul (χ ψ : G →* kˣ) (x y : k) :
    (ofTensorOfIso χ ψ).hom.hom.hom.hom (x ⊗ₜ y) = x * y :=
  (rfl)

/-- **The tensor product of two one-dimensional representations is the representation of the
product character**, along the multiplication `TensorProduct.lid k k : k ⊗ k ≃ k`. -/
noncomputable def ofLinearCharacterTensorIso (χ ψ : G →* kˣ) :
    ofLinearCharacter χ ⊗ ofLinearCharacter ψ ≅ ofLinearCharacter (χ * ψ) :=
  (eqToIso (ofLinearCharacter_def χ) ⊗ᵢ eqToIso (ofLinearCharacter_def ψ)) ≪≫
    ofTensorOfIso χ ψ ≪≫ eqToIso (ofLinearCharacter_def (χ * ψ)).symm

/-- `FDRep.ofLinearCharacterTensorIso` is `FDRep.ofTensorOfIso`, read through
`FDRep.ofLinearCharacter_def`. -/
theorem ofLinearCharacterTensorIso_def (χ ψ : G →* kˣ) :
    ofLinearCharacterTensorIso χ ψ =
      (eqToIso (ofLinearCharacter_def χ) ⊗ᵢ eqToIso (ofLinearCharacter_def ψ)) ≪≫
        ofTensorOfIso χ ψ ≪≫ eqToIso (ofLinearCharacter_def (χ * ψ)).symm :=
  (rfl)

/-- **The one-dimensional representation of the trivial character is the monoidal unit** of
`FDRep k G`; both are the line `k` with the trivial action. -/
theorem ofLinearCharacter_one : ofLinearCharacter (1 : G →* kˣ) = 𝟙_ (FDRep k G) := by
  rw [ofLinearCharacter_def, Representation.ofLinearCharacter_one]
  rfl

/-- **Two linear characters with trivial product give mutually inverse lines**:
`χ ⊗ ψ ≅ 𝟙_ (FDRep k G)` when `χ * ψ = 1`. -/
noncomputable def ofLinearCharacterTensorIsoOfMulEqOne {χ ψ : G →* kˣ} (h : χ * ψ = 1) :
    ofLinearCharacter χ ⊗ ofLinearCharacter ψ ≅ 𝟙_ (FDRep k G) :=
  ofLinearCharacterTensorIso χ ψ ≪≫ eqToIso (congrArg ofLinearCharacter h) ≪≫
    eqToIso ofLinearCharacter_one

/-- `FDRep.ofLinearCharacterTensorIsoOfMulEqOne` is `FDRep.ofLinearCharacterTensorIso` followed
by the equalities `ofLinearCharacter (χ * ψ) = ofLinearCharacter 1 = 𝟙_ (FDRep k G)`. -/
theorem ofLinearCharacterTensorIsoOfMulEqOne_def {χ ψ : G →* kˣ} (h : χ * ψ = 1) :
    ofLinearCharacterTensorIsoOfMulEqOne h =
      ofLinearCharacterTensorIso χ ψ ≪≫ eqToIso (congrArg ofLinearCharacter h) ≪≫
        eqToIso ofLinearCharacter_one :=
  (rfl)

end FDRep
