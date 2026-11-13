/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.InvertibleObject
public import TauCeti.RepresentationTheory.LinearCharacter.Tensor
public import TauCeti.RepresentationTheory.Symmetric.Specht.SignTranspose

/-!
# Transposing the factors of a Kronecker product of Specht modules

The **Kronecker product** of two Specht modules is their tensor product `S^μ₁ ⊗ S^μ₂` as a
representation of the one group `Sₙ`, and its **multiplicity spaces** are the spaces of
intertwiners `S^ν ⟶ S^μ₁ ⊗ S^μ₂`; their dimensions are the Kronecker coefficients.

Since `S^(μᵗ) ≅ S^μ ⊗ sgn` (`TauCeti.spechtModuleTensorSignIso`) and `sgn ⊗ sgn` is trivial, the
sign twists of two transposed factors cancel, while a single transposed factor leaves one sign
twist, which can be moved onto the output:

* `S^(μ₁ᵗ) ⊗ S^(μ₂ᵗ) ≅ S^μ₁ ⊗ S^μ₂`;
* `S^(μ₁ᵗ) ⊗ S^μ₂ ≅ (S^μ₁ ⊗ S^μ₂) ⊗ sgn`, hence
  `(S^ν ⟶ S^(μ₁ᵗ) ⊗ S^μ₂) ≃ (S^(νᵗ) ⟶ S^μ₁ ⊗ S^μ₂)`.

So the Kronecker coefficients are invariant under transposing both factors, and under transposing
one factor together with the output.  Transposing all three indices is not a symmetry: for `n ≥ 2`
the trivial module occurs once in `S^((n)) ⊗ S^((n))`, which is trivial, but the sign module does
not occur in `S^((1ⁿ)) ⊗ S^((1ⁿ)) = sgn ⊗ sgn`, which is trivial as well.

## Main definitions

* `TauCeti.kroneckerDoubleTranspose`: `S^(μ₁ᵗ) ⊗ S^(μ₂ᵗ) ≅ S^μ₁ ⊗ S^μ₂`.
* `TauCeti.kroneckerSingleTranspose`: `S^(μ₁ᵗ) ⊗ S^μ₂ ≅ (S^μ₁ ⊗ S^μ₂) ⊗ sgn`.
* `TauCeti.kroneckerHomTransposeEquiv`: the linear equivalence of multiplicity spaces
  `(S^ν ⟶ S^(μ₁ᵗ) ⊗ S^μ₂) ≃ₗ[ℚ] (S^(νᵗ) ⟶ S^μ₁ ⊗ S^μ₂)`.

## Main results

* `TauCeti.finrank_hom_spechtModule_tensor_conjugate_conjugate`: transposing both factors does
  not change a Kronecker coefficient.
* `TauCeti.finrank_hom_spechtModule_tensor_conjugate_left`: transposing one factor and the output
  does not change a Kronecker coefficient.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Theorem 8.15,
  for the sign twist `S^(μᵗ) ≅ S^μ ⊗ sgn` of a single Specht module that both symmetries are
  derived from.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4,
  Exercise 4.4, for the same sign twist.
-/

public section

open CategoryTheory MonoidalCategory Module

namespace TauCeti

variable {n : ℕ}

/-- The sign representation of `Sₙ` squares to the monoidal unit. -/
private noncomputable def signTensorSignIso :
    FDRep.ofLinearCharacter (signLinearCharacter ℚ (Fin n)) ⊗
        FDRep.ofLinearCharacter (signLinearCharacter ℚ (Fin n)) ≅
      𝟙_ (FDRep ℚ (Equiv.Perm (Fin n))) :=
  FDRep.ofLinearCharacterTensorIsoOfMulEqOne signLinearCharacter_mul_self

/-- **Transposing both factors of a Kronecker product of Specht modules gives an isomorphic
representation**: `S^(μ₁ᵗ) ⊗ S^(μ₂ᵗ) ≅ S^μ₁ ⊗ S^μ₂`, the two sign twists of
`TauCeti.spechtModuleTensorSignIso` cancelling. -/
noncomputable def kroneckerDoubleTranspose (μ₁ μ₂ : n.Partition) :
    spechtModule (R := ℚ) μ₁.conjugate ⊗ spechtModule (R := ℚ) μ₂.conjugate ≅
      spechtModule (R := ℚ) μ₁ ⊗ spechtModule (R := ℚ) μ₂ :=
  ((spechtModuleTensorSignIso μ₁).symm ⊗ᵢ (spechtModuleTensorSignIso μ₂).symm) ≪≫
    Functor.Monoidal.μIso (tensor _) (_, _) (_, _) ≪≫ whiskerLeftIso _ signTensorSignIso ≪≫ ρ_ _

/-- `TauCeti.kroneckerDoubleTranspose` untwists both factors by
`TauCeti.spechtModuleTensorSignIso`, interchanges the middle factors, and cancels
`sgn ⊗ sgn ≅ 1`. -/
theorem kroneckerDoubleTranspose_hom (μ₁ μ₂ : n.Partition) :
    (kroneckerDoubleTranspose μ₁ μ₂).hom =
      ((spechtModuleTensorSignIso μ₁).inv ⊗ₘ (spechtModuleTensorSignIso μ₂).inv) ≫
        tensorμ _ _ _ _ ≫
          _ ◁ (FDRep.ofLinearCharacterTensorIsoOfMulEqOne signLinearCharacter_mul_self).hom ≫
            (ρ_ _).hom :=
  (rfl)

/-- **Transposing one factor of a Kronecker product of Specht modules twists it by the sign**:
`S^(μ₁ᵗ) ⊗ S^μ₂ ≅ (S^μ₁ ⊗ S^μ₂) ⊗ sgn`, from `TauCeti.spechtModuleTensorSignIso` and the
braiding. -/
noncomputable def kroneckerSingleTranspose (μ₁ μ₂ : n.Partition) :
    spechtModule (R := ℚ) μ₁.conjugate ⊗ spechtModule (R := ℚ) μ₂ ≅
      (spechtModule (R := ℚ) μ₁ ⊗ spechtModule (R := ℚ) μ₂) ⊗
        FDRep.ofLinearCharacter (signLinearCharacter ℚ (Fin n)) :=
  whiskerRightIso (spechtModuleTensorSignIso μ₁).symm _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (β_ _ _) ≪≫ (α_ _ _ _).symm

/-- `TauCeti.kroneckerSingleTranspose` untwists the first factor by
`TauCeti.spechtModuleTensorSignIso` and braids the sign past the second factor. -/
theorem kroneckerSingleTranspose_hom (μ₁ μ₂ : n.Partition) :
    (kroneckerSingleTranspose μ₁ μ₂).hom =
      (spechtModuleTensorSignIso μ₁).inv ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ (β_ _ _).hom ≫
        (α_ _ _ _).inv :=
  (rfl)

/-- **The Kronecker coefficients are unchanged by transposing both factors**: the
dimension of `S^ν ⟶ S^(μ₁ᵗ) ⊗ S^(μ₂ᵗ)` is that of `S^ν ⟶ S^μ₁ ⊗ S^μ₂`. -/
theorem finrank_hom_spechtModule_tensor_conjugate_conjugate (ν μ₁ μ₂ : n.Partition) :
    finrank ℚ (spechtModule (R := ℚ) ν ⟶
        spechtModule (R := ℚ) μ₁.conjugate ⊗ spechtModule (R := ℚ) μ₂.conjugate) =
      finrank ℚ (spechtModule (R := ℚ) ν ⟶ spechtModule (R := ℚ) μ₁ ⊗ spechtModule (R := ℚ) μ₂) :=
  (Linear.homCongr ℚ (Iso.refl _) (kroneckerDoubleTranspose μ₁ μ₂)).finrank_eq

/-- **Transposing one factor and the output identifies the Kronecker multiplicity spaces**:
`(S^ν ⟶ S^(μ₁ᵗ) ⊗ S^μ₂) ≃ₗ[ℚ] (S^(νᵗ) ⟶ S^μ₁ ⊗ S^μ₂)`.  An intertwiner `f` is sent to its sign
twist `f ▷ sgn`, read through `TauCeti.kroneckerSingleTranspose`, `sgn ⊗ sgn ≅ 1` and
`S^(νᵗ) ≅ S^ν ⊗ sgn` (see `TauCeti.kroneckerHomTransposeEquiv_apply`). -/
noncomputable def kroneckerHomTransposeEquiv (ν μ₁ μ₂ : n.Partition) :
    (spechtModule (R := ℚ) ν ⟶ spechtModule (R := ℚ) μ₁.conjugate ⊗ spechtModule (R := ℚ) μ₂) ≃ₗ[ℚ]
      (spechtModule (R := ℚ) ν.conjugate ⟶
        spechtModule (R := ℚ) μ₁ ⊗ spechtModule (R := ℚ) μ₂) :=
  Linear.homCongr ℚ (Iso.refl _) (kroneckerSingleTranspose μ₁ μ₂) ≪≫ₗ
    tensorRightHomLinearEquivOfIso ℚ signTensorSignIso signTensorSignIso _ _ ≪≫ₗ
    Linear.homCongr ℚ (spechtModuleTensorSignIso ν) (Iso.refl _)

/-- **The multiplicity-space equivalence is the sign twist**: `kroneckerHomTransposeEquiv` sends
`f : S^ν ⟶ S^(μ₁ᵗ) ⊗ S^μ₂` to the composite
`S^(νᵗ) ≅ S^ν ⊗ sgn ⟶ ((S^μ₁ ⊗ S^μ₂) ⊗ sgn) ⊗ sgn ≅ S^μ₁ ⊗ S^μ₂` through `f ▷ sgn`. -/
theorem kroneckerHomTransposeEquiv_apply (ν μ₁ μ₂ : n.Partition)
    (f : spechtModule (R := ℚ) ν ⟶
      spechtModule (R := ℚ) μ₁.conjugate ⊗ spechtModule (R := ℚ) μ₂) :
    kroneckerHomTransposeEquiv ν μ₁ μ₂ f =
      (spechtModuleTensorSignIso ν).inv ≫
        (f ≫ (kroneckerSingleTranspose μ₁ μ₂).hom) ▷ _ ≫ (α_ _ _ _).hom ≫
          _ ◁ (FDRep.ofLinearCharacterTensorIsoOfMulEqOne signLinearCharacter_mul_self).hom ≫
            (ρ_ _).hom := by
  simp [kroneckerHomTransposeEquiv, Linear.homCongr_apply, tensorRightHomLinearEquivOfIso_apply,
    signTensorSignIso]

/-- The inverse of `TauCeti.kroneckerHomTransposeEquiv` sends `g : S^(νᵗ) ⟶ S^μ₁ ⊗ S^μ₂` to the
intertwiner `S^ν ⟶ (S^μ₁ ⊗ S^μ₂) ⊗ sgn` corresponding to `S^ν ⊗ sgn ≅ S^(νᵗ) ⟶ S^μ₁ ⊗ S^μ₂` under
`CategoryTheory.MonoidalCategory.tensorRightHomLinearEquivOfIso`, read back through
`TauCeti.kroneckerSingleTranspose`. -/
theorem kroneckerHomTransposeEquiv_symm_apply (ν μ₁ μ₂ : n.Partition)
    (g : spechtModule (R := ℚ) ν.conjugate ⟶
      spechtModule (R := ℚ) μ₁ ⊗ spechtModule (R := ℚ) μ₂) :
    (kroneckerHomTransposeEquiv ν μ₁ μ₂).symm g =
      (tensorRightHomLinearEquivOfIso ℚ
          (FDRep.ofLinearCharacterTensorIsoOfMulEqOne signLinearCharacter_mul_self)
          (FDRep.ofLinearCharacterTensorIsoOfMulEqOne signLinearCharacter_mul_self) _ _).symm
          ((spechtModuleTensorSignIso ν).hom ≫ g) ≫
        (kroneckerSingleTranspose μ₁ μ₂).inv := by
  simp [kroneckerHomTransposeEquiv, Linear.homCongr_symm_apply, signTensorSignIso]

/-- **The Kronecker coefficients are unchanged by transposing one factor and the output**: the
dimension of `S^ν ⟶ S^(μ₁ᵗ) ⊗ S^μ₂` is that of `S^(νᵗ) ⟶ S^μ₁ ⊗ S^μ₂`. -/
theorem finrank_hom_spechtModule_tensor_conjugate_left (ν μ₁ μ₂ : n.Partition) :
    finrank ℚ (spechtModule (R := ℚ) ν ⟶
        spechtModule (R := ℚ) μ₁.conjugate ⊗ spechtModule (R := ℚ) μ₂) =
      finrank ℚ (spechtModule (R := ℚ) ν.conjugate ⟶
        spechtModule (R := ℚ) μ₁ ⊗ spechtModule (R := ℚ) μ₂) :=
  (kroneckerHomTransposeEquiv ν μ₁ μ₂).finrank_eq

end TauCeti
