/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.PrincipalUnitGroup

/-!
# Uniformizer coordinates on principal-unit graded pieces of a discrete valuation ring

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and residue field `κ`. Fixing a
uniformizer `π` identifies each positive-depth graded piece `U(R, n + 1) / U(R, n + 2)` of the
principal unit filtration `U(R, i) = 1 + 𝔪 ^ i` with the additive group of `κ`, sending the class
of `u` to the residue of `y` when `u - 1 = y * π ^ (n + 1)`.

Replacing `π` by `π' = π * a` scales the coordinate relative to `π'` by the residue of
`a ^ (n + 1)`. This is the pure discrete-valuation-ring counterpart of
`TauCeti/NumberTheory/LocalField/UnitFiltration/Uniformizer.lean`, requiring neither a fraction
field nor residue-field finiteness.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.principalUnitGroupGradedSuccEquivResidueField`:
  the additive equivalence `Additive (U(R, n + 1) / U(R, n + 2)) ≃+ ResidueField R` determined by a
  uniformizer `π`.

## Main results

* `TauCeti.IsDiscreteValuationRing.principalUnitGroupGradedSuccEquivResidueField_of_sub_eq`:
  explicit evaluation when `u - 1 = y * π ^ (n + 1)`.
* `TauCeti.IsDiscreteValuationRing.principalUnitGroupGradedSuccEquivResidueField_change`:
  change-of-uniformizer scaling formula.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section
noncomputable section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]

/-- The positive-depth principal-unit coordinate determined by a uniformizer `π` of a discrete
valuation ring `R`: an additive isomorphism from `U(R, n + 1) / U(R, n + 2)` to `ResidueField R`
carrying `1 + y * π ^ (n + 1)` to the residue of `y`. -/
def principalUnitGroupGradedSuccEquivResidueField (n : ℕ) (π : R) (hπ : Irreducible π) :
    Additive (PrincipalUnitGroupGraded R (n + 1)) ≃+ ResidueField R :=
  (principalUnitGroupGradedSuccEquivMaximalIdealGraded (R := R) n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative _).trans <|
      (TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).symm.toAddEquiv

/-- Multiplying the uniformizer coordinate of `u ∈ U(R, n + 1)` by `π ^ (n + 1)` recovers the
class of `u - 1` in `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`. -/
@[simp]
theorem principalUnitGroupGradedSuccEquivResidueField_ofMul_mk (n : ℕ) (π : R)
    (hπ : Irreducible π) (u : (maximalIdeal R ^ (n + 1)).principalUnitGroup) :
    TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (principalUnitGroupGradedSuccEquivResidueField n π hπ
          (Additive.ofMul (QuotientGroup.mk u))) =
      Submodule.Quotient.mk ⟨((u : Rˣ) : R) - 1, Ideal.mem_principalUnitGroup.mp u.2⟩ := by
  rw [principalUnitGroupGradedSuccEquivResidueField]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    principalUnitGroupGradedSuccEquivMaximalIdealGraded_mk]
  exact LinearEquiv.apply_symm_apply _ _

/-- If `u - 1 = y * π ^ (n + 1)` in `R`, then the uniformizer coordinate of `u` is `residue R y`. -/
theorem principalUnitGroupGradedSuccEquivResidueField_of_sub_eq
    (n : ℕ) (π : R) (hπ : Irreducible π) (u : (maximalIdeal R ^ (n + 1)).principalUnitGroup)
    (y : R) (hy : ((u : Rˣ) : R) - 1 = y * π ^ (n + 1)) :
    principalUnitGroupGradedSuccEquivResidueField n π hπ
        (Additive.ofMul (QuotientGroup.mk u)) =
      residue R y := by
  apply (TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).injective
  rw [principalUnitGroupGradedSuccEquivResidueField_ofMul_mk,
    TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hy)

/-- Replacing `π` by `π' = π * a` scales the positive-depth principal-unit coordinate relative to
`π'` by the residue of `a ^ (n + 1)`. -/
theorem principalUnitGroupGradedSuccEquivResidueField_change (n : ℕ)
    (π π' : R) (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (PrincipalUnitGroupGraded R (n + 1))) :
    principalUnitGroupGradedSuccEquivResidueField n π hπ x =
      residue R (TauCeti.uniformizerChangeUnit π π' hπ hπ' : R) ^ (n + 1) *
        principalUnitGroupGradedSuccEquivResidueField n π' hπ' x :=
  TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change π π' hπ hπ' (n + 1) _

end TauCeti.IsDiscreteValuationRing
