/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.PrincipalUnitGroup

/-!
# Uniformizer coordinates on principal unit graded quotients of a discrete valuation ring

Let `S` be a discrete valuation ring with maximal ideal `𝔪` and residue field `κ`. At positive depth
`n + 1`, the canonical local-ring isomorphism
`TauCeti.IsLocalRing.principalUnitGradedSuccEquivMaximalIdealGraded` identifies
`Additive (U(S, n + 1) / U(S, n + 2))` with `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`. Fixing a uniformizer `ϖ` and
composing with the inverse of `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer` produces
an additive isomorphism `Additive (U(S, n + 1) / U(S, n + 2)) ≃+ κ` sending the class of
`1 + y * ϖ ^ (n + 1)` to `residue S y`.

When `ϖ' = ϖ * a` for a unit `a` of `S`, the coordinate relative to `ϖ` equals
`(residue S a) ^ (n + 1)` times the coordinate relative to `ϖ'` (equivalently, replacing `ϖ` by
`ϖ * a` multiplies the coordinate by `((residue S a) ^ (n + 1))⁻¹`).

## Main definitions

* `TauCeti.IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField`: the uniformizer
  coordinate `Additive (U(S, n + 1) / U(S, n + 2)) ≃+ ResidueField S`.

## Main results

* `TauCeti.IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField_apply`: factorization
  through `principalUnitGradedSuccEquivMaximalIdealGraded` and the inverse uniformizer map.
* `TauCeti.IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField_ofMul_mk_eq_residue`:
  if `u - 1 = y * ϖ ^ (n + 1)`, then the uniformizer coordinate of `u` is `residue S y`.
* `TauCeti.IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField_change`: uniformizer
  change-of-coordinate formula at positive depth.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

variable {S : Type*} [CommRing S] [IsDomain S] [_root_.IsDiscreteValuationRing S]

/-- At positive depth `n + 1`, fixing a uniformizer `ϖ` identifies the additive group of
`U(S, n + 1) / U(S, n + 2)` with `ResidueField S` by sending the class of `1 + y * ϖ ^ (n + 1)` to
`residue S y`. -/
noncomputable def principalUnitGradedSuccEquivResidueField (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    Additive (PrincipalUnitGraded S (n + 1)) ≃+ ResidueField S :=
  (principalUnitGradedSuccEquivMaximalIdealGraded S n).trans
    (residueFieldEquivMaximalIdealGradedOfUniformizer ϖ hϖ (n + 1)).symm.toAddEquiv

/-- Evaluating `principalUnitGradedSuccEquivResidueField` factors through the canonical
identification `U(S, n + 1) / U(S, n + 2) ≃+ 𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)` followed by the inverse of
`residueFieldEquivMaximalIdealGradedOfUniformizer`. -/
theorem principalUnitGradedSuccEquivResidueField_apply (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (x : Additive (PrincipalUnitGraded S (n + 1))) :
    principalUnitGradedSuccEquivResidueField n hϖ x =
      (residueFieldEquivMaximalIdealGradedOfUniformizer ϖ hϖ (n + 1)).symm
        (principalUnitGradedSuccEquivMaximalIdealGraded S n x) := by
  rw [principalUnitGradedSuccEquivResidueField, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply]

/-- Applying `residueFieldEquivMaximalIdealGradedOfUniformizer` to the uniformizer coordinate of
`u ∈ U(S, n + 1)` recovers the class of `u - 1` in `𝔪 ^ (n + 1) ⧸ 𝔪 ^ (n + 2)`. -/
@[simp]
theorem principalUnitGradedSuccEquivResidueField_ofMul_mk (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (u : (maximalIdeal S ^ (n + 1)).principalUnitGroup) :
    residueFieldEquivMaximalIdealGradedOfUniformizer ϖ hϖ (n + 1)
        (principalUnitGradedSuccEquivResidueField n hϖ
          (Additive.ofMul (QuotientGroup.mk u))) =
      Submodule.Quotient.mk ⟨((u : Sˣ) : S) - 1, Ideal.mem_principalUnitGroup.mp u.2⟩ := by
  rw [principalUnitGradedSuccEquivResidueField_apply,
    principalUnitGradedSuccEquivMaximalIdealGraded_ofMul_mk,
    LinearEquiv.apply_symm_apply]

/-- If `u - 1 = y * ϖ ^ (n + 1)` for `u ∈ U(S, n + 1)`, then the uniformizer coordinate of the
class of `u` in `U(S, n + 1) / U(S, n + 2)` is `residue S y`. -/
theorem principalUnitGradedSuccEquivResidueField_ofMul_mk_eq_residue (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (u : (maximalIdeal S ^ (n + 1)).principalUnitGroup) (y : S)
    (hu : ((u : Sˣ) : S) - 1 = y * ϖ ^ (n + 1)) :
    principalUnitGradedSuccEquivResidueField n hϖ
        (Additive.ofMul (QuotientGroup.mk u)) = residue S y := by
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer ϖ hϖ (n + 1)).injective
  rw [principalUnitGradedSuccEquivResidueField_ofMul_mk,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hu)

/-- When `ϖ' = ϖ * a` with `a = uniformizerChangeUnit ϖ ϖ' hϖ hϖ'`, the positive-depth
principal-unit coordinate relative to `ϖ` equals `(residue S a) ^ (n + 1)` times the coordinate
relative to `ϖ'` (equivalently, replacing `ϖ` by `ϖ * a` multiplies the coordinate by
`((residue S a) ^ (n + 1))⁻¹`). -/
theorem principalUnitGradedSuccEquivResidueField_change (n : ℕ) {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (x : Additive (PrincipalUnitGraded S (n + 1))) :
    principalUnitGradedSuccEquivResidueField n hϖ x =
      residue S (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : S) ^ (n + 1) *
        principalUnitGradedSuccEquivResidueField n hϖ' x := by
  rw [principalUnitGradedSuccEquivResidueField_apply,
    principalUnitGradedSuccEquivResidueField_apply]
  exact residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change ϖ ϖ' hϖ hϖ' (n + 1) _

end TauCeti.IsDiscreteValuationRing
