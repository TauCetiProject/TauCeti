/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.KroneckerWeber
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Reciprocity

/-!
# Explicit geometric Weil reciprocity for `ℚ_p`

Combining geometric local Weil reciprocity
`TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv ℚ_[p]` with local Kronecker–Weber
(`TauCeti.ClassFieldTheory.padicAbsoluteGaloisGroupAbelianizationEquiv`), the inverse isomorphism
`W_{ℚ_p}^{ab} ≃ₜ* ℚ_[p]ˣ` satisfies Colmez's explicit formula:

`w ↦ p ^ (-deg w) * χ_cyc(w)`

(`TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv_symm_padic_mk`).

## Main results

* `TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv_symm_padic_mk`: explicit Colmez inverse
  reciprocity formula on `W_{ℚ_p}`.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

/-- **Explicit Colmez inverse reciprocity formula on `W_{ℚ_p}`.** Under the inverse of geometric
local reciprocity `W_{ℚ_p}^{ab} ≃ₜ* ℚ_[p]ˣ`, a Weil element `w` maps to
`p ^ (-deg w) * χ_cyc(w)`. -/
theorem localWeilGeometricArtinEquiv_symm_padic_mk (p : ℕ) [Fact p.Prime] (w : WeilGroup ℚ_[p]) :
    (localWeilGeometricArtinEquiv ℚ_[p]).symm
        (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup ℚ_[p])) =
      padicPrimeUnit p ^ (-(weilDegree ℚ_[p] w).toAdd) *
        padicIntUnitsInclusion p (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w)) := by
  apply (localWeilGeometricArtinEquiv ℚ_[p]).injective
  apply injective_weilToAbsoluteAbelianization ℚ_[p]
  apply (padicAbsoluteGaloisGroupAbelianizationEquiv p).injective
  rw [ContinuousMulEquiv.apply_symm_apply, weilToAbsoluteAbelianization_mk,
    weilToAbsoluteAbelianization_localWeilGeometricArtinEquiv,
    padicAbsoluteGaloisGroupAbelianizationEquiv_apply,
    padicAbsoluteGaloisGroupAbelianizationEquiv_geometricArtinMap,
    unramifiedCoordinate_weilDegree, abelianizedLocalCyclotomicCharacter_mk]
  let x : ℚ_[p]ˣ := padicPrimeUnit p ^ (-(weilDegree ℚ_[p] w).toAdd) *
    padicIntUnitsInclusion p (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w))
  have hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ (-(weilDegree ℚ_[p] w).toAdd) *
      ((localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, coe_padicPrimeUnit,
      coe_padicIntUnitsInclusion_apply]
  have hval : (x : ℚ_[p]).valuation = -(weilDegree ℚ_[p] w).toAdd :=
    TauCeti.Padic.valuation_eq_of_eq hx
  have hunit : padicUnitPart p x =
      localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) :=
    padicUnitPart_apply_of_eq hx
  refine Prod.ext ?_ hunit.symm
  rw [hval, neg_neg]
  conv_lhs => rw [← ofAdd_toAdd (weilDegree ℚ_[p] w), zHat.ofInt_ofAdd]

end TauCeti.ClassFieldTheory
