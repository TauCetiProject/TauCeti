/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BaseChange.Algebra
public import TauCeti.Algebra.CrossedProduct.BaseChange.Restriction
public import TauCeti.Algebra.CrossedProduct.GaloisCocycle.Refinement
public import TauCeti.Algebra.BrauerGroup.TwoTorsionBaseChange
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Transfer

/-!
# Naturality of the Brauer–cohomology comparison

For a finite separable extension `L/K`, scalar extension of Brauer classes corresponds
under `brauerCohomologyEquiv` to restriction in absolute Galois cohomology. This holds
for every Brauer class, without a quaternion presentation or a normality assumption
on `L/K`. Restricting the comparison to two-torsion gives the corresponding square
for `brauer2EquivH2` with trivial mod-two coefficients.

The proof uses `BrauerGroup.exists_galoisCocycle_brauerClass_eq_with_le` to choose a
crossed-product presentation over a finite Galois field containing the image of `L`.
The restricted crossed product represents scalar extension by
`TauCeti.BrauerGroup.baseChange_crossedProductClass`, and its cohomology class is
restriction by `TauCeti.brauerCohomologyEquiv_restrict_crossedProductClass`.
The two-torsion square then follows from the defining square of `brauer2EquivH2` and
injectivity and restriction compatibility of `h2MuToUnits`.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public section

noncomputable section

universe u

namespace TauCeti

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- Scalar extension of any Brauer class corresponds to restriction under the
Brauer–cohomology comparison, for a finite separable extension embedded in `Kˢ`.
The extension need not be normal. -/
theorem brauerCohomologyEquiv_baseChange (x : BrauerGroup K) :
    brauerCohomologyEquiv L (Additive.ofMul (BrauerGroup.baseChange K L x)) =
      galoisResUnits K L σ 2 (brauerCohomologyEquiv K (Additive.ofMul x)) := by
  have : FiniteDimensional K σ.fieldRange := σ.toLinearMap.finiteDimensional_range
  obtain ⟨g, hS, hg⟩ :=
    _root_.BrauerGroup.exists_galoisCocycle_brauerClass_eq_with_le x σ.fieldRange
  let ι : L →ₐ[K] g.extension :=
    (IntermediateField.inclusion hS).comp σ.equivFieldRange.toAlgHom
  let : Algebra L g.extension := ι.toRingHom.toAlgebra
  have : IsScalarTower K L g.extension :=
    IsScalarTower.of_algebraMap_eq fun z => (ι.commutes z).symm
  have : FiniteDimensional L g.extension := FiniteDimensional.right K L g.extension
  have : IsGalois L g.extension := IsGalois.tower_top_of_isGalois K L g.extension
  have hσ (z : L) : g.extension.val (algebraMap L g.extension z) = σ z := by
    simp [RingHom.algebraMap_toAlgebra, ι]
  rw [← hg, GaloisCocycle.brauerClass_def, BrauerGroup.baseChange_crossedProductClass]
  exact brauerCohomologyEquiv_restrict_crossedProductClass σ g.extension hσ g.cocycle

/-- Scalar extension of any two-torsion Brauer class corresponds under `ι` to
restriction of its mod-two Galois cohomology class. -/
theorem brauer2EquivH2_baseChange [Invertible (2 : K)] [Invertible (2 : L)]
    (x : BrauerGroup.twoTorsion K) :
    brauer2EquivH2 L (Additive.ofMul (BrauerGroup.twoTorsionBaseChange K L x)) =
      galoisRes K L σ 2 (brauer2EquivH2 K (Additive.ofMul x)) := by
  apply h2MuToUnits_injective L
  rw [brauer2EquivH2_h2MuToUnits, h2MuToUnits_galoisRes,
    brauer2EquivH2_h2MuToUnits, BrauerGroup.coe_twoTorsionBaseChange]
  exact brauerCohomologyEquiv_baseChange σ x

end TauCeti
