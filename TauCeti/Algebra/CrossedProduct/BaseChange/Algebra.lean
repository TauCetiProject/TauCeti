/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BrauerClass
public import TauCeti.Algebra.CrossedProduct.Restriction
public import TauCeti.Algebra.BrauerGroup.BaseChange
import TauCeti.Algebra.BrauerGroup.Centralizer

/-!
# Scalar extension of a crossed-product class

For a finite Galois extension `E/K` and an intermediate field `L`, scalar extension of
the crossed-product class of a cocycle `c` is the class of `c.restrict L`.
The existing embedding `CrossedProduct.restrictHom` identifies the restricted crossed
product with the centralizer of `L` in the original algebra. The centralizer theorem
then identifies its Brauer class with scalar extension. This supplies the algebraic
side of the restriction square for the Brauer–cohomology comparison.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public section

namespace TauCeti.BrauerGroup

universe u

variable {K L E : Type u} [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
  [FiniteDimensional K E] [IsGalois K E]

/-- Scalar extension of a crossed-product Brauer class to an intermediate field is
the class of the cocycle restricted to the automorphisms fixing that field. No
normality assumption on the intermediate field over the original base is needed. -/
@[simp]
theorem baseChange_crossedProductClass (c : TwoCocycle K E) :
    letI := FiniteDimensional.right K L E
    letI := IsGalois.tower_top_of_isGalois K L E
    baseChange K L (crossedProductClass c) = crossedProductClass (c.restrict L) := by
  let := FiniteDimensional.right K L E
  let := IsGalois.tower_top_of_isGalois K L E
  rw [crossedProductClass_def, crossedProductClass_def]
  apply baseChange_mk_eq_mk_of_range_eq_centralizer (CrossedProduct.restrictHom c)
  rw [CrossedProduct.range_restrictHom_eq_centralizer]
  congr 1
  rw [AlgHom.coe_range]
  congr 1
  funext x
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  rw [← (CrossedProduct.inc (c.restrict L)).commutes, CrossedProduct.restrictHom_inc]

end TauCeti.BrauerGroup
