/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Golay
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.Quadratic

/-!
# The Golay code as discriminant glue for Construction A

The extended binary Golay code is a quadratic-isotropic subgroup of the discriminant group of
the zero-code lattice `2 ℤ²⁴`. Gluing that subgroup gives the same integral lattice, in the same
rational ambient space, as Construction A applied directly to the code. Its self-duality makes
the code Lagrangian in the coordinate discriminant module, so its orthogonal quotient is trivial.

This identifies the code and lattice descriptions of the Golay construction through the actual
discriminant subgroup, with no choice of an abstract lattice isomorphism.

## References

* W. Ebeling, *Lattices and Codes*, §§1.3 and 3.3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
-/

public section

namespace TauCeti.BinaryGolay

/-- The Golay code defines a quadratic-isotropic subgroup of the discriminant group of the
zero-code lattice `2 ℤ²⁴`. -/
theorem isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule :
    ((ConstructionA.zeroLattice 2 (Fin 24)).discriminantQuadraticModule
      (ConstructionA.isEven_zeroLattice 2 (Fin 24) even_two)).IsIsotropic
      (ConstructionA.codeInZeroLatticeDiscriminantGroup 2 (Fin 24) code.toAddSubgroup) :=
  (ConstructionA.isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_two_iff_isDoublyEven
    (ι := Fin 24) code).mpr isDoublyEven_code

/-- Gluing `2 ℤ²⁴` along the Golay discriminant subgroup is literally the Golay Construction A
lattice, with its halved dot product on the rational coordinate space. -/
theorem ofIsotropicSubgroup_codeInZeroLatticeDiscriminantGroup_eq_constructionALattice :
    (ConstructionA.zeroLattice 2 (Fin 24)).ofIsotropicSubgroup
      (ConstructionA.isEven_zeroLattice 2 (Fin 24) even_two)
      (ConstructionA.codeInZeroLatticeDiscriminantGroup 2 (Fin 24) code.toAddSubgroup)
      isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule = constructionALattice := by
  have hq : ((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower
      (Fin 24)).IsIsotropic code.toAddSubgroup :=
    (isIsotropic_coordinatePower_zmodStandard_two_iff_isDoublyEven code).mpr
      isDoublyEven_code
  rw [constructionALattice_eq_integralLattice]
  exact
    (ConstructionA.ofIsotropicSubgroup_codeInZeroLatticeDiscriminantGroup_eq_integralLattice
      2 (Fin 24) even_two code.toAddSubgroup hq)

/-- The orthogonal quotient of the Golay code in the binary coordinate discriminant module has
one element: the code is its own Euclidean dual. -/
theorem natCard_orthogonalQuotient_code :
    Nat.card (((FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)).orthogonalQuotient
      code.toAddSubgroup) = 1 := by
  let A := (FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)
  have hlag : A.IsLagrangian code.toAddSubgroup :=
    (isLagrangian_coordinatePower_zmodStandard_iff 2 code.toAddSubgroup).mpr
      toZModSubmodule_code_eq_euclideanDual
  have hiso : A.IsIsotropic code.toAddSubgroup :=
    (A.isIsotropic_iff_le_orthogonalComplement code.toAddSubgroup).mpr
      ((A.isLagrangian_def code.toAddSubgroup).mp hlag).le
  exact (A.card_orthogonalQuotient_eq_one_iff_isLagrangian hiso).mpr hlag

end TauCeti.BinaryGolay
