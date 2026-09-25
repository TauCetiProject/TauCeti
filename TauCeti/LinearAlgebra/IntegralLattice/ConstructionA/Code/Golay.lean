/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Golay
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.OrthogonalQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.Quadratic

/-!
# The Golay code as discriminant glue for Construction A

The extended binary Golay code is a quadratic-isotropic subgroup of the discriminant group of
the zero-code lattice `2 ℤ²⁴`. Gluing that subgroup gives the same integral lattice, in the same
rational ambient space, as Construction A applied directly to the code. Its self-duality makes
the code Lagrangian in the coordinate discriminant module, so its orthogonal quotient is trivial.

This identifies the code and lattice descriptions of the Golay construction through the actual
discriminant subgroup, with no choice of an abstract lattice isomorphism. The final discriminant
modules of the named lattice are also compared, by both bilinear and quadratic isometries, with
the actual orthogonal quotients of the Golay code; those quotients are trivial.

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
@[simp]
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

/-- The Golay code is Lagrangian in the binary coordinate discriminant module. -/
theorem isLagrangian_code :
    ((FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)).IsLagrangian
      code.toAddSubgroup :=
  (isLagrangian_coordinatePower_zmodStandard_iff 2 code.toAddSubgroup).mpr
    toZModSubmodule_code_eq_euclideanDual

/-- The orthogonal quotient of the Golay code in the binary coordinate discriminant module has
one element: the code is its own Euclidean dual. -/
theorem natCard_orthogonalQuotient_code_eq_one :
    Nat.card (((FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)).orthogonalQuotient
      code.toAddSubgroup) = 1 := by
  let A := (FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)
  have hiso : A.IsIsotropic code.toAddSubgroup :=
    (A.isIsotropic_iff_le_orthogonalComplement code.toAddSubgroup).mpr
      ((A.isLagrangian_def code.toAddSubgroup).mp isLagrangian_code).le
  exact (A.card_orthogonalQuotient_eq_one_iff_isLagrangian hiso).mpr isLagrangian_code

/-- The binary coordinate discriminant form is quadratically isotropic on the Golay code. -/
theorem isIsotropic_code :
    ((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower (Fin 24)).IsIsotropic
      code.toAddSubgroup :=
  (isIsotropic_coordinatePower_zmodStandard_two_iff_isDoublyEven code).mpr isDoublyEven_code

/-- The discriminant bilinear module of the Golay Construction A lattice is the actual orthogonal
quotient of its code. -/
noncomputable def discriminantBilinearOrthogonalQuotientIsometry :
    FiniteBilinearModule.Isometry constructionALattice.discriminantBilinearModule
      (((FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)).orthogonalQuotient
        code.toAddSubgroup) := by
  let hC := toZModSubmodule_code_eq_euclideanDual.le
  letI : (ConstructionA.integralLattice 2 code.toAddSubgroup hC).IsNondegenerate :=
    ConstructionA.isNondegenerate_integralLattice 2 code.toAddSubgroup hC
  have hfirst : constructionALattice.discriminantBilinearModule.Isometry
      (ConstructionA.integralLattice 2 code.toAddSubgroup hC).discriminantBilinearModule :=
    (IntegralLattice.Isometry.ofEq
      constructionALattice_eq_integralLattice).discriminantBilinearIsometry
  exact hfirst.trans
    (ConstructionA.discriminantBilinearOrthogonalQuotientIsometry 2 (Fin 24) code.toAddSubgroup hC)

/-- The discriminant quadratic module of the Golay Construction A lattice is the actual quadratic
orthogonal quotient of its code. -/
noncomputable def discriminantQuadraticOrthogonalQuotientIsometry :
    FiniteQuadraticModule.Isometry
      (constructionALattice.discriminantQuadraticModule isEven_constructionALattice)
      (((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower
        (Fin 24)).orthogonalQuotient code.toAddSubgroup isIsotropic_code) := by
  let hC := (isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual 2
    code.toAddSubgroup).mp isIsotropic_code.toFiniteBilinearModule
  letI : (ConstructionA.integralLattice 2 code.toAddSubgroup hC).IsNondegenerate :=
    ConstructionA.isNondegenerate_integralLattice 2 code.toAddSubgroup hC
  have hfirst :
      (constructionALattice.discriminantQuadraticModule isEven_constructionALattice).Isometry
        ((ConstructionA.integralLattice 2 code.toAddSubgroup hC).discriminantQuadraticModule
          ((ConstructionA.isEven_integralLattice_iff_isIsotropic 2 even_two
            code.toAddSubgroup hC).mpr isIsotropic_code)) :=
    (IntegralLattice.Isometry.ofEq
      constructionALattice_eq_integralLattice).discriminantQuadraticIsometry
      isEven_constructionALattice
  exact hfirst.trans
    (ConstructionA.discriminantOrthogonalQuotientIsometry 2 (Fin 24) even_two
      code.toAddSubgroup isIsotropic_code)

/-- The discriminant bilinear group of the Golay lattice is trivial. -/
instance subsingleton_discriminantBilinearModule :
    Subsingleton constructionALattice.discriminantBilinearModule := by
  let hC := toZModSubmodule_code_eq_euclideanDual.le
  have hU : (ConstructionA.integralLattice 2 code.toAddSubgroup hC).IsUnimodular := by
    rw [← constructionALattice_eq_integralLattice]
    exact isUnimodular_constructionALattice
  have hq : Subsingleton
      (((FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)).orthogonalQuotient
        code.toAddSubgroup) :=
    (ConstructionA.subsingleton_orthogonalQuotient_coordinatePower_zmodStandard_iff_isUnimodular
      2 (Fin 24) code.toAddSubgroup hC).mpr hU
  exact (Equiv.subsingleton_congr
    discriminantBilinearOrthogonalQuotientIsometry.toAddEquiv.toEquiv).mpr hq

/-- The discriminant bilinear group of the Golay lattice has one element. -/
theorem natCard_discriminantBilinearModule_eq_one :
    Nat.card constructionALattice.discriminantBilinearModule = 1 :=
  Nat.card_unique

/-- The discriminant quadratic group of the Golay lattice is also trivial. -/
instance subsingleton_discriminantQuadraticModule :
    Subsingleton
      (constructionALattice.discriminantQuadraticModule isEven_constructionALattice) := by
  let hC := (isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual 2
    code.toAddSubgroup).mp isIsotropic_code.toFiniteBilinearModule
  have hU : (ConstructionA.integralLattice 2 code.toAddSubgroup hC).IsUnimodular := by
    rw [← constructionALattice_eq_integralLattice]
    exact isUnimodular_constructionALattice
  let A := (FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower (Fin 24)
  have hbilin : Subsingleton (A.toFiniteBilinearModule.orthogonalQuotient code.toAddSubgroup) :=
    (ConstructionA.subsingleton_orthogonalQuotient_coordinatePower_zmodStandard_iff_isUnimodular
      2 (Fin 24) code.toAddSubgroup hC).mpr hU
  have hq : Subsingleton (A.orthogonalQuotient code.toAddSubgroup isIsotropic_code) :=
    (Equiv.subsingleton_congr
      (A.orthogonalQuotientUnderlyingEquiv code.toAddSubgroup isIsotropic_code)).mpr hbilin
  exact (Equiv.subsingleton_congr
    discriminantQuadraticOrthogonalQuotientIsometry.toAddEquiv.toEquiv).mpr hq

end TauCeti.BinaryGolay
