/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Discriminant
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.Golay
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic

/-!
# Binary codes in the `A₁` discriminant alphabet

The standard `A₁` discriminant module is the binary standard quadratic alphabet: both have
carrier `ZMod 2` and half-norm quadratic value `a² / 4`. The identity isometry
`TauCeti.IntegralLattice.typeAOneZModStandardIsometry` therefore transfers the binary coding
formulas to the `A₁` alphabet. A word has quadratic value one quarter of its Hamming weight, and
an additive code is isotropic exactly when every weight is divisible by four.

The extended binary Golay code is consequently a quadratic Lagrangian in the `A₁²⁴` coordinate
module. These facts concern the code itself and do not depend on a lattice glue-table row.

## Main declarations

* `TauCeti.coordinatePower_typeAStandardQuadraticModule_one_quadratic`: the quadratic value of
  a binary word in the `A₁` alphabet.
* `TauCeti.isIsotropic_coordinatePower_typeAStandardQuadraticModule_one_iff`: the divisibility
  criterion for quadratic isotropy.
* `TauCeti.BinaryGolay.isIsotropic_typeA1` and `TauCeti.BinaryGolay.isLagrangian_typeA1`: the
  Golay code in the `A₁` coordinate module.

## References

* W. Ebeling, *Lattices and Codes*, §§1.3 and 3.3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
-/

public section

namespace TauCeti

open IntegralLattice

variable {ι : Type*} [Fintype ι]

private theorem map_typeAOneZModStandardIsometry_coordinatePower
    (C : AddSubgroup ((typeAStandardQuadraticModule 1).coordinatePower ι)) :
    C.map ((typeAOneZModStandardIsometry.coordinatePower ι).toAddEquiv :
      ((typeAStandardQuadraticModule 1).coordinatePower ι) →+
        ((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower ι)) = C := by
  -- Compare the maps with their actual module carriers before simplifying their subgroup images.
  have hid : ((typeAOneZModStandardIsometry.coordinatePower ι).toAddEquiv :
      ((typeAStandardQuadraticModule 1).coordinatePower ι) →+
        ((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower ι)) =
      AddMonoidHom.id (ι → ZMod 2) := by
    ext x i
    exact (FiniteQuadraticModule.Isometry.coordinatePower_apply
      typeAOneZModStandardIsometry ι x i).trans (typeAOneZModStandardIsometry_apply (x i))
  rw [hid]
  exact C.map_id

/-- The quadratic value of a binary word in the `A₁` coordinate alphabet is a quarter of its
Hamming weight. -/
@[simp↓]
theorem coordinatePower_typeAStandardQuadraticModule_one_quadratic (x : ι → ZMod 2) :
    ((typeAStandardQuadraticModule 1).coordinatePower ι).quadratic x =
      (((hammingNorm x : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ)) := by
  have hx : typeAOneZModStandardIsometry.coordinatePower ι x = x := by
    ext i
    exact (FiniteQuadraticModule.Isometry.coordinatePower_apply
      typeAOneZModStandardIsometry ι x i).trans (typeAOneZModStandardIsometry_apply (x i))
  have h := (typeAOneZModStandardIsometry.coordinatePower ι).map_app x
  rw [hx] at h
  exact h.symm.trans (coordinatePower_zmodStandard_two_quadratic x)

/-- A binary additive code is quadratically isotropic in the `A₁` coordinate alphabet exactly
when all of its Hamming weights are divisible by four. -/
@[simp]
theorem isIsotropic_coordinatePower_typeAStandardQuadraticModule_one_iff
    (C : AdditiveCode (ZMod 2) ι) :
    ((typeAStandardQuadraticModule 1).coordinatePower ι).IsIsotropic C ↔
      ∀ x ∈ C, 4 ∣ hammingNorm x := by
  have h := FiniteQuadraticModule.Isometry.isIsotropic_map_iff
    ((typeAStandardQuadraticModule 1).coordinatePower ι)
    (typeAOneZModStandardIsometry.coordinatePower ι) C
  rw [map_typeAOneZModStandardIsometry_coordinatePower (ι := ι) C] at h
  exact h.symm.trans (isIsotropic_coordinatePower_zmodStandard_two_iff C)

namespace BinaryGolay

/-- The extended binary Golay code is quadratically isotropic in the `A₁` alphabet, through
the identity comparison with the standard binary discriminant alphabet. -/
theorem isIsotropic_typeA1 :
    ((typeAStandardQuadraticModule 1).coordinatePower (Fin 24)).IsIsotropic
      code.toAddSubgroup := by
  have h := FiniteQuadraticModule.Isometry.isIsotropic_map_iff
    ((typeAStandardQuadraticModule 1).coordinatePower (Fin 24))
    (typeAOneZModStandardIsometry.coordinatePower (Fin 24)) code.toAddSubgroup
  rw [map_typeAOneZModStandardIsometry_coordinatePower (ι := Fin 24) code.toAddSubgroup] at h
  exact h.mp isIsotropic_code

/-- The extended binary Golay code is a quadratic Lagrangian in the `A₁²⁴` coordinate module.
Its quadratic isotropy and bilinear Lagrangian property are transported from the standard binary
alphabet. -/
theorem isLagrangian_typeA1 :
    ((typeAStandardQuadraticModule 1).coordinatePower (Fin 24)).IsLagrangian
      code.toAddSubgroup := by
  have h := FiniteQuadraticModule.Isometry.isLagrangian_map_iff
    ((typeAStandardQuadraticModule 1).coordinatePower (Fin 24))
    (typeAOneZModStandardIsometry.coordinatePower (Fin 24)) code.toAddSubgroup
  rw [map_typeAOneZModStandardIsometry_coordinatePower (ι := Fin 24) code.toAddSubgroup] at h
  apply h.mp
  apply (((FiniteQuadraticModule.zmodStandard 2 even_two).coordinatePower
    (Fin 24)).isLagrangian_def code.toAddSubgroup).mpr
  exact ⟨isIsotropic_code, isLagrangian_code⟩

end BinaryGolay

end TauCeti
