/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic

/-!
# Quadratically isotropic codes in the Construction A discriminant group

For an even modulus, the discriminant group of the zero-code Construction A lattice carries a
quadratic form.  The coordinate isometry identifies quadratic isotropy of the subgroup attached
to a code with quadratic isotropy of the code in the standard coordinate alphabet.  Consequently,
gluing the zero-code lattice along this subgroup gives exactly the existing Construction A
integral lattice, not merely an abstractly isometric copy.

This supplies the quadratic refinement of the bilinear code transport in
`TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.Basic`.

## Main declarations

* `TauCeti.ConstructionA.isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff` transports
  quadratic isotropy through the coordinate discriminant isometry.
* `TauCeti.ConstructionA.ofIsotropicSubgroup_codeInZeroLatticeDiscriminantGroup_eq_integralLattice`
  identifies quadratic gluing with the Construction A integral lattice.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, §§1.3 and 3.3.
-/

public section

namespace TauCeti.ConstructionA

variable (m : ℕ+) (ι : Type*) [Fintype ι]

/-- A code transported into the zero lattice's discriminant group is quadratically isotropic
exactly when the original code is quadratically isotropic in the standard coordinate alphabet. -/
theorem isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff
    (hm : Even (m : ℕ)) (C : AdditiveCode (ZMod m) ι) :
    ((zeroLattice m ι).discriminantQuadraticModule (isEven_zeroLattice m ι hm)).IsIsotropic
        (codeInZeroLatticeDiscriminantGroup m ι C) ↔
      ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).IsIsotropic C := by
  let e := discriminantQuadraticIsometry m ι hm
  have h := (FiniteQuadraticModule.Isometry.isIsotropic_map_iff _ e
    (C.comap e.toAddEquiv)).symm
  rw [AddSubgroup.map_comap_eq_self_of_surjective e.toAddEquiv.surjective C] at h
  convert h using 1
  apply iff_of_eq
  congr 1
  ext x
  rw [mem_codeInZeroLatticeDiscriminantGroup_iff]
  -- The quadratic-module carrier is the discriminant group definitionally, but subgroup
  -- membership does not unfold through the opaque `IsIsotropic` predicate above.
  change discriminantEquiv m ι x ∈ C ↔ e x ∈ C
  rw [discriminantQuadraticIsometry_apply]

/-- Quadratic isotropy of the transported discriminant subgroup is equivalent to evenness of
the associated Construction A integral lattice. -/
theorem isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff_isEven
    (hm : Even (m : ℕ)) (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    ((zeroLattice m ι).discriminantQuadraticModule (isEven_zeroLattice m ι hm)).IsIsotropic
        (codeInZeroLatticeDiscriminantGroup m ι C) ↔
      (integralLattice m C hC).IsEven :=
  (isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff m ι hm C).trans
    (isEven_integralLattice_iff_isIsotropic m hm C hC).symm

/-- Over the binary alphabet, the subgroup transported into the zero lattice's discriminant
quadratic module is isotropic exactly when the linear code is doubly even. -/
theorem isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_two_iff_isDoublyEven
    (C : LinearCode (ZMod 2) ι) :
    ((zeroLattice 2 ι).discriminantQuadraticModule
        (isEven_zeroLattice 2 ι even_two)).IsIsotropic
        (codeInZeroLatticeDiscriminantGroup 2 ι C.toAddSubgroup) ↔
      BinaryCode.IsDoublyEven C :=
  (isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff 2 ι even_two
    C.toAddSubgroup).trans
      (isIsotropic_coordinatePower_zmodStandard_two_iff_isDoublyEven C)

/-- Gluing the zero-code lattice along the discriminant subgroup of a quadratically isotropic
code gives its Construction A integral lattice.  Both lattices have the literal Construction A
carrier inside `ι → ℚ` and the same normalized dot-product form. -/
theorem ofIsotropicSubgroup_codeInZeroLatticeDiscriminantGroup_eq_integralLattice
    (hm : Even (m : ℕ)) (C : AdditiveCode (ZMod m) ι)
    (hC : ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).IsIsotropic C) :
    (zeroLattice m ι).ofIsotropicSubgroup (isEven_zeroLattice m ι hm)
        (codeInZeroLatticeDiscriminantGroup m ι C)
        ((isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff m ι hm C).mpr hC) =
      integralLattice m C
        ((isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual (m : ℕ) C).mp
          hC.toFiniteBilinearModule) := by
  apply IntegralLattice.ext
  · rw [IntegralLattice.ofIsotropicSubgroup_carrier, integralLattice_carrier,
      coe_intermediateCarrierOfDiscriminantSubgroup_codeInZeroLatticeDiscriminantGroup]
  · rw [IntegralLattice.ofIsotropicSubgroup_form, zeroLattice_form, integralLattice_form]

end TauCeti.ConstructionA
