/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Bilinear
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Quadratic

/-!
# The discriminant module of a Construction A lattice is `C⊥ / C`

Let `C ≤ (ℤ/m)^ι` be a self-orthogonal additive code. Inside the coordinate alphabet
`(ℤ/m)^ι`, whose pairing is `(x ⬝ᵥ y) / m`, the orthogonal complement of `C` is its Euclidean dual
`C⊥`, so the orthogonal quotient of `C` is the finite bilinear module `C⊥ / C`. This file
identifies it with the discriminant bilinear module of the Construction A lattice `P_m(C)`:

```text
A_{P_m(C)} ≅ C⊥ / C.
```

The class of an integer vector `z` of the dual lattice `P_m(C⊥)` goes to the class of its
coordinatewise reduction modulo `m`. When `m` is even and `C` is quadratically isotropic, so that
`P_m(C)` is even, the same map is an isometry of finite quadratic modules for the half-norm
convention.

The isometry is not computed afresh. The canonical coordinate isometry `A_{L₀} ≅ (ℤ/m)^ι` for the
zero-code lattice `L₀ = m ℤ^ι` carries the transported subgroup of `C` onto `C`, the overlattice
of `L₀` glued along that subgroup is literally `P_m(C)`, and the general comparison
`A_{L_H} ≅ H⊥ / H` for an overlattice glued along an isotropic subgroup `H` does the rest.

## Main declarations

* `TauCeti.ConstructionA.discriminantBilinearOrthogonalQuotientIsometry`: the isometry
  `A_{P_m(C)} ≅ C⊥ / C` of finite bilinear modules, with representative formula
  `TauCeti.ConstructionA.discriminantBilinearOrthogonalQuotientIsometry_mk_intCast`.
* `TauCeti.ConstructionA.discriminantOrthogonalQuotientIsometry`: the isometry of finite
  quadratic modules for an even modulus and a quadratically isotropic code, with representative
  formula `TauCeti.ConstructionA.discriminantOrthogonalQuotientIsometry_mk_intCast`.
* `TauCeti.ConstructionA.natCard_orthogonalQuotient_coordinatePower_zmodStandard`: the order of
  `C⊥ / C` is the discriminant of `P_m(C)`.
* `subsingleton_orthogonalQuotient_coordinatePower_zmodStandard_iff_isUnimodular`:
  `C⊥ / C` is trivial exactly when `P_m(C)` is unimodular.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1.
* W. Ebeling, *Lattices and Codes*, §§1.3 and 3.3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3, and
  Chapter 7, §§8–9.
-/

public section

namespace TauCeti.ConstructionA

variable (m : ℕ+) (ι : Type*) [Fintype ι]

/-! ## The bilinear isometry -/

/-- The discriminant class in `A_{L₀}` of an integer vector of the dual of an integral overlattice
of the zero-code lattice is its coordinatewise reduction modulo `m`. -/
private theorem discriminantEquiv_dualClassHom_of_intCast
    {M : (zeroLattice m ι).IntermediateCarrier}
    (hM : IntegralLattice.IntermediateCarrier.IsIntegral M)
    (z : ι → ℤ) (y : hM.toIntegralLattice.dualCarrier) (hy : (y : ι → ℚ) = fun i ↦ (z i : ℚ)) :
    discriminantEquiv m ι (hM.dualClassHom y) = fun i ↦ (z i : ZMod m) := by
  rw [IntegralLattice.IntermediateCarrier.IsIntegral.dualClassHom_apply]
  convert discriminantEquiv_mk_of_intCast m ι z
    ((mem_zeroLattice_dualCarrier_iff m ι).mpr ⟨z, rfl⟩) using 3
  exact Subtype.ext hy

/-- **The discriminant bilinear module of a Construction A lattice is `C⊥ / C`.** For a
self-orthogonal additive code `C` over `ℤ/m`, the discriminant bilinear module of `P_m(C)` is the
orthogonal quotient of `C` in the coordinate alphabet `(ℤ/m)^ι`. -/
noncomputable def discriminantBilinearOrthogonalQuotientIsometry (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    FiniteBilinearModule.Isometry (integralLattice m C hC).discriminantBilinearModule
      (((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).orthogonalQuotient C) :=
  (IntegralLattice.Isometry.ofEq
      (toIntegralLattice_codeInZeroLatticeDiscriminantGroup_eq_integralLattice m ι C hC).symm
    ).discriminantBilinearIsometry.trans
    (((zeroLattice m ι).discriminantBilinearOrthogonalQuotientIsometryOfSubgroup
        (isIsotropic_codeInZeroLatticeDiscriminantGroup m ι C hC)).trans
      ((discriminantIsometry m ι).orthogonalQuotientEquiv
        (by
          rw [codeInZeroLatticeDiscriminantGroup_eq_codeInZeroLatticeDiscriminantBilinearModule]
          exact map_codeInZeroLatticeDiscriminantBilinearModule m ι C)))

/-- **The representative formula.** The class in `A_{P_m(C)}` of an integer vector of the dual
lattice goes to the class in `C⊥ / C` of its coordinatewise reduction modulo `m`. -/
@[simp]
theorem discriminantBilinearOrthogonalQuotientIsometry_mk_intCast (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (z : ι → ℤ) (hz : (fun i ↦ (z i : ℚ)) ∈ (integralLattice m C hC).dualCarrier) :
    discriminantBilinearOrthogonalQuotientIsometry m ι C hC (Submodule.Quotient.mk ⟨_, hz⟩) =
      ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).orthogonalQuotientMk C
        ⟨fun i ↦ (z i : ZMod m),
          (intCast_mem_integralLattice_dualCarrier_iff m ι C hC z).mp hz⟩ := by
  rw [discriminantBilinearOrthogonalQuotientIsometry]
  refine (FiniteBilinearModule.Isometry.trans_apply _ _ _).trans ?_
  refine (FiniteBilinearModule.Isometry.trans_apply _ _ _).trans ?_
  rw [IntegralLattice.Isometry.discriminantBilinearIsometry_mk]
  rw [IntegralLattice.discriminantBilinearOrthogonalQuotientIsometryOfSubgroup_mk]
  refine (FiniteBilinearModule.Isometry.orthogonalQuotientEquiv_orthogonalQuotientMk
    _ _ _).trans (congrArg _ (Subtype.ext ?_))
  dsimp only
  rw [discriminantIsometry_apply]
  refine discriminantEquiv_dualClassHom_of_intCast m ι _ z _ ?_
  simp

/-- **The order of `C⊥ / C` is the discriminant of the Construction A lattice.** -/
theorem natCard_orthogonalQuotient_coordinatePower_zmodStandard (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    Nat.card
        (((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).orthogonalQuotient C) =
      (integralLattice m C hC).discriminant :=
  (Nat.card_congr
      (discriminantBilinearOrthogonalQuotientIsometry m ι C hC).toAddEquiv.toEquiv).symm.trans
    (integralLattice m C hC).natCard_discriminantGroup

/-- The orthogonal quotient of a self-orthogonal code is trivial exactly when its Construction A
lattice is unimodular. -/
theorem subsingleton_orthogonalQuotient_coordinatePower_zmodStandard_iff_isUnimodular
    (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    Subsingleton
        (((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).orthogonalQuotient C) ↔
      (integralLattice m C hC).IsUnimodular := by
  rw [(integralLattice m C hC).isUnimodular_iff_subsingleton_discriminantGroup]
  exact Equiv.subsingleton_congr
    (discriminantBilinearOrthogonalQuotientIsometry m ι C hC).toAddEquiv.toEquiv.symm

/-! ## The quadratic isometry for an even modulus -/

variable (hm : Even (m : ℕ))

/-- **The discriminant quadratic module of an even Construction A lattice is `C⊥ / C`.** Over an
even modulus, for a quadratically isotropic code `C`, the discriminant quadratic module of the
even lattice `P_m(C)` is the quadratic orthogonal quotient of `C` in the coordinate alphabet
`(ℤ/m)^ι`, in the half-norm convention. -/
noncomputable def discriminantOrthogonalQuotientIsometry (C : AdditiveCode (ZMod m) ι)
    (hC : ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).IsIsotropic C) :
    FiniteQuadraticModule.Isometry
      ((integralLattice m C
          ((isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual (m : ℕ) C).mp
            hC.toFiniteBilinearModule)).discriminantQuadraticModule
        ((isEven_integralLattice_iff_isIsotropic m hm C _).mpr hC))
      (((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).orthogonalQuotient
        C hC) :=
  ((IntegralLattice.Isometry.ofEq
      (toIntegralLattice_codeInZeroLatticeDiscriminantGroup_eq_integralLattice m ι C _).symm
    ).discriminantQuadraticIsometry
      ((isEven_integralLattice_iff_isIsotropic m hm C _).mpr hC)).trans
    (((zeroLattice m ι).discriminantOrthogonalQuotientIsometryOfSubgroup
        (isEven_zeroLattice m ι hm)
        ((isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff m ι hm C).mpr hC)).trans
      ((discriminantQuadraticIsometry m ι hm).orthogonalQuotientEquiv
        ((isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff m ι hm C).mpr hC)
        (by
          rw [← FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv,
            discriminantQuadraticIsometry_toFiniteBilinearModule,
            codeInZeroLatticeDiscriminantGroup_eq_codeInZeroLatticeDiscriminantBilinearModule]
          exact map_codeInZeroLatticeDiscriminantBilinearModule m ι C)))

/-- **The representative formula.** The class in the discriminant quadratic module of `P_m(C)`
of an integer vector of the dual lattice goes to the class in `C⊥ / C` of its coordinatewise
reduction modulo `m`. -/
@[simp]
theorem discriminantOrthogonalQuotientIsometry_mk_intCast (C : AdditiveCode (ZMod m) ι)
    (hC : ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).IsIsotropic C)
    (z : ι → ℤ)
    (hz : (fun i ↦ (z i : ℚ)) ∈ (integralLattice m C
      ((isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual (m : ℕ) C).mp
        hC.toFiniteBilinearModule)).dualCarrier) :
    discriminantOrthogonalQuotientIsometry m ι hm C hC (Submodule.Quotient.mk ⟨_, hz⟩) =
      ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).orthogonalQuotientMk C hC
        ⟨fun i ↦ (z i : ZMod m),
          (intCast_mem_integralLattice_dualCarrier_iff m ι C _ z).mp hz⟩ := by
  rw [discriminantOrthogonalQuotientIsometry]
  refine (FiniteQuadraticModule.Isometry.trans_apply _ _ _).trans ?_
  refine (FiniteQuadraticModule.Isometry.trans_apply _ _ _).trans ?_
  rw [IntegralLattice.Isometry.discriminantQuadraticIsometry_mk]
  rw [IntegralLattice.discriminantOrthogonalQuotientIsometryOfSubgroup_mk]
  refine (FiniteQuadraticModule.Isometry.orthogonalQuotientEquiv_orthogonalQuotientMk
    _ _ _ _).trans (congrArg _ (Subtype.ext ?_))
  dsimp only
  rw [discriminantQuadraticIsometry_apply]
  refine discriminantEquiv_dualClassHom_of_intCast m ι _ z _ ?_
  simp

end TauCeti.ConstructionA
