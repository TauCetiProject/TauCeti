/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.CoordinateDiscriminant
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic
public import TauCeti.InformationTheory.Coding.Discriminant

/-!
# Additive codes in the Construction A discriminant group

The discriminant group of the zero-code Construction A lattice is canonically the coordinate
alphabet `(ℤ/m)^ι`. This file transports an additive code through that canonical isometry, so the
code becomes an actual subgroup of the discriminant group. The transport identifies bilinear
orthogonal complements and bilinear isotropy, and its inverse-image carrier is exactly the
Construction A carrier of the original code. Gluing along a self-orthogonal code gives the
Construction A integral lattice. The orthogonality statements use the finite
bilinear-module presentation, while the carrier statement uses the quotient discriminant-group
presentation required by the corresponding APIs. Quadratic isotropy is not treated here.

References:

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, §§1.3 and 3.3.
-/

public section

namespace TauCeti.ConstructionA

variable (m : ℕ+) (ι : Type*) [Fintype ι]

/-! ## Transport to the discriminant module -/

/-- The additive code `C` as the inverse image under the canonical isometry from the zero-lattice
discriminant group to the coordinate alphabet. -/
noncomputable def codeInZeroLatticeDiscriminantBilinearModule (C : AdditiveCode (ZMod m) ι) :
    AddSubgroup (zeroLattice m ι).discriminantBilinearModule :=
  C.comap (discriminantIsometry m ι).toAddEquiv

@[simp]
theorem mem_codeInZeroLatticeDiscriminantBilinearModule_iff (C : AdditiveCode (ZMod m) ι)
    {x : (zeroLattice m ι).discriminantBilinearModule} :
    x ∈ codeInZeroLatticeDiscriminantBilinearModule m ι C ↔ discriminantIsometry m ι x ∈ C :=
  Iff.rfl

/-- Reduction maps the transported discriminant subgroup back to the original code. -/
@[simp]
theorem map_codeInZeroLatticeDiscriminantBilinearModule (C : AdditiveCode (ZMod m) ι) :
    (codeInZeroLatticeDiscriminantBilinearModule m ι C).map
      (discriminantIsometry m ι).toAddEquiv = C := by
  rw [codeInZeroLatticeDiscriminantBilinearModule]
  exact AddSubgroup.map_comap_eq_self_of_surjective
    (f := (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom)
    (discriminantIsometry m ι).toAddEquiv.surjective C

/-- The orthogonal complement of a transported code is the transport of its Euclidean dual. -/
@[simp]
theorem orthogonalComplement_codeInZeroLatticeDiscriminantBilinearModule
    (C : AdditiveCode (ZMod m) ι) :
    (zeroLattice m ι).discriminantBilinearModule.orthogonalComplement
        (codeInZeroLatticeDiscriminantBilinearModule m ι C) =
      codeInZeroLatticeDiscriminantBilinearModule m ι
        (AddSubgroup.toZModSubmodule m C).euclideanDual.toAddSubgroup := by
  rw [codeInZeroLatticeDiscriminantBilinearModule,
    (discriminantIsometry m ι).comap_orthogonalComplement,
    orthogonalComplement_coordinatePower_zmodStandard,
    codeInZeroLatticeDiscriminantBilinearModule]

/-- An integer vector lies in the dual of the Construction A lattice exactly when its reduction
lies in the orthogonal complement of the code in the coordinate alphabet. -/
theorem intCast_mem_integralLattice_dualCarrier_iff (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (z : ι → ℤ) :
    (fun i ↦ (z i : ℚ)) ∈ (integralLattice m C hC).dualCarrier ↔
      (fun i ↦ (z i : ZMod m)) ∈
        ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).orthogonalComplement C := by
  rw [integralLattice_dualCarrier, intCast_mem_lattice,
    orthogonalComplement_coordinatePower_zmodStandard]

/-- Bilinear isotropy is preserved by the coordinate identification. -/
@[simp]
theorem isIsotropic_codeInZeroLatticeDiscriminantBilinearModule_iff
    (C : AdditiveCode (ZMod m) ι) :
    (zeroLattice m ι).discriminantBilinearModule.IsIsotropic
        (codeInZeroLatticeDiscriminantBilinearModule m ι C) ↔
      ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).IsIsotropic C := by
  rw [codeInZeroLatticeDiscriminantBilinearModule,
    (discriminantIsometry m ι).isIsotropic_comap_iff]

/-- A code is bilinearly isotropic in the discriminant group exactly when it is self-orthogonal. -/
theorem isIsotropic_codeInZeroLatticeDiscriminantBilinearModule_iff_le_euclideanDual
    (C : AdditiveCode (ZMod m) ι) :
    (zeroLattice m ι).discriminantBilinearModule.IsIsotropic
        (codeInZeroLatticeDiscriminantBilinearModule m ι C) ↔
      AddSubgroup.toZModSubmodule m C ≤
        (AddSubgroup.toZModSubmodule m C).euclideanDual := by
  rw [isIsotropic_codeInZeroLatticeDiscriminantBilinearModule_iff,
    isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual]

/-! ## The inverse-image carrier -/

/-- The same inverse-image code as a subgroup of the quotient discriminant group used by
intermediate-carrier constructions. -/
noncomputable def codeInZeroLatticeDiscriminantGroup (C : AdditiveCode (ZMod m) ι) :
    AddSubgroup (zeroLattice m ι).DiscriminantGroup :=
  C.comap (discriminantEquiv m ι).toAddEquiv

@[simp]
theorem mem_codeInZeroLatticeDiscriminantGroup_iff (C : AdditiveCode (ZMod m) ι)
    {x : (zeroLattice m ι).DiscriminantGroup} :
    x ∈ codeInZeroLatticeDiscriminantGroup m ι C ↔ discriminantEquiv m ι x ∈ C :=
  Iff.rfl

/-- The quotient-group view has the same coordinate membership characterization as the
finite-bilinear-module view, expressed through the canonical discriminant isometry. -/
theorem mem_codeInZeroLatticeDiscriminantGroup_iff_discriminantIsometry
    (C : AdditiveCode (ZMod m) ι) {x : (zeroLattice m ι).DiscriminantGroup} :
    x ∈ codeInZeroLatticeDiscriminantGroup m ι C ↔ discriminantIsometry m ι x ∈ C := by
  rw [mem_codeInZeroLatticeDiscriminantGroup_iff, discriminantIsometry_apply]

/-- The quotient-group and finite-bilinear-module views of a transported code are the same
subgroup of the zero-lattice discriminant group. -/
theorem codeInZeroLatticeDiscriminantGroup_eq_codeInZeroLatticeDiscriminantBilinearModule
    (C : AdditiveCode (ZMod m) ι) :
    codeInZeroLatticeDiscriminantGroup m ι C = codeInZeroLatticeDiscriminantBilinearModule m ι C :=
  AddSubgroup.ext fun _ ↦ mem_codeInZeroLatticeDiscriminantGroup_iff_discriminantIsometry m ι C

/-- The subgroup of the zero-lattice discriminant group transported from a self-orthogonal code
is isotropic for the discriminant pairing. -/
theorem isIsotropic_codeInZeroLatticeDiscriminantGroup (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (zeroLattice m ι).discriminantBilinearModule.IsIsotropic
      (codeInZeroLatticeDiscriminantGroup m ι C) := by
  rw [codeInZeroLatticeDiscriminantGroup_eq_codeInZeroLatticeDiscriminantBilinearModule,
    isIsotropic_codeInZeroLatticeDiscriminantBilinearModule_iff_le_euclideanDual]
  exact hC

/-- Reduction maps the transported discriminant subgroup back to the original code. -/
@[simp]
theorem map_codeInZeroLatticeDiscriminantGroup (C : AdditiveCode (ZMod m) ι) :
    (codeInZeroLatticeDiscriminantGroup m ι C).map (discriminantEquiv m ι).toAddEquiv = C := by
  rw [codeInZeroLatticeDiscriminantGroup]
  exact AddSubgroup.map_comap_eq_self_of_surjective
    (f := (discriminantEquiv m ι).toAddEquiv.toAddMonoidHom)
    (discriminantEquiv m ι).toAddEquiv.surjective C

private theorem mem_intermediateCarrier_codeInZeroLatticeDiscriminantGroup_iff
    (C : AdditiveCode (ZMod m) ι) (x : ι → ℚ) :
    x ∈ ((zeroLattice m ι).intermediateCarrierOfDiscriminantSubgroup
        (codeInZeroLatticeDiscriminantGroup m ι C)).1 ↔ x ∈ lattice m C := by
  constructor
  · intro hx
    obtain ⟨hxdual, hxC⟩ := (IntegralLattice.mem_intermediateCarrierOfDiscriminantSubgroup_iff
      (zeroLattice m ι) (codeInZeroLatticeDiscriminantGroup m ι C) x).mp hx
    obtain ⟨z, rfl⟩ := (mem_zeroLattice_dualCarrier_iff m ι).mp hxdual
    rw [mem_lattice (m := m)]
    refine ⟨z, ?_, rfl⟩
    rw [mem_codeInZeroLatticeDiscriminantGroup_iff,
      discriminantEquiv_mk_of_intCast] at hxC
    exact hxC
  · intro hx
    obtain ⟨z, hz, rfl⟩ := (mem_lattice (m := m)).mp hx
    have hzdual : (fun i ↦ (z i : ℚ)) ∈ (zeroLattice m ι).dualCarrier :=
      (mem_zeroLattice_dualCarrier_iff m ι).mpr ⟨z, rfl⟩
    apply (IntegralLattice.mem_intermediateCarrierOfDiscriminantSubgroup_iff
      (zeroLattice m ι) (codeInZeroLatticeDiscriminantGroup m ι C) _).mpr
    refine ⟨hzdual, ?_⟩
    rw [mem_codeInZeroLatticeDiscriminantGroup_iff,
      discriminantEquiv_mk_of_intCast]
    exact hz

/-- The inverse-image carrier of a transported code is its Construction A carrier. -/
@[simp]
theorem coe_intermediateCarrierOfDiscriminantSubgroup_codeInZeroLatticeDiscriminantGroup
    (C : AdditiveCode (ZMod m) ι) :
    ((zeroLattice m ι).intermediateCarrierOfDiscriminantSubgroup
      (codeInZeroLatticeDiscriminantGroup m ι C)).1 = lattice m C := by
  ext x
  exact mem_intermediateCarrier_codeInZeroLatticeDiscriminantGroup_iff m ι C x

/-- **Gluing the zero-code lattice along a self-orthogonal code gives Construction A.** The
integral overlattice of `m ℤ^ι` glued along the discriminant subgroup of `C` has the literal
Construction A carrier and the same normalized dot-product form. -/
theorem toIntegralLattice_codeInZeroLatticeDiscriminantGroup_eq_integralLattice
    (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    ((zeroLattice m ι).isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff _ |>.mpr
        (isIsotropic_codeInZeroLatticeDiscriminantGroup m ι C hC)).toIntegralLattice =
      integralLattice m C hC := by
  apply IntegralLattice.ext
  · rw [IntegralLattice.IntermediateCarrier.IsIntegral.toIntegralLattice_carrier,
      integralLattice_carrier,
      coe_intermediateCarrierOfDiscriminantSubgroup_codeInZeroLatticeDiscriminantGroup]
  · rw [IntegralLattice.IntermediateCarrier.IsIntegral.toIntegralLattice_form, zeroLattice_form,
      integralLattice_form]

end TauCeti.ConstructionA
