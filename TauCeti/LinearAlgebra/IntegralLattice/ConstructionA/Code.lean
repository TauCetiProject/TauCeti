/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.CoordinateDiscriminant
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Basic
public import TauCeti.InformationTheory.Coding.Discriminant

/-!
# Additive codes in the Construction A discriminant group

The discriminant group of the zero-code Construction A lattice is canonically the coordinate
alphabet `(ℤ/m)^ι`. This file transports an additive code through that canonical isometry, so the
code becomes an actual subgroup of the discriminant group. The transport identifies bilinear
orthogonal complements and bilinear isotropy, and its inverse-image carrier is exactly the
Construction A carrier of the original code. The orthogonality statements use the finite
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

end TauCeti.ConstructionA
