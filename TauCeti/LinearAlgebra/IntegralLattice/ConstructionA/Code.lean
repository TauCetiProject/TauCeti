/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.CoordinateDiscriminant
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic
public import TauCeti.InformationTheory.Coding.Discriminant

/-!
# Additive codes in the Construction A discriminant group

The discriminant group of the zero-code Construction A lattice is canonically the coordinate
alphabet `(ℤ/m)^ι`. This file transports an additive code through that canonical isometry, so the
code becomes an actual subgroup of the discriminant module rather than an opaque external datum.
The transport identifies orthogonal complements and isotropy, and its inverse-image carrier is
exactly the Construction A carrier of the original code.

The transported subgroup is exposed in both existing presentations: the finite-module form is the
reusable orthogonality API, while the quotient-typed form is the boundary consumed by the existing
overlattice API. Both are the same inverse-image construction under the two already-established
presentations of the zero-code discriminant group.

References:

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, §§1.3 and 3.3.
-/

public section

namespace TauCeti.ConstructionA

variable (m : ℕ+) (ι : Type*) [Fintype ι]

/-! ## Transport to the discriminant module -/

/-- The additive code `C` viewed as a subgroup of the zero-code discriminant module.

This is the literal inverse image under the canonical discriminant isometry, not an existential
subgroup chosen only up to cardinality. -/
noncomputable def codeInBaseDiscriminant (C : AdditiveCode (ZMod m) ι) :
    AddSubgroup (zeroLattice m ι).discriminantBilinearModule :=
  C.comap (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom

@[simp]
theorem mem_codeInBaseDiscriminant_iff (C : AdditiveCode (ZMod m) ι)
    {x : (zeroLattice m ι).discriminantBilinearModule} :
    x ∈ codeInBaseDiscriminant m ι C ↔ discriminantIsometry m ι x ∈ C :=
  Iff.rfl

/-- Reduction maps the transported discriminant subgroup back to the original code. -/
@[simp]
theorem map_codeInBaseDiscriminant (C : AdditiveCode (ZMod m) ι) :
    (codeInBaseDiscriminant m ι C).map (discriminantIsometry m ι).toAddEquiv = C := by
  -- `AddSubgroup.map` stores an `AddMonoidHom`, while the public statement uses the isometry's
  -- bundled equivalence; expose that coercion before applying the standard map-comap theorem.
  change AddSubgroup.map (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom
      (C.comap (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom) = C
  exact AddSubgroup.map_comap_eq_self_of_surjective
    (f := (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom)
    (discriminantIsometry m ι).toAddEquiv.surjective C

/-- The discriminant isometry carries the code's orthogonal complement to the orthogonal
complement of its transported subgroup. -/
theorem map_codeInBaseDiscriminant_orthogonalComplement (C : AdditiveCode (ZMod m) ι) :
    ((zeroLattice m ι).discriminantBilinearModule.orthogonalComplement
      (codeInBaseDiscriminant m ι C)).map (discriminantIsometry m ι).toAddEquiv =
      ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).orthogonalComplement C := by
  -- Normalize the bundled isometry map to the hom form expected by `AddSubgroup.map`.
  change AddSubgroup.map (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom
      ((zeroLattice m ι).discriminantBilinearModule.orthogonalComplement
        (codeInBaseDiscriminant m ι C)) = _
  calc
    _ = ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).orthogonalComplement
        ((codeInBaseDiscriminant m ι C).map (discriminantIsometry m ι).toAddEquiv) := by
      have h := (discriminantIsometry m ι).map_orthogonalComplement
        (H := codeInBaseDiscriminant m ι C)
      -- The same bundled-equivalence coercion occurs in the generic transport theorem.
      change AddSubgroup.map (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom _ = _ at h
      exact h
    _ = _ := by rw [map_codeInBaseDiscriminant]

/-- The orthogonal complement of a transported code is the transport of its Euclidean dual. -/
@[simp]
theorem orthogonalComplement_codeInBaseDiscriminant (C : AdditiveCode (ZMod m) ι) :
    (zeroLattice m ι).discriminantBilinearModule.orthogonalComplement
        (codeInBaseDiscriminant m ι C) =
      codeInBaseDiscriminant m ι
        (AddSubgroup.toZModSubmodule m C).euclideanDual.toAddSubgroup := by
  apply AddSubgroup.map_injective
    (f := (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom)
    (discriminantIsometry m ι).toAddEquiv.injective
  have h := map_codeInBaseDiscriminant_orthogonalComplement m ι C
  -- Normalize the map coercion so the preceding transport theorem can be reused verbatim.
  change AddSubgroup.map (discriminantIsometry m ι).toAddEquiv.toAddMonoidHom _ = _ at h
  rw [h, orthogonalComplement_coordinatePower_zmodStandard]
  exact (map_codeInBaseDiscriminant m ι
    (AddSubgroup.toZModSubmodule m C).euclideanDual.toAddSubgroup).symm

/-- Bilinear isotropy is preserved by the coordinate identification. -/
@[simp]
theorem isIsotropic_codeInBaseDiscriminant (C : AdditiveCode (ZMod m) ι) :
    (zeroLattice m ι).discriminantBilinearModule.IsIsotropic
        (codeInBaseDiscriminant m ι C) ↔
      ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).IsIsotropic C := by
  rw [← (discriminantIsometry m ι).isIsotropic_map_iff,
    map_codeInBaseDiscriminant]

/-- A code is isotropic in the actual discriminant group exactly when it is self-orthogonal. -/
@[simp]
theorem isIsotropic_codeInBaseDiscriminant_iff (C : AdditiveCode (ZMod m) ι) :
    (zeroLattice m ι).discriminantBilinearModule.IsIsotropic
        (codeInBaseDiscriminant m ι C) ↔
      AddSubgroup.toZModSubmodule m C ≤
        (AddSubgroup.toZModSubmodule m C).euclideanDual := by
  rw [isIsotropic_codeInBaseDiscriminant,
    isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual]

/-! ## The inverse-image carrier -/

/-- The same transported code in the quotient presentation used by intermediate-carrier gluing. -/
noncomputable def codeInBaseDiscriminantGroup (C : AdditiveCode (ZMod m) ι) :
    AddSubgroup (zeroLattice m ι).DiscriminantGroup :=
  C.comap (discriminantEquiv m ι).toAddEquiv.toAddMonoidHom

@[simp]
theorem mem_codeInBaseDiscriminantGroup_iff (C : AdditiveCode (ZMod m) ι)
    {x : (zeroLattice m ι).DiscriminantGroup} :
    x ∈ codeInBaseDiscriminantGroup m ι C ↔ discriminantEquiv m ι x ∈ C :=
  Iff.rfl

private theorem mem_intermediateCarrier_codeInBaseDiscriminant_iff
    (C : AdditiveCode (ZMod m) ι) (x : ι → ℚ) :
    x ∈ ((zeroLattice m ι).intermediateCarrierOfDiscriminantSubgroup
        (codeInBaseDiscriminantGroup m ι C)).1 ↔ x ∈ lattice m C := by
  constructor
  · intro hx
    obtain ⟨hxdual, hxC⟩ := (IntegralLattice.mem_intermediateCarrierOfDiscriminantSubgroup_iff
      (zeroLattice m ι) (codeInBaseDiscriminantGroup m ι C) x).mp hx
    obtain ⟨z, rfl⟩ := (mem_zeroLattice_dualCarrier_iff m ι).mp hxdual
    rw [mem_lattice (m := m)]
    refine ⟨z, ?_, rfl⟩
    -- The intermediate-carrier API exposes quotient membership, whereas the code definition is
    -- a comap; changing to the defining preimage makes the representative computation explicit.
    change discriminantEquiv m ι
        (Submodule.Quotient.mk (⟨(fun i ↦ (z i : ℚ)), hxdual⟩ :
          (zeroLattice m ι).dualCarrier)) ∈ C at hxC
    have hrep : (⟨(fun i ↦ (z i : ℚ)), hxdual⟩ : (zeroLattice m ι).dualCarrier) =
        dualCarrierIntEquiv m ι z := by
      apply Subtype.ext
      exact (coe_dualCarrierIntEquiv_apply m ι z).symm
    rw [hrep, discriminantEquiv_mk_intCast] at hxC
    exact hxC
  · intro hx
    obtain ⟨z, hz, rfl⟩ := (mem_lattice (m := m)).mp hx
    have hzdual : (fun i ↦ (z i : ℚ)) ∈ (zeroLattice m ι).dualCarrier :=
      (mem_zeroLattice_dualCarrier_iff m ι).mpr ⟨z, rfl⟩
    apply (IntegralLattice.mem_intermediateCarrierOfDiscriminantSubgroup_iff
      (zeroLattice m ι) (codeInBaseDiscriminantGroup m ι C) _).mpr
    refine ⟨hzdual, ?_⟩
    -- As above, expose the quotient representative before reducing its integer coordinates.
    change discriminantEquiv m ι
        (Submodule.Quotient.mk (⟨(fun i ↦ (z i : ℚ)), hzdual⟩ :
          (zeroLattice m ι).dualCarrier)) ∈ C
    have hrep : (⟨(fun i ↦ (z i : ℚ)), hzdual⟩ : (zeroLattice m ι).dualCarrier) =
        dualCarrierIntEquiv m ι z := by
      apply Subtype.ext
      exact (coe_dualCarrierIntEquiv_apply m ι z).symm
    rw [hrep, discriminantEquiv_mk_intCast]
    exact hz

/-- The inverse-image carrier of a transported code is its Construction A carrier. -/
theorem intermediateCarrierOfDiscriminantSubgroup_codeInBaseDiscriminant
    (C : AdditiveCode (ZMod m) ι) :
    ((zeroLattice m ι).intermediateCarrierOfDiscriminantSubgroup
      (codeInBaseDiscriminantGroup m ι C)).1 = lattice m C := by
  ext x
  exact mem_intermediateCarrier_codeInBaseDiscriminant_iff m ι C x

end TauCeti.ConstructionA
