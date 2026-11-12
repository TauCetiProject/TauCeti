/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic
public import TauCeti.NumberTheory.IntegralLattice.Mass
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.SmallRankUnimodular
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.WeylGroup

/-!
# The genus of `E₈`

The genus of the root lattice `E₈` has a single class, because `E₈` is the only positive definite
even unimodular lattice of rank eight
(`TauCeti.IntegralLattice.IsPosDef.nonempty_isometry_typeE₈RootLattice_of_isEven`). So its class
number is `1` and the mass of its genus is the reciprocal `1 / 696729600` of the order of its
isometry group (`TauCeti.IntegralLattice.card_isometry_typeE₈RootLattice`).

## Main results

* `TauCeti.IntegralLattice.genusClasses_typeE₈RootLattice`: the genus of `E₈` is the single class
  of `E₈`.
* `TauCeti.IntegralLattice.classNumber_typeE₈RootLattice`: the class number of `E₈` is `1`.
* `TauCeti.IntegralLattice.mass_typeE₈RootLattice`: the mass of the genus of `E₈` is
  `1 / 696729600`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.1, and
  Chapter 16, §1.
-/

public section

namespace TauCeti.IntegralLattice

/-- **The genus of `E₈` is a single class.** A lattice in the genus of `E₈` is positive definite,
even and unimodular of rank eight, hence isometric to `E₈`. -/
theorem genusClasses_typeE₈RootLattice :
    typeE₈RootLattice.genusClasses = {typeE₈RootLattice.isometryClass} := by
  ext c
  obtain ⟨M, rfl⟩ := isometryClass_surjective c
  rw [isometryClass_mem_genusClasses_iff, Set.mem_singleton_iff, eq_comm,
    isometryClass_eq_isometryClass_iff]
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.sameGenus⟩
  have hM := h.isPosDef_iff.mp isPosDef_typeE₈RootLattice
  have : M.IsNondegenerate := ⟨(M.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hM).2⟩
  refine hM.nonempty_isometry_typeE₈RootLattice_of_isEven
    (M.isUnimodular_iff_isUnit_determinant.mpr ?_) (h.isEven_iff.mp isEven_typeE₈RootLattice) ?_
  · rw [← h.determinant_eq, determinant_typeE₈RootLattice]
    exact isUnit_one
  · rw [← h.finrank_eq, typeE₈RootLattice.finrank_carrier, Module.finrank_fin_fun]

/-- The class number of `E₈` is `1`. -/
@[simp]
theorem classNumber_typeE₈RootLattice : typeE₈RootLattice.classNumber = 1 := by
  rw [classNumber_def, genusClasses_typeE₈RootLattice, Nat.card_unique]

/-- **The mass of the genus of `E₈` is `1 / 696729600`**, the reciprocal order of the isometry
group of its single class. -/
@[simp]
theorem mass_typeE₈RootLattice : typeE₈RootLattice.mass = 696729600⁻¹ := by
  obtain ⟨e⟩ :=
    isometryClass_eq_isometryClass_iff.mp (isometryClass_out typeE₈RootLattice.isometryClass)
  rw [mass_def, genusClasses_typeE₈RootLattice, finsum_mem_singleton, e.natCard_isometry_eq,
    card_isometry_typeE₈RootLattice, Nat.cast_ofNat]

end TauCeti.IntegralLattice
