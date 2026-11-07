/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Minimum
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.RepresentationNumber
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Roots

/-!
# Distinguishing the rootful rank-24 lattices

The 23 glued rootful rank-24 lattices are pairwise non-isometric, and none is isometric
to the rootless Leech lattice. Two elementary invariants
suffice: the number of roots and the index of their integral span. The glue-minimum checks
identify the actual roots with those of the component root lattice, so the first invariant
is the sum of the component root counts and the second is the order of the glue subgroup.
The pairs of numbers are distinct, even for rows with the same root count.

This proves non-isometry of the constructed lattices, not completeness of the table.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed.,
  Chapter 16, Table 16.1.
-/

public section

namespace TauCeti.RootfulNiemeierType

open IntegralLattice

/-- The number of roots in the component root lattice is the displayed root count. -/
@[simp]
theorem representationNumber_rootLattice_two (r : RootfulNiemeierType) :
    r.rootLattice.representationNumber 2 = r.rootCount := by
  have hmin (i : Fin r.components.length) (x : (r.componentType i).rootLattice
      (r.isSimplyLaced_componentType i)) (hx : x ≠ 0) :
      2 ≤ ((r.componentType i).rootLattice (r.isSimplyLaced_componentType i)).norm x :=
    IsPosDef.two_le_norm_of_ne_zero
      ((r.componentType i).isPosDef_rootLattice (r.isSimplyLaced_componentType i))
      ((r.componentType i).isEven_rootLattice (r.isSimplyLaced_componentType i)) hx
  rw [representationNumber_pi_of_le_norm _ (by norm_num) hmin
    (fun i ↦ ((r.componentType i).isPosDef_rootLattice
      (r.isSimplyLaced_componentType i)).finite_vectorsOfNorm 2)]
  simp only [DynkinType.representationNumber_rootLattice_two _ _ (r.valid_componentType _)]
  cases r <;> decide

/-- The actual glued lattice has exactly the displayed number of roots. -/
@[simp]
theorem representationNumber_lattice_two (r : RootfulNiemeierType) :
    r.lattice.representationNumber 2 = r.rootCount := by
  rw [representationNumber_def, ← Set.ncard_image_of_injective _ Subtype.val_injective,
    r.image_vectorsOfNorm_two_lattice,
    Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [← representationNumber_def]
  exact r.representationNumber_rootLattice_two

/-- The index of the integral span of the roots is the displayed glue order. -/
@[simp]
theorem index_span_vectorsOfNorm_two_lattice (r : RootfulNiemeierType) :
    (Submodule.span ℤ (r.lattice.vectorsOfNorm 2)).toAddSubgroup.index = r.glueOrder := by
  have hspan : (Submodule.span ℤ (r.lattice.vectorsOfNorm 2)).map
      r.lattice.carrier.subtype = r.rootLattice.carrier := by
    rw [Submodule.map_span]
    exact r.span_vectorsOfNorm_two_lattice
  have h := AddSubgroup.relIndex_map_map_of_injective
    (f := (r.lattice.carrier.subtype :
      r.lattice →+ (∀ i, Fin (r.componentType i).rank → ℚ)))
    (Submodule.span ℤ (r.lattice.vectorsOfNorm 2)).toAddSubgroup ⊤
    r.lattice.carrier.injective_subtype
  rw [← Submodule.map_toAddSubgroup r.lattice.carrier.subtype, hspan] at h
  have hrange : (r.lattice.carrier.subtype :
      r.lattice →+ (∀ i, Fin (r.componentType i).rank → ℚ)).range =
      r.lattice.carrier.toAddSubgroup := by
    ext x
    simp
  simpa only [AddSubgroup.map_top, hrange, AddSubgroup.relIndex_top_right,
    r.relIndex_rootLattice_lattice, r.natCard_glueSubgroup] using h.symm

/-- The root count together with the glue order distinguishes all 23 rows. -/
theorem rootCount_glueOrder_injective :
    Function.Injective (fun r : RootfulNiemeierType ↦ (r.rootCount, r.glueOrder)) := by
  decide

/-- Two rootful table lattices are isometric exactly when they are the same row. -/
@[simp]
theorem nonempty_isometry_lattice_iff (r s : RootfulNiemeierType) :
    Nonempty (Isometry r.lattice s.lattice) ↔ r = s := by
  refine ⟨fun ⟨e⟩ ↦ ?_, ?_⟩
  · apply rootCount_glueOrder_injective
    have hcount := e.representationNumber_eq 2
    have hindex := AddSubgroup.index_map_of_bijective
      (f := (e.carrierEquiv.toLinearMap : r.lattice →+ s.lattice)) e.carrierEquiv.bijective
      (Submodule.span ℤ (r.lattice.vectorsOfNorm 2)).toAddSubgroup
    rw [← Submodule.map_toAddSubgroup e.carrierEquiv.toLinearMap,
      e.map_span_vectorsOfNorm] at hindex
    exact Prod.ext (by simpa using hcount) (by simpa using hindex.symm)
  · rintro rfl
    exact ⟨Isometry.refl _⟩

/-- None of the 23 rootful table lattices is isometric to the Leech lattice. -/
@[simp]
theorem not_nonempty_isometry_lattice_leechLattice (r : RootfulNiemeierType) :
    ¬ Nonempty (Isometry r.lattice leechLattice) := by
  rintro ⟨e⟩
  have h := e.representationNumber_eq 2
  rw [representationNumber_lattice_two, representationNumber_def,
    vectorsOfNorm_two_leechLattice, Set.ncard_empty] at h
  have hpos : 0 < r.rootCount := by cases r <;> decide
  omega

end TauCeti.RootfulNiemeierType
