/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Equation
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Basic

/-!
# Commutation invariance of `GH⁻`

Let `C` be validated data for a column commutation of a grid diagram `G`, exchanging the column
`a = C.column` with `b = finRotate n a`, and let `G' = G.swapColumns a b` be the commuted
diagram. The reverse data `C.reverse` commutes `G'` back to `G'.swapColumns a b`, which is `G`
again. Write `Φ : GC⁻(G) → GC⁻(G')` for the pentagon-counting map of `C`,
`Ψ : GC⁻(G') → GC⁻(G)` for that of `C.reverse`, and `H`, `H'` for the hexagon-counting maps of
`C` and `C.reverse`. Over a commutative semiring of characteristic two, the homotopy equation
`GridDiagram.unblockedDifferential_commutationHomotopy_add_eq` of `C.reverse` reads

  `∂' ∘ H' + H' ∘ ∂' = 1 + Φ ∘ Ψ`,

once the double swap is identified with `G`
(`GridDiagram.unblockedDifferential_commutationHomotopy_reverse_add_eq`), and `Ψ` is a chain map
`GC⁻(G') → GC⁻(G)` (`GridDiagram.commutationMap_reverse_comp_unblockedDifferential`). Together
with the homotopy equation of `C` itself, `Φ` and `Ψ` are mutually inverse chain homotopy
equivalences. In particular, on cycles, `Ψ ∘ Φ` and `Φ ∘ Ψ` are the identity up to a boundary.

Over a commutative ring of characteristic two this shows that the map `Φ_*` induced on `GH⁻`
(`GridDiagram.unblockedHomologyCommutationMap`) is bijective
(`GridDiagram.unblockedHomologyCommutationMap_bijective`). Since `Φ_*` preserves the
`(O-Maslov, Alexander)` bigrading and is semilinear along a renaming of the variables, for knot
grids it is a bigraded `R[U]`-isomorphism of degree zero, so `GH⁻` does not change under any
elementary commutation (`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_isCommutation`,
in `Homology/Bigraded/Invariance.lean`).

## Main results

* `TauCeti.GridDiagram.unblockedHomologyCommutationMap_bijective`: **commutation invariance of
  `GH⁻`**, the commutation map on unblocked grid homology is bijective.

## References

Commutation invariance of grid homology is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Section 5.1, and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Geom. Topol. 11 (2007), Section 3.1 (arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) (R : Type*)

local notation "G'" => G.swapColumns C.column (finRotate n C.column)

/-! ### Bijectivity on homology -/

variable [CommRing R] [CharP R 2]

/-- **Commutation invariance of `GH⁻`.** The map induced on unblocked grid homology by the
pentagon map of a validated column commutation is bijective. -/
theorem unblockedHomologyCommutationMap_bijective :
    Function.Bijective (G.unblockedHomologyCommutationMap R C) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun y => ?_⟩
  · -- If `Φ z = ∂' w`, then `z = Ψ Φ z - ∂ H z = ∂ (Ψ w - H z)`.
    obtain ⟨z, rfl⟩ := G.unblockedHomologyClass_surjective R y
    rw [unblockedHomologyCommutationMap_unblockedHomologyClass,
      unblockedHomologyClass_eq_zero_iff] at hy
    obtain ⟨w, hw⟩ := hy
    rw [unblockedHomologyClass_eq_zero_iff]
    refine ⟨(G').commutationMap R C.reverse w - G.commutationHomotopy R C z, ?_⟩
    have hΨ := LinearMap.congr_fun (G.commutationMap_reverse_comp_unblockedDifferential R C) w
    simp only [LinearMap.comp_apply, hw] at hΨ
    rw [map_sub, ← hΨ, G.commutationMap_reverse_commutationMap_of_mem_ker C R z.property,
      add_sub_cancel_right]
  · -- The class of a cycle `z` of `GC⁻(G')` is the image of the class of `Ψ z`, since
    -- `Φ Ψ z - z = ∂' H' z`.
    obtain ⟨z, rfl⟩ := (G').unblockedHomologyClass_surjective R y
    have hΨz : (G').commutationMap R C.reverse z ∈ LinearMap.ker (G.unblockedDifferential R) := by
      have h := (G').commutationMap_mem_ker_unblockedDifferential R C.reverse z.property
      simpa only [ColumnCommutationData.reverse_column, swapColumns_swapColumns] using h
    refine ⟨G.unblockedHomologyClass R ⟨_, hΨz⟩, ?_⟩
    rw [unblockedHomologyCommutationMap_unblockedHomologyClass, ← sub_eq_zero, ← map_sub,
      unblockedHomologyClass_eq_zero_iff]
    refine ⟨(G').commutationHomotopy R C.reverse z, ?_⟩
    simp only [AddSubgroupClass.coe_sub,
      G.commutationMap_commutationMap_reverse_of_mem_ker C R z.property, add_sub_cancel_left]

end GridDiagram

end TauCeti
