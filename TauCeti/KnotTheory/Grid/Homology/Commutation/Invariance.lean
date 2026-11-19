/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Equation
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Basic
public import TauCeti.KnotTheory.Grid.Homology.Transpose

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
(`GridDiagram.unblockedHomologyCommutationMap_bijective`). Since `Φ_*` preserves the Alexander
grading and is semilinear along a renaming of the variables, for knot grids it is a graded
`R[U]`-isomorphism of degree zero, so `GH⁻` does not change under a column commutation as an
Alexander-graded `R[U]`-module (`GridDiagram.IsKnot.unblockedHomologyIsomorphic_swapColumns`).
Combined with the invariance of `GH⁻` under the diagonal reflection, which exchanges row and column
commutations, `GH⁻` is invariant under every elementary commutation
(`GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_isCommutation`).

## Main results

* `TauCeti.GridDiagram.unblockedHomologyCommutationMap_bijective`: **commutation invariance of
  `GH⁻`**, the commutation map on unblocked grid homology is bijective.
* `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_swapColumns`: for a knot grid, `GH⁻` is
  unchanged by a column commutation as an Alexander-graded `R[U]`-module.
* `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_isCommutation`: the same for any
  elementary commutation, of rows or of columns.

## References

Commutation invariance of grid homology is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Section 5.1, and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Geom. Topol. 11 (2007), Section 3.1 (arXiv:math/0610559).
-/

public section

open MvPolynomial

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
    rw [map_sub, ← hΨ, G.commutationMap_reverse_commutationMap_of_mem_ker C R z.2,
      add_sub_cancel_right]
  · -- The class of a cycle `z` of `GC⁻(G')` is the image of the class of `Ψ z`, since
    -- `Φ Ψ z - z = ∂' H' z`.
    obtain ⟨z, rfl⟩ := (G').unblockedHomologyClass_surjective R y
    have hΨz : (G').commutationMap R C.reverse z ∈ LinearMap.ker (G.unblockedDifferential R) := by
      have h := (G').commutationMap_mem_ker_unblockedDifferential R C.reverse z.2
      simpa only [ColumnCommutationData.reverse_column, swapColumns_swapColumns] using h
    refine ⟨G.unblockedHomologyClass R ⟨_, hΨz⟩, ?_⟩
    rw [unblockedHomologyCommutationMap_unblockedHomologyClass, ← sub_eq_zero, ← map_sub,
      unblockedHomologyClass_eq_zero_iff]
    refine ⟨(G').commutationHomotopy R C.reverse z, ?_⟩
    simp only [AddSubgroupClass.coe_sub,
      G.commutationMap_commutationMap_reverse_of_mem_ker C R z.2, add_sub_cancel_left]

end GridDiagram

/-! ### Invariance of the graded `K[U]`-module `GH⁻` -/

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **`GH⁻` is invariant under column commutation.** The commuted diagram of a knot grid along
validated column-commutation data is a knot grid whose `GH⁻` is isomorphic to that of the original
as an Alexander-graded `K[U]`-module. -/
theorem unblockedHomologyIsomorphic_swapColumns (C : ColumnCommutationData G) :
    hG.UnblockedHomologyIsomorphic (hG.swapColumns C.column (finRotate n C.column)) K := by
  refine .of_semilinearMap (fun p => ?_) (G.unblockedHomologyCommutationMap K C)
    (G.unblockedHomologyCommutationMap_bijective C K) fun a y hy => ?_
  · simp [aeval_rename, Function.comp_def]
  · let _ := hG.unblockedHomologyModule K
    let _ := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule K
    simpa using (hG.isHomogeneous_unblockedHomologyCommutationLinearMap K C).map_mem hy

/-- **`GH⁻` is invariant under elementary column commutations.** -/
theorem unblockedHomologyIsomorphic_of_isColumnCommutation {G' : GridDiagram n} (hG' : G'.IsKnot)
    (h : IsColumnCommutation G G') : hG.UnblockedHomologyIsomorphic hG' K := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact hG.unblockedHomologyIsomorphic_swapColumns K C

/-- **`GH⁻` is invariant under elementary commutations.** Two knot grids related by an elementary
row or column commutation have isomorphic `GH⁻` as Alexander-graded `K[U]`-modules; a row
commutation is a column commutation of the diagonal reflections. -/
theorem unblockedHomologyIsomorphic_of_isCommutation {G' : GridDiagram n} (hG' : G'.IsKnot)
    (h : IsCommutation G G') : hG.UnblockedHomologyIsomorphic hG' K := by
  rcases (isCommutation_iff G G').mp h with h | h
  · exact (hG.unblockedHomologyIsomorphic_transpose K).trans
      ((unblockedHomologyIsomorphic_of_isColumnCommutation _ K _
        ((isColumnCommutation_transpose G G').mpr h)).trans
        (hG'.unblockedHomologyIsomorphic_transpose K).symm)
  · exact hG.unblockedHomologyIsomorphic_of_isColumnCommutation K hG' h

end GridDiagram.IsKnot

end TauCeti
