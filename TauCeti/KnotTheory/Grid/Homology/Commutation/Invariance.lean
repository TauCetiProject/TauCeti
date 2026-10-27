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
# Commutation invariance of `GH⁻` and of `τ`

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
`R[U]`-isomorphism of degree zero, so the invariant `τ` does not change under a column
commutation (`GridDiagram.IsKnot.tau_swapColumns`). Combined with the invariance of `τ` under the
diagonal reflection, which exchanges row and column commutations, `τ` is invariant under every
elementary commutation (`GridDiagram.IsKnot.tau_eq_of_isCommutation`).

## Main results

* `TauCeti.GridDiagram.unblockedHomologyCommutationMap_bijective`: **commutation invariance of
  `GH⁻`**, the commutation map on unblocked grid homology is bijective.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns`: `τ` is unchanged by a column commutation.
* `TauCeti.GridDiagram.IsKnot.tau_eq_of_isCommutation`: `τ` is unchanged by any elementary
  commutation, of rows or of columns.

## References

Commutation invariance of grid homology is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Section 5.1, and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Geom. Topol. 11 (2007), Section 3.1 (arXiv:math/0610559); the invariant `τ` is defined
from `GH⁻` in Chapter 6 of the book.
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

/-! ### Invariance of `τ` -/

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **`τ` is invariant under column commutation.** The commuted diagram of a knot grid along
validated column-commutation data is a knot grid with the same invariant `τ`. -/
theorem tau_swapColumns (C : ColumnCommutationData G) :
    (hG.swapColumns C.column (finRotate n C.column)).tau K = hG.tau K := by
  refine (hG.tau_eq_of_semilinearMap K _ (fun p => ?_) (G.unblockedHomologyCommutationMap K C)
    (G.unblockedHomologyCommutationMap_bijective C K) fun a y hy => ?_).symm
  · simp [aeval_rename, Function.comp_def]
  · let _ := hG.unblockedHomologyModule K
    let _ := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule K
    simpa using (hG.isHomogeneous_unblockedHomologyCommutationLinearMap K C).map_mem hy

/-- **`τ` is invariant under elementary column commutations.** -/
theorem tau_eq_of_isColumnCommutation {G' : GridDiagram n} (hG' : G'.IsKnot)
    (h : IsColumnCommutation G G') : hG.tau K = hG'.tau K := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact (hG.tau_swapColumns K C).symm

/-- **`τ` is invariant under elementary commutations.** Two knot grids related by an elementary
row or column commutation have the same invariant `τ`; a row commutation is a column
commutation of the diagonal reflections. -/
theorem tau_eq_of_isCommutation {G' : GridDiagram n} (hG' : G'.IsKnot)
    (h : IsCommutation G G') : hG.tau K = hG'.tau K := by
  rcases (isCommutation_iff G G').mp h with h | h
  · rw [← hG.tau_transpose K, ← hG'.tau_transpose K]
    exact tau_eq_of_isColumnCommutation _ K _ ((isColumnCommutation_transpose G G').mpr h)
  · exact hG.tau_eq_of_isColumnCommutation K hG' h

end GridDiagram.IsKnot

end TauCeti
