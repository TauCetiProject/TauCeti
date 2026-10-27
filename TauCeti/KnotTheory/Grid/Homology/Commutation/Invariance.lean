/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Equation
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Basic
public import TauCeti.KnotTheory.Grid.Homology.Transpose
import TauCeti.Algebra.CharP.Two

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

* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_reverse_add_eq`: the homotopy
  equation `∂' ∘ H' + H' ∘ ∂' = 1 + Φ ∘ Ψ` on the commuted diagram.
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

/-! ### The reverse commutation at chain level -/

section Chain

variable [CommSemiring R] [CharP R 2]

omit [CommSemiring R] [CharP R 2] in
/-- Commuting back along the reverse data recovers the original diagram. -/
private theorem swapColumns_reverse_swapColumns :
    (G').swapColumns C.reverse.column (finRotate n C.reverse.column) = G := by
  rw [ColumnCommutationData.reverse_column, swapColumns_swapColumns]

/-- **The reverse commutation map is a chain map back to `G`.** The pentagon map `Ψ` of the
reverse commutation intertwines the unblocked differential of the commuted diagram with that of
`G`. -/
theorem commutationMap_reverse_comp_unblockedDifferential :
    ((G').commutationMap R C.reverse).comp ((G').unblockedDifferential R) =
      (G.unblockedDifferential R).comp ((G').commutationMap R C.reverse) := by
  have h := (G').commutationMap_comp_unblockedDifferential C.reverse R
  rwa [swapColumns_reverse_swapColumns] at h

/-- **The homotopy equation on the commuted diagram.** The hexagon map `H'` of the reverse
commutation is a chain homotopy between the identity of `GC⁻(G')` and the round trip `Φ ∘ Ψ`
through `G`: `∂' ∘ H' + H' ∘ ∂' = 1 + Φ ∘ Ψ`. -/
theorem unblockedDifferential_commutationHomotopy_reverse_add_eq (c : GridChainMinus R n) :
    (G').unblockedDifferential R ((G').commutationHomotopy R C.reverse c) +
        (G').commutationHomotopy R C.reverse ((G').unblockedDifferential R c) =
      c + G.commutationMap R C ((G').commutationMap R C.reverse c) := by
  have h := (G').unblockedDifferential_commutationHomotopy_add_eq C.reverse R c
  -- The type of the twice-reversed data mentions the doubly swapped diagram, so its turn is
  -- replaced by that of `C` before that diagram is rewritten to `G`.
  have hturn : (C.reverse.reverse : ColumnTurn n) = C := ColumnTurn.ext (by simp) (by simp)
  rwa [hturn, swapColumns_reverse_swapColumns] at h

/-- On a cycle `z` of `GC⁻(G)`, the round trip `Ψ ∘ Φ` through the commuted diagram is the
identity up to the boundary of `H z`. -/
theorem commutationMap_reverse_commutationMap_of_mem_ker {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G').commutationMap R C.reverse (G.commutationMap R C z) =
      z + G.unblockedDifferential R (G.commutationHomotopy R C z) := by
  have h := G.unblockedDifferential_commutationHomotopy_add_eq C R z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) z, zero_add]

/-- On a cycle `z` of `GC⁻(G')`, the round trip `Φ ∘ Ψ` through `G` is the identity up to the
boundary of `H' z`. -/
theorem commutationMap_commutationMap_reverse_of_mem_ker {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker ((G').unblockedDifferential R)) :
    G.commutationMap R C ((G').commutationMap R C.reverse z) =
      z + (G').unblockedDifferential R ((G').commutationHomotopy R C.reverse z) := by
  have h := G.unblockedDifferential_commutationHomotopy_reverse_add_eq C R z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) z, zero_add]

end Chain

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
    have hΨ := LinearMap.congr_fun (G.commutationMap_reverse_comp_unblockedDifferential C R) w
    simp only [LinearMap.comp_apply, hw] at hΨ
    rw [map_sub, ← hΨ, G.commutationMap_reverse_commutationMap_of_mem_ker C R z.2,
      add_sub_cancel_right]
  · -- The class of a cycle `z` of `GC⁻(G')` is the image of the class of `Ψ z`, since
    -- `Φ Ψ z - z = ∂' H' z`.
    obtain ⟨z, rfl⟩ := (G').unblockedHomologyClass_surjective R y
    have hΨz : (G').commutationMap R C.reverse z ∈ LinearMap.ker (G.unblockedDifferential R) := by
      have h := LinearMap.congr_fun (G.commutationMap_reverse_comp_unblockedDifferential C R) z
      simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp z.2, map_zero] at h
      exact LinearMap.mem_ker.mpr h.symm
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
