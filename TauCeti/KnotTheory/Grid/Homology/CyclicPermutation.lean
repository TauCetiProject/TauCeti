/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Grading.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology.KnotAlexander

/-!
# Invariance of `GH⁻` under cyclic permutation

Cyclically permuting the rows or the columns of a grid diagram is a grid move
(`GridDiagram.IsMove.cyclicRows`, `GridDiagram.IsMove.cyclicColumns`). This file shows that the
unblocked grid homology `GH⁻` of a knot grid, as an Alexander-graded `R[U]`-module, does not
change under either move.

The chain-level input is that relabeling every grid state by the cyclic permutation intertwines
the two unblocked differentials, after renaming the variables `V_c` along the same permutation
in the case of the columns (`Differential/CyclicPermutation.lean`). Any semilinear equivalence of
chain modules that intertwines two unblocked differentials induces a semilinear equivalence of
their homologies (`GridDiagram.unblockedHomologyEquivOfIntertwining`, in
`Homology/Unblocked.lean`). For a cyclic permutation
of the rows this is an isomorphism of modules over `R[V₀, …, V_{n-1}]`
(`GridDiagram.unblockedHomologyRelabelRowsFinRotateEquiv`); for the columns it is semilinear along
the renaming of the variables (`GridDiagram.unblockedHomologyRelabelColumnsFinRotateEquiv`).

Both moves preserve the Alexander grading of grid states (`Grading/CyclicPermutation.lean`), so
both equivalences preserve the Alexander grading of `GH⁻`
(`OddComponentGridDiagram.unblockedHomologyEquivOfIntertwining_mem_piece`, in
`Homology/Alexander.lean`). On a knot grid every variable acts as
`U`, and renaming the variables does not change the evaluation `V_c ↦ U`, so both equivalences
are graded `R[U]`-isomorphisms of degree zero
(`GridDiagram.IsKnot.unblockedHomologyIsomorphic_relabelRows_finRotate`,
`GridDiagram.IsKnot.unblockedHomologyIsomorphic_relabelColumns_finRotate`), so the invariants `τ`
agree (`GridDiagram.IsKnot.UnblockedHomologyIsomorphic.tau_eq`, in `Homology/Tau.lean`).
The corresponding statements for fully blocked grid homology are in `Homology/Symmetry.lean`.

## Main definitions

* `TauCeti.GridDiagram.unblockedHomologyRelabelRowsFinRotateEquiv`,
  `TauCeti.GridDiagram.unblockedHomologyRelabelColumnsFinRotateEquiv`: the equivalences induced by
  the cyclic permutations of the rows and of the columns.

## Main results

* `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_relabelRows_finRotate`,
  `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_relabelColumns_finRotate`: `GH⁻` of a
  knot grid is invariant under the cyclic permutation moves as an Alexander-graded `R[U]`-module.

## References

The invariance of grid homology under cyclic permutation is part of the invariance proof in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 5; `τ` is defined from
`GH⁻` in Chapter 6.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

/-! ### Cyclic permutations -/

variable (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- **Invariance of `GH⁻` under cyclic permutation of the rows.** Relabeling the grid states
along `finRotate n` induces an isomorphism of `R[V₀, …, V_{n-1}]`-modules from `GH⁻(G)` to the
unblocked homology of the row-permuted diagram. -/
noncomputable def unblockedHomologyRelabelRowsFinRotateEquiv :
    G.unblockedHomology R ≃ₗ[MvPolynomial (Fin n) R]
      (G.relabelRows (finRotate n)).unblockedHomology R :=
  G.unblockedHomologyEquivOfIntertwining R _ (GridChain.relabelRowsEquiv (finRotate n))
    (G.unblockedDifferential_relabelRows_finRotate_apply R)

/-- The row equivalence sends the class of a cycle `z` to the class of its relabeling. -/
@[simp]
theorem unblockedHomologyRelabelRowsFinRotateEquiv_unblockedHomologyClass
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyRelabelRowsFinRotateEquiv R (G.unblockedHomologyClass R z) =
      (G.relabelRows (finRotate n)).unblockedHomologyClass R
        ⟨GridChain.relabelRowsEquiv (finRotate n) z,
          G.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_relabelRows_finRotate_apply R) z.2⟩ :=
  G.unblockedHomologyEquivOfIntertwining_unblockedHomologyClass R _ _ _ z

/-- **Invariance of `GH⁻` under cyclic permutation of the columns.** Relabeling the grid states
along `finRotate n` and renaming the variables along the same permutation induces an equivalence
from `GH⁻(G)` to the unblocked homology of the column-permuted diagram, semilinear along the
renaming. -/
noncomputable def unblockedHomologyRelabelColumnsFinRotateEquiv :
    G.unblockedHomology R ≃ₛₗ[((renameEquiv R (finRotate n)).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)]
      (G.relabelColumns (finRotate n)).unblockedHomology R :=
  G.unblockedHomologyEquivOfIntertwining R _ (GridChain.relabelColumnsRenameEquiv R (finRotate n))
    (G.unblockedDifferential_relabelColumns_finRotate_apply R)

/-- The column equivalence sends the class of a cycle `z` to the class of its relabeling with
renamed coefficients. -/
@[simp]
theorem unblockedHomologyRelabelColumnsFinRotateEquiv_unblockedHomologyClass
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyRelabelColumnsFinRotateEquiv R (G.unblockedHomologyClass R z) =
      (G.relabelColumns (finRotate n)).unblockedHomologyClass R
        ⟨GridChain.relabelColumnsRenameEquiv R (finRotate n) z,
          G.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_relabelColumns_finRotate_apply R) z.2⟩ :=
  G.unblockedHomologyEquivOfIntertwining_unblockedHomologyClass R _ _ _ z

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ}

/-! ### The Alexander grading -/

variable (G : OddComponentGridDiagram n) (R : Type*) [CommRing R]

/-- Relabeling the grid states along a cyclic permutation of the rows preserves the Alexander
grading of chains. -/
theorem relabelRowsEquiv_mem_alexanderChainMinusPiece {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    GridChain.relabelRowsEquiv (finRotate n) c ∈
      (G.relabelRows (finRotate n)).alexanderChainMinusPiece R a := by
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  rw [GridChain.forall_mem_support_relabelRowsEquiv_iff]
  simpa only [alexanderℤ_relabelRows_finRotate] using hc

/-- Relabeling the grid states along a cyclic permutation of the columns and renaming the
variables along the same permutation preserves the Alexander grading of chains. -/
theorem relabelColumnsRenameEquiv_mem_alexanderChainMinusPiece {a : ℤ}
    {c : GridChainMinus R n} (hc : c ∈ G.alexanderChainMinusPiece R a) :
    GridChain.relabelColumnsRenameEquiv R (finRotate n) c ∈
      (G.relabelColumns (finRotate n)).alexanderChainMinusPiece R a := by
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  rw [GridChain.forall_mem_support_relabelColumnsRenameEquiv_iff]
  simpa only [alexanderℤ_relabelColumns_finRotate, Finsupp.degree_mapDomain] using hc

end OddComponentGridDiagram

/-! ### Invariance of the graded `K[U]`-module `GH⁻` -/

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **Cyclic permutation of the rows preserves `GH⁻`** of a knot grid as an Alexander-graded
`K[U]`-module. -/
theorem unblockedHomologyIsomorphic_relabelRows_finRotate :
    hG.UnblockedHomologyIsomorphic ((G.isKnot_relabelRows (finRotate n)).mpr hG) K := by
  refine .of_semilinearMap (σ := RingHom.id _) (fun _ ↦ rfl)
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).bijective fun a y hy ↦ ?_
  have hG' : hG.toOddComponentGridDiagram.relabelRows (finRotate n) =
      ((G.isKnot_relabelRows (finRotate n)).mpr hG).toOddComponentGridDiagram :=
    Subtype.ext (hG.toOddComponentGridDiagram.val_relabelRows _)
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
    ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff] at hy ⊢
  exact hG.toOddComponentGridDiagram.unblockedHomologyEquivOfIntertwining_mem_piece K _ _ _
    (fun _ _ hc ↦ hG' ▸
      hG.toOddComponentGridDiagram.relabelRowsEquiv_mem_alexanderChainMinusPiece K hc) hy

/-- **Cyclic permutation of the columns preserves `GH⁻`** of a knot grid as an Alexander-graded
`K[U]`-module. -/
theorem unblockedHomologyIsomorphic_relabelColumns_finRotate :
    hG.UnblockedHomologyIsomorphic ((G.isKnot_relabelColumns (finRotate n)).mpr hG) K := by
  refine .of_semilinearMap (fun p ↦ ?_)
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).bijective fun a y hy ↦ ?_
  · simp [aeval_rename, Function.comp_def]
  · have hG' : hG.toOddComponentGridDiagram.relabelColumns (finRotate n) =
        ((G.isKnot_relabelColumns (finRotate n)).mpr hG).toOddComponentGridDiagram :=
      Subtype.ext (hG.toOddComponentGridDiagram.val_relabelColumns _)
    rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
      ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff] at hy ⊢
    exact hG.toOddComponentGridDiagram.unblockedHomologyEquivOfIntertwining_mem_piece K _ _ _
      (fun _ _ hc ↦ hG' ▸
        hG.toOddComponentGridDiagram.relabelColumnsRenameEquiv_mem_alexanderChainMinusPiece K hc) hy

end GridDiagram.IsKnot

end TauCeti
