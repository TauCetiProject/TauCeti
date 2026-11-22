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
(`GridDiagram.IsMove.cyclicRows`, `GridDiagram.IsMove.cyclicColumns`). This file constructs the
equivalences that either move induces on the unblocked grid homology `GH⁻` and shows that they
preserve the Alexander grading.

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
`Homology/Alexander.lean`). They also preserve the full `(O-Maslov, Alexander)` bigrading
(`Homology/Bigraded/CyclicPermutation.lean`), so on a knot grid, where every variable acts as `U`
and renaming the variables does not change the evaluation `V_c ↦ U`, both moves preserve `GH⁻` as
a bigraded `R[U]`-module
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate`,
`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate`, in
`Homology/Bigraded/Invariance.lean`). The corresponding statements for fully blocked grid
homology are in `Homology/Symmetry.lean`.

## Main definitions

* `TauCeti.GridDiagram.unblockedHomologyRelabelRowsFinRotateEquiv`,
  `TauCeti.GridDiagram.unblockedHomologyRelabelColumnsFinRotateEquiv`: the equivalences induced by
  the cyclic permutations of the rows and of the columns.

## Main results

* `TauCeti.OddComponentGridDiagram.relabelRowsEquiv_mem_alexanderChainMinusPiece`,
  `TauCeti.OddComponentGridDiagram.relabelColumnsRenameEquiv_mem_alexanderChainMinusPiece`: the
  chain-level relabelings preserve the Alexander grading.

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
            (G.unblockedDifferential_relabelRows_finRotate_apply R) z.property⟩ :=
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
            (G.unblockedDifferential_relabelColumns_finRotate_apply R) z.property⟩ :=
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

end TauCeti
