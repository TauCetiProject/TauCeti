/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Transpose
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Relation

/-!
# The diagonal reflection on unblocked grid homology

The diagonal reflection carries a grid diagram `G` to `G.transpose` and its grid states to their
reflections, and it intertwines the unblocked differentials once the variables are renamed along
the permutation `G.O` (`Differential/Transpose.lean`). This file descends that symmetry to
unblocked grid homology: `GH⁻(G)` and `GH⁻(G.transpose)` are identified by a semilinear
equivalence along the renaming of the variables. The reflection preserves the `O`-Maslov and
Alexander gradings of grid states, so on chains and on homology it preserves the full bigrading.
Hence for a knot grid the two homologies are isomorphic as bigraded `R[U]`-modules
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_transpose`), and so also as
Alexander-graded `R[U]`-modules (`GridDiagram.IsKnot.unblockedHomologyIsomorphic_transpose`).

The reflection exchanges row and column commutations (`GridDiagram.isColumnCommutation_transpose`).
So the invariance of `GH⁻` under row commutations follows from its invariance under the
diagonal reflection and under column commutations
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_isCommutation`, in
`Homology/Bigraded/Invariance.lean`).

## Main definitions

* `TauCeti.GridDiagram.unblockedHomologyTransposeEquiv`: the equivalence
  `GH⁻(G) ≃ GH⁻(G.transpose)` induced by the diagonal reflection, semilinear along the renaming of
  the variables by `G.O`.

## Main results

* `TauCeti.GridDiagram.unblockedHomologyTransposeEquiv_unblockedHomologyClass`,
  `TauCeti.GridDiagram.unblockedHomologyTransposeEquiv_symm_unblockedHomologyClass`: it and its
  inverse send the class of a cycle to the class of the reflected cycle.
* `unblockedHomologyTransposeEquiv_mem_bigradedUnblockedHomologyPiece`, in the namespace
  `TauCeti.OddComponentGridDiagram`: it preserves the `O`-Maslov--Alexander bigrading.
* `TauCeti.GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_transpose`,
  `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_transpose`: for a knot grid, `GH⁻` is
  unchanged by the diagonal reflection as a bigraded, and so as an Alexander-graded,
  `R[U]`-module.

## References

The symmetries of grid diagrams are in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3, and unblocked grid homology is defined in Chapter 4.6.
The construction adapts the half-turn symmetry of `TauCeti.KnotTheory.Grid.Homology.HalfTurn`
(`GridDiagram.unblockedHomologyRotateEquiv` and its grading preservation on chains) to the
diagonal reflection.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- **The diagonal reflection on `GH⁻`.** Reflecting grid states and renaming the variables along
`G.O` induces an equivalence from `GH⁻(G)` to the unblocked homology of the reflected diagram
`G.transpose`, semilinear along the renaming. -/
noncomputable def unblockedHomologyTransposeEquiv :
    G.unblockedHomology R ≃ₛₗ[((renameEquiv R G.O.toPerm).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] G.transpose.unblockedHomology R :=
  G.unblockedHomologyEquivOfIntertwining R _ (G.transposeRenameEquiv R)
    (G.unblockedDifferential_transpose_transposeRenameEquiv R)

/-- The reflection sends the class of a cycle `z` to the class of the reflected cycle. -/
@[simp]
theorem unblockedHomologyTransposeEquiv_unblockedHomologyClass
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyTransposeEquiv R (G.unblockedHomologyClass R z) =
      G.transpose.unblockedHomologyClass R
        ⟨G.transposeRenameEquiv R z,
          G.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_transpose_transposeRenameEquiv R) z.property⟩ :=
  G.unblockedHomologyEquivOfIntertwining_unblockedHomologyClass R _ _ _ z

/-- The inverse of the reflection sends the class of a cycle `w` of `GC⁻(G.transpose)` to the
class of its reflection back to `G`. -/
@[simp]
theorem unblockedHomologyTransposeEquiv_symm_unblockedHomologyClass
    (w : LinearMap.ker (G.transpose.unblockedDifferential R)) :
    (G.unblockedHomologyTransposeEquiv R).symm (G.transpose.unblockedHomologyClass R w) =
      G.unblockedHomologyClass R
        ⟨G.transpose.transposeRenameEquiv R w,
          G.transpose.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_transposeRenameEquiv R) w.property⟩ := by
  rw [LinearEquiv.symm_apply_eq, unblockedHomologyTransposeEquiv_unblockedHomologyClass]
  -- `G.transpose.transpose` is `G` by definition, so the involution law applies as stated.
  exact congrArg _ (Subtype.ext
    (G.transpose.transposeRenameEquiv_transpose_transposeRenameEquiv R w).symm)

end GridDiagram

namespace OddComponentGridDiagram

section Chains

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

/-- The diagonal reflection, including the renaming of the coefficient variables along `G.O`,
preserves the full `O`-Maslov--Alexander bigrading of unblocked chains. -/
theorem transposeRenameEquiv_mem_bigradedChainMinusPiece {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.val.transposeRenameEquiv R c ∈ G.transpose.bigradedChainMinusPiece R g := by
  classical
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro x e he
  rw [GridDiagram.transposeRenameEquiv_apply,
    support_rename_of_injective G.val.O.toPerm.injective, Finset.mem_image] at he
  obtain ⟨e, he, rfl⟩ := he
  have hM := G.val.maslovOℤ_transpose x.transpose
  have hA := G.alexanderℤ_transpose x.transpose
  rw [GridState.transpose_transpose] at hM hA
  have hdegree : G.transpose.monomialBidegree x (e.mapDomain G.val.O.toPerm) =
      G.monomialBidegree x.transpose e := by
    apply Prod.ext <;>
      simp only [monomialBidegree_fst, monomialBidegree_snd, hM, hA,
        Finsupp.degree_mapDomain]
  rw [hdegree]
  exact hc x.transpose e he

end Chains

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The equivalence induced by the diagonal reflection preserves the `O`-Maslov--Alexander
bigrading on homology. -/
theorem unblockedHomologyTransposeEquiv_mem_bigradedUnblockedHomologyPiece {g : ℤ × ℤ}
    {y : G.val.unblockedHomology R} (hy : y ∈ G.bigradedUnblockedHomologyPiece R g) :
    G.val.unblockedHomologyTransposeEquiv R y ∈
      G.transpose.bigradedUnblockedHomologyPiece R g := by
  obtain ⟨z, hz, rfl⟩ := (G.mem_bigradedUnblockedHomologyPiece_iff R).mp hy
  rw [GridDiagram.unblockedHomologyTransposeEquiv_unblockedHomologyClass]
  exact G.transpose.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R
    (G.transposeRenameEquiv_mem_bigradedChainMinusPiece R hz)

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- The diagonal reflection of a knot grid preserves the bigraded `GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_transpose :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_transpose).mpr hG) K := by
  refine .of_semilinearMap (fun _ ↦ by simp [aeval_rename, Function.comp_def])
    (G.unblockedHomologyTransposeEquiv K).toLinearMap
    (G.unblockedHomologyTransposeEquiv K).bijective fun _ _ hy ↦ ?_
  -- The target piece is that of `hG.toOddComponentGridDiagram.transpose`: the two odd-component
  -- diagrams agree by definition (`IsKnot.transpose_toOddComponentGridDiagram`).
  change _ ∈ hG.toOddComponentGridDiagram.transpose.bigradedUnblockedHomologyPiece K _
  exact OddComponentGridDiagram.unblockedHomologyTransposeEquiv_mem_bigradedUnblockedHomologyPiece
    hG.toOddComponentGridDiagram K hy

/-- The diagonal reflection of a knot grid preserves `GH⁻` as an Alexander-graded
`K[U]`-module. -/
theorem unblockedHomologyIsomorphic_transpose :
    hG.UnblockedHomologyIsomorphic ((G.isKnot_transpose).mpr hG) K :=
  (hG.bigradedUnblockedHomologyIsomorphic_transpose K).unblockedHomologyIsomorphic

end GridDiagram.IsKnot

end TauCeti
