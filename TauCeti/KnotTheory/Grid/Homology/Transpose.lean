/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Transpose
public import TauCeti.KnotTheory.Grid.Homology.Tau

/-!
# The diagonal reflection on unblocked grid homology

The diagonal reflection carries a grid diagram `G` to `G.transpose` and its grid states to their
reflections, and it intertwines the unblocked differentials once the variables are renamed along
the permutation `G.O` (`Differential/Transpose.lean`). This file descends that symmetry to
unblocked grid homology: `GH⁻(G)` and `GH⁻(G.transpose)` are identified by a semilinear
equivalence along the renaming of the variables. The reflection preserves the `O`-Maslov and
Alexander gradings of grid states, so on chains it preserves the full bigrading, and on homology
it preserves the Alexander grading. Hence it preserves the invariant `τ` of a knot grid.

The reflection exchanges row and column commutations (`GridDiagram.isColumnCommutation_transpose`).
So, by `GridDiagram.IsCommutation.apply_eq_of_transpose`, the invariance of `τ` under row
commutations follows from `GridDiagram.IsKnot.tau_transpose` and its invariance under column
commutations.

## Main definitions

* `TauCeti.GridDiagram.unblockedHomologyTransposeEquiv`: the equivalence
  `GH⁻(G) ≃ GH⁻(G.transpose)` induced by the diagonal reflection, semilinear along the renaming of
  the variables by `G.O`.

## Main results

* `TauCeti.GridDiagram.unblockedHomologyTransposeEquiv_unblockedHomologyClass`,
  `TauCeti.GridDiagram.unblockedHomologyTransposeEquiv_symm_unblockedHomologyClass`: it and its
  inverse send the class of a cycle to the class of the reflected cycle.
* `TauCeti.OddComponentGridDiagram.unblockedHomologyTransposeEquiv_mem_piece`: it preserves the
  Alexander grading.
* `TauCeti.GridDiagram.IsKnot.tau_transpose`: the invariant `τ` is unchanged by the diagonal
  reflection.

## References

The symmetries of grid diagrams are in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3, unblocked grid homology is defined in Chapter 4.6, and `τ` in Chapter 6.
The construction adapts the half-turn symmetry of `TauCeti.KnotTheory.Grid.Homology.HalfTurn`
(`GridDiagram.unblockedHomologyRotateEquiv`, its grading preservation and
`GridDiagram.IsKnot.tau_rotate`) to the diagonal reflection.
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
            (G.unblockedDifferential_transpose_transposeRenameEquiv R) z.2⟩ :=
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
            (G.unblockedDifferential_transposeRenameEquiv R) w.2⟩ := by
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
    G.1.transposeRenameEquiv R c ∈ G.transpose.bigradedChainMinusPiece R g := by
  classical
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro x e he
  rw [GridDiagram.transposeRenameEquiv_apply,
    support_rename_of_injective G.1.O.toPerm.injective, Finset.mem_image] at he
  obtain ⟨e, he, rfl⟩ := he
  have hM := G.1.maslovOℤ_transpose x.transpose
  have hA := G.alexanderℤ_transpose x.transpose
  rw [GridState.transpose_transpose] at hM hA
  have hdegree : G.transpose.monomialBidegree x (e.mapDomain G.1.O.toPerm) =
      G.monomialBidegree x.transpose e := by
    apply Prod.ext <;>
      simp only [monomialBidegree_fst, monomialBidegree_snd, hM, hA,
        Finsupp.degree_mapDomain]
  rw [hdegree]
  exact hc x.transpose e he

/-- The diagonal reflection, including the renaming of the coefficient variables along `G.O`,
preserves the Alexander grading of unblocked chains. -/
theorem transposeRenameEquiv_mem_alexanderChainMinusPiece {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.transposeRenameEquiv R c ∈ G.transpose.alexanderChainMinusPiece R a := by
  classical
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  intro x e he
  rw [GridDiagram.transposeRenameEquiv_apply,
    support_rename_of_injective G.1.O.toPerm.injective, Finset.mem_image] at he
  obtain ⟨e, he, rfl⟩ := he
  have hx := G.alexanderℤ_transpose x.transpose
  rw [GridState.transpose_transpose] at hx
  rw [hx, Finsupp.degree_mapDomain]
  exact hc x.transpose e he

end Chains

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The equivalence induced by the diagonal reflection preserves the Alexander grading on
homology. -/
theorem unblockedHomologyTransposeEquiv_mem_piece {a : ℤ} {y : G.1.unblockedHomology R}
    (hy : y ∈ (G.alexanderUnblockedHomologyGrading R).piece a) :
    G.1.unblockedHomologyTransposeEquiv R y ∈
      (G.transpose.alexanderUnblockedHomologyGrading R).piece a :=
  G.unblockedHomologyEquivOfIntertwining_mem_piece R G.transpose _ _
    (fun _ _ hc => G.transposeRenameEquiv_mem_alexanderChainMinusPiece R hc) hy

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- The knot invariant `τ` is unchanged by the diagonal reflection of a grid diagram. -/
theorem tau_transpose : ((G.isKnot_transpose).mpr hG).tau K = hG.tau K := by
  refine (hG.tau_eq_of_semilinearMap K _ (fun p => ?_)
    (G.unblockedHomologyTransposeEquiv K).toLinearMap
    (G.unblockedHomologyTransposeEquiv K).bijective fun a y hy => ?_).symm
  · simp [aeval_rename, Function.comp_def]
  · rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
      ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff] at hy ⊢
    exact hG.toOddComponentGridDiagram.unblockedHomologyTransposeEquiv_mem_piece K hy

end GridDiagram.IsKnot

end TauCeti
