/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Grading.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Relation

/-!
# The half-turn on unblocked grid homology

The half-turn of the torus carries a grid diagram `G` to `G.rotate` and its grid states to their
images under `GridState.halfTurn`, and it intertwines the unblocked differentials once the
variables are renamed along `Fin.rev` (`Differential/HalfTurn.lean`). This file descends that
symmetry to unblocked grid homology: `GH⁻(G)` and `GH⁻(G.rotate)` are identified by a
semilinear equivalence along the renaming of the variables. On chains, and so on homology, the
half-turn preserves the full `O`-Maslov--Alexander bigrading, including the coefficient-variable
degrees. Hence for a knot grid the two homologies are isomorphic as bigraded `R[U]`-modules
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_rotate`), and so also as
Alexander-graded `R[U]`-modules (`GridDiagram.IsKnot.unblockedHomologyIsomorphic_rotate`).

## Main definitions

* `TauCeti.GridDiagram.unblockedHomologyRotateEquiv`: the equivalence `GH⁻(G) ≃ GH⁻(G.rotate)`
  induced by the half-turn, semilinear along the renaming of the variables by `Fin.revPerm`.

## Main results

* `TauCeti.GridDiagram.unblockedHomologyRotateEquiv_unblockedHomologyClass`,
  `TauCeti.GridDiagram.unblockedHomologyRotateEquiv_symm_unblockedHomologyClass`: it and its
  inverse send the class of a cycle to the class of the half-turned cycle.
* `TauCeti.OddComponentGridDiagram.halfTurnRenameEquiv_mem_bigradedChainMinusPiece`,
  `TauCeti.OddComponentGridDiagram.unblockedHomologyRotateEquiv_mem_bigradedUnblockedHomologyPiece`:
  the half-turn preserves the bigrading of unblocked chains and of `GH⁻`.
* `TauCeti.GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_rotate`,
  `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_rotate`: for a knot grid, `GH⁻` is
  unchanged by the half-turn as a bigraded, and so as an Alexander-graded, `R[U]`-module.

## References

The symmetries of grid diagrams are in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3, and unblocked grid homology is defined in Chapter 4.6.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- **The half-turn on `GH⁻`.** Moving grid states by the half-turn and renaming the variables
along `Fin.revPerm` induces an equivalence from `GH⁻(G)` to the unblocked homology of the
half-turned diagram `G.rotate`, semilinear along the renaming. -/
noncomputable def unblockedHomologyRotateEquiv :
    G.unblockedHomology R ≃ₛₗ[((renameEquiv R (Fin.revPerm (n := n))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] G.rotate.unblockedHomology R :=
  G.unblockedHomologyEquivOfIntertwining R _ (GridChain.halfTurnRenameEquiv R)
    (G.unblockedDifferential_rotate_halfTurnRenameEquiv R)

/-- The half-turn sends the class of a cycle `z` to the class of the half-turned cycle. -/
@[simp]
theorem unblockedHomologyRotateEquiv_unblockedHomologyClass
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyRotateEquiv R (G.unblockedHomologyClass R z) =
      G.rotate.unblockedHomologyClass R
        ⟨GridChain.halfTurnRenameEquiv R z,
          G.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_rotate_halfTurnRenameEquiv R) z.property⟩ :=
  G.unblockedHomologyEquivOfIntertwining_unblockedHomologyClass R _ _ _ z

/-- The inverse of the half-turn also moves the class of a cycle `w` of `GC⁻(G.rotate)` by the
half-turn, since the half-turn is an involution. -/
@[simp]
theorem unblockedHomologyRotateEquiv_symm_unblockedHomologyClass
    (w : LinearMap.ker (G.rotate.unblockedDifferential R)) :
    (G.unblockedHomologyRotateEquiv R).symm (G.rotate.unblockedHomologyClass R w) =
      G.unblockedHomologyClass R
        ⟨GridChain.halfTurnRenameEquiv R w,
          G.rotate.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_halfTurnRenameEquiv R) w.property⟩ := by
  rw [LinearEquiv.symm_apply_eq, unblockedHomologyRotateEquiv_unblockedHomologyClass]
  exact congrArg _ (Subtype.ext (GridChain.halfTurnRenameEquiv_halfTurnRenameEquiv R _).symm)

end GridDiagram

namespace OddComponentGridDiagram

section Chains

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

/-- The half-turn, including reversal of coefficient-variable indices, preserves the full
`O`-Maslov--Alexander bigrading of unblocked chains. -/
theorem halfTurnRenameEquiv_mem_bigradedChainMinusPiece {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    GridChain.halfTurnRenameEquiv R c ∈ G.rotate.bigradedChainMinusPiece R g := by
  classical
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro x e he
  rw [GridChain.halfTurnRenameEquiv_apply,
    support_rename_of_injective Fin.rev_injective, Finset.mem_image] at he
  obtain ⟨e, he, rfl⟩ := he
  have hM := G.val.maslovOℤ_rotate_halfTurn x.halfTurn
  have hA := G.alexanderℤ_rotate_halfTurn x.halfTurn
  rw [GridState.halfTurn_halfTurn] at hM hA
  have hdegree : G.rotate.monomialBidegree x (e.mapDomain Fin.rev) =
      G.monomialBidegree x.halfTurn e := by
    apply Prod.ext <;>
      simp only [monomialBidegree_fst, monomialBidegree_snd, hM, hA,
        Finsupp.degree_mapDomain]
  rw [hdegree]
  exact hc x.halfTurn e he

end Chains

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The equivalence induced by the half-turn preserves the `O`-Maslov--Alexander bigrading on
homology. -/
theorem unblockedHomologyRotateEquiv_mem_bigradedUnblockedHomologyPiece {g : ℤ × ℤ}
    {y : G.val.unblockedHomology R} (hy : y ∈ G.bigradedUnblockedHomologyPiece R g) :
    G.val.unblockedHomologyRotateEquiv R y ∈ G.rotate.bigradedUnblockedHomologyPiece R g := by
  obtain ⟨z, hz, rfl⟩ := (G.mem_bigradedUnblockedHomologyPiece_iff R).mp hy
  rw [GridDiagram.unblockedHomologyRotateEquiv_unblockedHomologyClass]
  exact G.rotate.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R
    (G.halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hz)

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- The half-turn of a knot grid preserves the bigraded `GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_rotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_rotate).mpr hG) K := by
  refine .of_semilinearMap (fun _ ↦ by simp [aeval_rename, Function.comp_def])
    (G.unblockedHomologyRotateEquiv K).toLinearMap
    (G.unblockedHomologyRotateEquiv K).bijective fun _ _ hy ↦ ?_
  -- The target piece is that of `hG.toOddComponentGridDiagram.rotate`: the two odd-component
  -- diagrams agree by definition (`IsKnot.rotate_toOddComponentGridDiagram`).
  change _ ∈ hG.toOddComponentGridDiagram.rotate.bigradedUnblockedHomologyPiece K _
  exact OddComponentGridDiagram.unblockedHomologyRotateEquiv_mem_bigradedUnblockedHomologyPiece
    hG.toOddComponentGridDiagram K hy

/-- The half-turn of a knot grid preserves `GH⁻` as an Alexander-graded `K[U]`-module. -/
theorem unblockedHomologyIsomorphic_rotate :
    hG.UnblockedHomologyIsomorphic ((G.isKnot_rotate).mpr hG) K :=
  (hG.bigradedUnblockedHomologyIsomorphic_rotate K).unblockedHomologyIsomorphic

end GridDiagram.IsKnot

end TauCeti
