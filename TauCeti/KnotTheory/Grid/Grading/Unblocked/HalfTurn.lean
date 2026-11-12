/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Grading.HalfTurn
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain

/-!
# The half-turn on unblocked chain gradings

The half-turn on grid states, together with reversal of the coefficient-variable indices,
preserves the full `(O-Maslov, Alexander)` bigrading and the Alexander grading on unblocked
chains of odd-component diagrams. These chain comparisons descend to homology and to the
one-variable specialization used to compare the two stabilization corners.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 5.2.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

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
  have hM := G.1.maslovOℤ_rotate_halfTurn x.halfTurn
  have hA := G.alexanderℤ_rotate_halfTurn x.halfTurn
  rw [GridState.halfTurn_halfTurn] at hM hA
  have hdegree : G.rotate.monomialBidegree x (e.mapDomain Fin.rev) =
      G.monomialBidegree x.halfTurn e := by
    apply Prod.ext <;>
      simp only [monomialBidegree_fst, monomialBidegree_snd, hM, hA,
        Finsupp.degree_mapDomain]
  rw [hdegree]
  exact hc x.halfTurn e he

/-- The half-turn, including reversal of coefficient-variable indices, preserves the Alexander
grading of unblocked chains. -/
theorem halfTurnRenameEquiv_mem_alexanderChainMinusPiece {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    GridChain.halfTurnRenameEquiv R c ∈ G.rotate.alexanderChainMinusPiece R a := by
  classical
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  intro x e he
  rw [GridChain.halfTurnRenameEquiv_apply,
    support_rename_of_injective Fin.rev_injective, Finset.mem_image] at he
  obtain ⟨e, he, rfl⟩ := he
  have hx := G.alexanderℤ_rotate_halfTurn x.halfTurn
  rw [GridState.halfTurn_halfTurn] at hx
  rw [hx, Finsupp.degree_mapDomain]
  exact hc x.halfTurn e he

end Chains

end TauCeti.OddComponentGridDiagram
