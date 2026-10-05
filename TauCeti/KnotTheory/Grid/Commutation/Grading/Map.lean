/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Grading.Basic

/-!
# The full grid commutation map preserves the bigrading

The commutation map counts both terminal-side and initial-side pentagons. The grading-change
formulas of `Grading/Basic.lean` imply that both contributions preserve the bidegree of every
monomial generator of `GC⁻`: an `O`-marking raises the target state's Maslov and Alexander
gradings by `(2, 1)`, while its renamed variable contributes `(-2, -1)`.

This file proves preservation of the bigraded and Alexander-homogeneous chain pieces by the
initial-side pentagon map and by their sum, `GridDiagram.commutationMap`. These are grading
statements over arbitrary commutative semirings, not chain-map or homotopy-equivalence assertions.
The integer Alexander grading requires an odd number of link components, as in the existing
unblocked bigrading API.

## Main results

* `TauCeti.OddComponentGridDiagram.initialPentagonMap_mem_bigradedChainMinusPiece`
* `TauCeti.OddComponentGridDiagram.commutationMap_mem_bigradedChainMinusPiece`
* `TauCeti.OddComponentGridDiagram.commutationMap_mem_alexanderChainMinusPiece`

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The argument extends the terminal-side grading proof in
`TauCeti.KnotTheory.Grid.Commutation.Grading.Basic` using the same polynomial-support API.
-/

public section

namespace TauCeti

open MvPolynomial

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)
  (C : GridDiagram.ColumnCommutationData G.1) (R : Type*) [CommSemiring R]

/-- Every output monomial of the initial-side pentagon map has the bidegree of an input
monomial. -/
private theorem exists_monomialBidegree_eq_of_mem_support_initialPentagonMap
    {c : GridChainMinus R n} {y : GridState n} {e : Fin n →₀ ℕ}
    (he : e ∈ (G.1.initialPentagonMap R C c y).support) :
    ∃ x : GridState n, ∃ d ∈ (c x).support,
      (G.swapColumns C).monomialBidegree y e = G.monomialBidegree x d := by
  classical
  rw [GridDiagram.initialPentagonMap_apply_apply] at he
  obtain ⟨x, d, hd, w, hw, rfl⟩ := GridChain.exists_support_of_mem_support_sum_rename_mul
    R (Equiv.swap C.column (finRotate n C.column)) _ he
  rw [GridDiagram.initialPentagonCoefficient_def] at hw
  obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
  rw [GridDiagram.initialPentagonWeight_eq_monomial] at hwP
  obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
  refine ⟨x, d, hd, ?_⟩
  have hM := G.1.maslovOℤ_swapColumns_of_isEmpty_initial C
    ((G.1.mem_initialPentagons P).mp hP).1
  have hA := G.alexanderℤ_swapColumns_of_mem_initialPentagons C hP
  have hdeg : ((Finsupp.mapDomain (Equiv.swap C.column (finRotate n C.column)) d +
      ∑ c ∈ G.1.OColumnsOfSquares P.coveredSquares,
        Finsupp.single (M := ℕ) (Equiv.swap C.column (finRotate n C.column) c) 1).degree : ℤ) =
      (d.degree : ℤ) + ((G.1.OColumnsOfSquares P.coveredSquares).card : ℤ) := by
    rw [map_add, map_sum, Finsupp.degree_mapDomain]
    simp
  refine Prod.ext ?_ ?_
  · simp only [monomialBidegree_fst, val_swapColumns, hdeg, hM]
    ring
  · simp only [monomialBidegree_snd, hdeg, hA]
    ring

/-- The initial-side pentagon map preserves the `O`-Maslov/Alexander bigrading of `GC⁻`. -/
theorem initialPentagonMap_mem_bigradedChainMinusPiece {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.initialPentagonMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro y e he
  obtain ⟨x, d, hd, h⟩ := G.exists_monomialBidegree_eq_of_mem_support_initialPentagonMap C R he
  rw [h, hc x d hd]

/-- The initial-side pentagon map preserves the Alexander grading of `GC⁻`. -/
theorem initialPentagonMap_mem_alexanderChainMinusPiece {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.initialPentagonMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  intro y e he
  obtain ⟨x, d, hd, h⟩ := G.exists_monomialBidegree_eq_of_mem_support_initialPentagonMap C R he
  rw [← monomialBidegree_snd, h, monomialBidegree_snd, hc x d hd]

/-- The full commutation map, counting both kinds of pentagon, preserves the bigrading of
`GC⁻`. -/
theorem commutationMap_mem_bigradedChainMinusPiece {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.commutationMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  rw [GridDiagram.commutationMap_apply]
  exact Submodule.add_mem _ (G.pentagonMap_mem_bigradedChainMinusPiece C R hc)
    (G.initialPentagonMap_mem_bigradedChainMinusPiece C R hc)

/-- The full commutation map, counting both kinds of pentagon, preserves the Alexander grading
of `GC⁻`. -/
theorem commutationMap_mem_alexanderChainMinusPiece {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.commutationMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  rw [GridDiagram.commutationMap_apply]
  exact Submodule.add_mem _ (G.pentagonMap_mem_alexanderChainMinusPiece C R hc)
    (G.initialPentagonMap_mem_alexanderChainMinusPiece C R hc)

end OddComponentGridDiagram

end TauCeti
