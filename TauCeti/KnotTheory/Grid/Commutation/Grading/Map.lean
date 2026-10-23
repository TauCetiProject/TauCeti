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
terminal-side and initial-side pentagon maps and by their sum, `GridDiagram.commutationMap`.
These are grading statements over arbitrary commutative semirings, not chain-map or
homotopy-equivalence assertions.
The integer Alexander grading requires an odd number of link components, as in the existing
unblocked bigrading API.

## Main results

* `TauCeti.OddComponentGridDiagram.pentagonMap_mem_bigradedChainMinusPiece`
* `TauCeti.OddComponentGridDiagram.pentagonMap_mem_alexanderChainMinusPiece`
* `TauCeti.OddComponentGridDiagram.initialPentagonMap_mem_bigradedChainMinusPiece`
* `TauCeti.OddComponentGridDiagram.initialPentagonMap_mem_alexanderChainMinusPiece`
* `TauCeti.OddComponentGridDiagram.commutationMap_mem_bigradedChainMinusPiece`
* `TauCeti.OddComponentGridDiagram.commutationMap_mem_alexanderChainMinusPiece`

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The argument uses the state-grading formulas in
`TauCeti.KnotTheory.Grid.Commutation.Grading.Basic` and the polynomial-support API.
-/

public section

namespace TauCeti

open MvPolynomial

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

variable (C : GridDiagram.ColumnCommutationData G.1)

/-- Each terminal-side coefficient monomial compensates for the grading change of its target. -/
private theorem monomialBidegree_mapDomain_add_of_mem_support_pentagonCoefficient
    (x y : GridState n) (w : Fin n →₀ ℕ) (hw : w ∈ (G.1.pentagonCoefficient R C x y).support)
    (d : Fin n →₀ ℕ) :
    (G.swapColumns C).monomialBidegree y
      (Finsupp.mapDomain (Equiv.swap C.column (finRotate n C.column)) d + w) =
      G.monomialBidegree x d := by
  classical
  rw [GridDiagram.pentagonCoefficient_def] at hw
  obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
  rw [GridDiagram.pentagonWeight_eq_monomial] at hwP
  obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
  exact G.monomialBidegree_mapDomain_add_sum (G.swapColumns C) _ d _
    (by simpa only [val_swapColumns] using
      G.1.maslovOℤ_swapColumns_of_isEmpty C ((G.1.mem_pentagons P).mp hP).1)
    (G.alexanderℤ_swapColumns_of_mem_pentagons C hP)

/-- Each initial-side coefficient monomial compensates for the grading change of its target. -/
private theorem monomialBidegree_mapDomain_add_of_mem_support_initialPentagonCoefficient
    (x y : GridState n) (w : Fin n →₀ ℕ)
    (hw : w ∈ (G.1.initialPentagonCoefficient R C x y).support) (d : Fin n →₀ ℕ) :
    (G.swapColumns C).monomialBidegree y
      (Finsupp.mapDomain (Equiv.swap C.column (finRotate n C.column)) d + w) =
      G.monomialBidegree x d := by
  classical
  rw [GridDiagram.initialPentagonCoefficient_def] at hw
  obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
  rw [GridDiagram.initialPentagonWeight_eq_monomial] at hwP
  obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
  exact G.monomialBidegree_mapDomain_add_sum (G.swapColumns C) _ d _
    (by simpa only [val_swapColumns] using
      G.1.maslovOℤ_swapColumns_initialPentagon_of_isEmpty C
          ((G.1.mem_initialPentagons P).mp hP).1)
    (G.alexanderℤ_swapColumns_of_mem_initialPentagons C hP)

/-- **The pentagon map preserves the bigrading.** The pentagon map of a validated column
commutation `C` sends a chain of `GC⁻(G)` that is homogeneous of bidegree `g` to a chain of
`GC⁻` of the commuted diagram that is homogeneous of the same bidegree. -/
theorem pentagonMap_mem_bigradedChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.pentagonMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  exact G.matrixMap_mem_bigradedChainMinusPiece R (G.swapColumns C) _ _ _
    (G.1.pentagonMap_apply_apply R C)
    (G.monomialBidegree_mapDomain_add_of_mem_support_pentagonCoefficient R C) hc

/-- **The pentagon map preserves the Alexander grading.** The pentagon map of a validated column
commutation `C` sends a chain of `GC⁻(G)` of Alexander degree `a` to a chain of `GC⁻` of the
commuted diagram of the same Alexander degree. -/
theorem pentagonMap_mem_alexanderChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.pentagonMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  exact G.matrixMap_mem_alexanderChainMinusPiece R (G.swapColumns C) _ _ _
    (G.1.pentagonMap_apply_apply R C)
    (fun x y w hw d => congrArg Prod.snd
      (G.monomialBidegree_mapDomain_add_of_mem_support_pentagonCoefficient R C x y w hw d)) hc

/-- The initial-side pentagon map sends a chain of `GC⁻(G)` homogeneous of bidegree `g` to a
chain of `GC⁻` of the commuted diagram homogeneous of the same bidegree. -/
theorem initialPentagonMap_mem_bigradedChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.initialPentagonMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  exact G.matrixMap_mem_bigradedChainMinusPiece R (G.swapColumns C) _ _ _
    (G.1.initialPentagonMap_apply_apply R C)
    (G.monomialBidegree_mapDomain_add_of_mem_support_initialPentagonCoefficient R C) hc

/-- The initial-side pentagon map sends a chain of `GC⁻(G)` of Alexander degree `a` to a chain of
`GC⁻` of the commuted diagram of the same Alexander degree. -/
theorem initialPentagonMap_mem_alexanderChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.initialPentagonMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  exact G.matrixMap_mem_alexanderChainMinusPiece R (G.swapColumns C) _ _ _
    (G.1.initialPentagonMap_apply_apply R C)
    (fun x y w hw d => congrArg Prod.snd
      (G.monomialBidegree_mapDomain_add_of_mem_support_initialPentagonCoefficient R C
        x y w hw d)) hc

/-- The full commutation map, counting both kinds of pentagon, sends a chain of `GC⁻(G)`
homogeneous of bidegree `g` to a chain of `GC⁻` of the commuted diagram of the same bidegree. -/
theorem commutationMap_mem_bigradedChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.commutationMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  rw [GridDiagram.commutationMap_apply]
  exact Submodule.add_mem _ (G.pentagonMap_mem_bigradedChainMinusPiece C R hc)
    (G.initialPentagonMap_mem_bigradedChainMinusPiece C R hc)

/-- The full commutation map, counting both kinds of pentagon, sends a chain of `GC⁻(G)` of
Alexander degree `a` to a chain of `GC⁻` of the commuted diagram of the same Alexander degree. -/
theorem commutationMap_mem_alexanderChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.commutationMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  rw [GridDiagram.commutationMap_apply]
  exact Submodule.add_mem _ (G.pentagonMap_mem_alexanderChainMinusPiece C R hc)
    (G.initialPentagonMap_mem_alexanderChainMinusPiece C R hc)

end OddComponentGridDiagram

end TauCeti
