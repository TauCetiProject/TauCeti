/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Grading.Basic

/-!
# The bidegree of the grid commutation map

The commutation map of a column turn `C` counts both terminal-side and initial-side pentagons.
The grading-change formulas of `Grading/Basic.lean` imply that both contributions raise the
bidegree of every monomial generator of `GC⁻` by the same amount, the bidegree
`GridDiagram.commutationBidegree C` of the turn: an `O`-marking raises the target state's Maslov and
Alexander gradings by `(2, 1)`, its renamed variable contributes `(-2, -1)`, and what remains is
the position of the turn row relative to the markings of the two exchanged columns.

For a column commutation the bidegree of the turn vanishes, so the terminal-side and initial-side
pentagon maps and their sum `GridDiagram.commutationMap` preserve the bigraded and the
Alexander-homogeneous chain pieces. For a turn exchanging two columns whose marking segments
interleave, the same maps are homogeneous of a possibly nonzero bidegree; these are the maps
attached to a crossing change in `TauCeti.KnotTheory.Grid.CrossingChange.Grading`.

These are grading statements over arbitrary commutative semirings, not chain-map or
homotopy-equivalence assertions. The integer Alexander grading requires an odd number of link
components, as in the existing unblocked bigrading API.

## Main results

* `TauCeti.OddComponentGridDiagram.pentagonMap_mem_bigradedChainMinusPiece_add`,
  `TauCeti.OddComponentGridDiagram.initialPentagonMap_mem_bigradedChainMinusPiece_add` and
  `TauCeti.OddComponentGridDiagram.commutationMap_mem_bigradedChainMinusPiece_add`: the pentagon
  maps of a column turn raise the bidegree by the bidegree of the turn.
* `TauCeti.OddComponentGridDiagram.pentagonMap_mem_alexanderChainMinusPiece_add`,
  `TauCeti.OddComponentGridDiagram.initialPentagonMap_mem_alexanderChainMinusPiece_add` and
  `TauCeti.OddComponentGridDiagram.commutationMap_mem_alexanderChainMinusPiece_add`: likewise for
  the Alexander grading alone.
* `TauCeti.OddComponentGridDiagram.commutationMap_mem_bigradedChainMinusPiece` and
  `TauCeti.OddComponentGridDiagram.commutationMap_mem_alexanderChainMinusPiece`, with their
  terminal-side and initial-side parts: for a column commutation these maps preserve the
  gradings.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 5.1 and 6.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The argument uses the state-grading formulas in
`TauCeti.KnotTheory.Grid.Commutation.Grading.Basic` and the polynomial-support API.
-/

public section

namespace TauCeti

open MvPolynomial

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

variable (C : GridDiagram.ColumnTurn n)

/-- Each terminal-side coefficient monomial compensates for the grading change of its target, up
to the bidegree of the turn. -/
private theorem monomialBidegree_mapDomain_add_of_mem_support_pentagonCoefficient
    (x y : GridState n) (w : Fin n →₀ ℕ) (hw : w ∈ (G.1.pentagonCoefficient R C x y).support)
    (d : Fin n →₀ ℕ) :
    (G.swapColumns C).monomialBidegree y
      (Finsupp.mapDomain (Equiv.swap C.column (finRotate n C.column)) d + w) =
      G.monomialBidegree x d + G.1.commutationBidegree C := by
  classical
  rw [GridDiagram.pentagonCoefficient_def] at hw
  obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
  rw [GridDiagram.pentagonWeight_eq_monomial] at hwP
  obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
  have hM := G.1.maslovOℤ_swapColumns_of_isEmpty C ((G.1.mem_pentagons P).mp hP).1
  have hA := G.alexanderℤ_swapColumns_of_mem_pentagons C hP
  exact G.monomialBidegree_mapDomain_add_sum_eq_add (G.swapColumns C) _ d _ _
    (by rw [val_swapColumns, hM]; ring) (by rw [hA]; ring)

/-- Each initial-side coefficient monomial compensates for the grading change of its target, up
to the bidegree of the turn. -/
private theorem monomialBidegree_mapDomain_add_of_mem_support_initialPentagonCoefficient
    (x y : GridState n) (w : Fin n →₀ ℕ)
    (hw : w ∈ (G.1.initialPentagonCoefficient R C x y).support) (d : Fin n →₀ ℕ) :
    (G.swapColumns C).monomialBidegree y
      (Finsupp.mapDomain (Equiv.swap C.column (finRotate n C.column)) d + w) =
      G.monomialBidegree x d + G.1.commutationBidegree C := by
  classical
  rw [GridDiagram.initialPentagonCoefficient_def] at hw
  obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
  rw [GridDiagram.initialPentagonWeight_eq_monomial] at hwP
  obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
  have hM := G.1.maslovOℤ_swapColumns_initialPentagon_of_isEmpty C
    ((G.1.mem_initialPentagons P).mp hP).1
  have hA := G.alexanderℤ_swapColumns_of_mem_initialPentagons C hP
  exact G.monomialBidegree_mapDomain_add_sum_eq_add (G.swapColumns C) _ d _ _
    (by rw [val_swapColumns, hM]; ring) (by rw [hA]; ring)

/-- **The bidegree of the pentagon map.** The pentagon map of a column turn `C` sends a chain of
`GC⁻(G)` that is homogeneous of bidegree `g` to a chain of `GC⁻` of the diagram with the two
columns of `C` exchanged that is homogeneous of bidegree `g + G.commutationBidegree C`. -/
theorem pentagonMap_mem_bigradedChainMinusPiece_add {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.pentagonMap R C c ∈
      (G.swapColumns C).bigradedChainMinusPiece R (g + G.1.commutationBidegree C) :=
  G.matrixMap_mem_bigradedChainMinusPiece_add R (G.swapColumns C) _ _ _
    (G.1.pentagonMap_apply_apply R C) _
    (G.monomialBidegree_mapDomain_add_of_mem_support_pentagonCoefficient R C) hc

/-- The pentagon map of a column turn `C` sends a chain of `GC⁻(G)` of Alexander degree `a` to a
chain of Alexander degree `a` plus the Alexander component of `G.commutationBidegree C`. -/
theorem pentagonMap_mem_alexanderChainMinusPiece_add {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.pentagonMap R C c ∈
      (G.swapColumns C).alexanderChainMinusPiece R (a + (G.1.commutationBidegree C).2) :=
  G.matrixMap_mem_alexanderChainMinusPiece_add R (G.swapColumns C) _ _ _
    (G.1.pentagonMap_apply_apply R C) _
    (fun x y w hw d => congrArg Prod.snd
      (G.monomialBidegree_mapDomain_add_of_mem_support_pentagonCoefficient R C x y w hw d)) hc

/-- The initial-side pentagon map of a column turn `C` raises the bidegree of homogeneous chains
by `G.commutationBidegree C`. -/
theorem initialPentagonMap_mem_bigradedChainMinusPiece_add {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.initialPentagonMap R C c ∈
      (G.swapColumns C).bigradedChainMinusPiece R (g + G.1.commutationBidegree C) :=
  G.matrixMap_mem_bigradedChainMinusPiece_add R (G.swapColumns C) _ _ _
    (G.1.initialPentagonMap_apply_apply R C) _
    (G.monomialBidegree_mapDomain_add_of_mem_support_initialPentagonCoefficient R C) hc

/-- The initial-side pentagon map of a column turn `C` raises the Alexander degree of homogeneous
chains by the Alexander component of `G.commutationBidegree C`. -/
theorem initialPentagonMap_mem_alexanderChainMinusPiece_add {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.initialPentagonMap R C c ∈
      (G.swapColumns C).alexanderChainMinusPiece R (a + (G.1.commutationBidegree C).2) :=
  G.matrixMap_mem_alexanderChainMinusPiece_add R (G.swapColumns C) _ _ _
    (G.1.initialPentagonMap_apply_apply R C) _
    (fun x y w hw d => congrArg Prod.snd
      (G.monomialBidegree_mapDomain_add_of_mem_support_initialPentagonCoefficient R C
        x y w hw d)) hc

/-- **The bidegree of the commutation map.** The commutation map of a column turn `C`, counting
both kinds of pentagon, sends a chain of `GC⁻(G)` homogeneous of bidegree `g` to a chain of `GC⁻`
of the diagram with the two columns of `C` exchanged of bidegree `g + G.commutationBidegree C`. -/
theorem commutationMap_mem_bigradedChainMinusPiece_add {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.commutationMap R C c ∈
      (G.swapColumns C).bigradedChainMinusPiece R (g + G.1.commutationBidegree C) := by
  rw [GridDiagram.commutationMap_apply]
  exact Submodule.add_mem _ (G.pentagonMap_mem_bigradedChainMinusPiece_add R C hc)
    (G.initialPentagonMap_mem_bigradedChainMinusPiece_add R C hc)

/-- The commutation map of a column turn `C` raises the Alexander degree of homogeneous chains by
the Alexander component of `G.commutationBidegree C`. -/
theorem commutationMap_mem_alexanderChainMinusPiece_add {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.commutationMap R C c ∈
      (G.swapColumns C).alexanderChainMinusPiece R (a + (G.1.commutationBidegree C).2) := by
  rw [GridDiagram.commutationMap_apply]
  exact Submodule.add_mem _ (G.pentagonMap_mem_alexanderChainMinusPiece_add R C hc)
    (G.initialPentagonMap_mem_alexanderChainMinusPiece_add R C hc)

/-! ### Column commutations -/

/-- **The pentagon map preserves the bigrading.** The pentagon map of a validated column
commutation `C` sends a chain of `GC⁻(G)` that is homogeneous of bidegree `g` to a chain of
`GC⁻` of the commuted diagram that is homogeneous of the same bidegree. -/
theorem pentagonMap_mem_bigradedChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.pentagonMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  simpa using G.pentagonMap_mem_bigradedChainMinusPiece_add R C hc

/-- **The pentagon map preserves the Alexander grading.** The pentagon map of a validated column
commutation `C` sends a chain of `GC⁻(G)` of Alexander degree `a` to a chain of `GC⁻` of the
commuted diagram of the same Alexander degree. -/
theorem pentagonMap_mem_alexanderChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.pentagonMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  simpa using G.pentagonMap_mem_alexanderChainMinusPiece_add R C hc

/-- The initial-side pentagon map sends a chain of `GC⁻(G)` homogeneous of bidegree `g` to a
chain of `GC⁻` of the commuted diagram homogeneous of the same bidegree. -/
theorem initialPentagonMap_mem_bigradedChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.initialPentagonMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  simpa using G.initialPentagonMap_mem_bigradedChainMinusPiece_add R C hc

/-- The initial-side pentagon map sends a chain of `GC⁻(G)` of Alexander degree `a` to a chain of
`GC⁻` of the commuted diagram of the same Alexander degree. -/
theorem initialPentagonMap_mem_alexanderChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.initialPentagonMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  simpa using G.initialPentagonMap_mem_alexanderChainMinusPiece_add R C hc

/-- The full commutation map, counting both kinds of pentagon, sends a chain of `GC⁻(G)`
homogeneous of bidegree `g` to a chain of `GC⁻` of the commuted diagram of the same bidegree. -/
theorem commutationMap_mem_bigradedChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.commutationMap R C c ∈ (G.swapColumns C).bigradedChainMinusPiece R g := by
  simpa using G.commutationMap_mem_bigradedChainMinusPiece_add R C hc

/-- The full commutation map, counting both kinds of pentagon, sends a chain of `GC⁻(G)` of
Alexander degree `a` to a chain of `GC⁻` of the commuted diagram of the same Alexander degree. -/
theorem commutationMap_mem_alexanderChainMinusPiece (C : GridDiagram.ColumnCommutationData G.1)
    (R : Type*) [CommSemiring R] {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.commutationMap R C c ∈ (G.swapColumns C).alexanderChainMinusPiece R a := by
  simpa using G.commutationMap_mem_alexanderChainMinusPiece_add R C hc

end OddComponentGridDiagram

end TauCeti
