/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Residual.Assembly

/-!
# The fully blocked commutation chain map

Setting every marking variable to zero in the pentagon-counting map retains exactly the empty
pentagons avoiding both kinds of markings. Both terminal-side and initial-side pentagons
contribute. The resulting map is linear over the coefficient semiring: the variable permutation
in the unblocked map disappears under constant coefficients.

`GridDiagram.fullyBlockedCommutationMap_mapRange_constantCoeff` expresses this specialization on
arbitrary chains. Over `ZMod 2`,
`GridDiagram.fullyBlockedCommutationMap_comp_fullyBlockedDifferential` proves that it is a chain map
between the fully blocked complexes. These statements specify the
map; invertibility on homology additionally needs the hexagon homotopy identities.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.4 and 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]
  (C : ColumnCommutationData G)

/-- A terminal-side pentagon contributes a constant term precisely when it covers no `O`-marking.
Its `X`-avoidance is imposed separately by membership in `pentagons`. -/
@[simp]
theorem constantCoeff_pentagonWeight {x y : GridState n}
    (P : GridPentagonBetween C.column C.turnRow x y) :
    constantCoeff (G.pentagonWeight R C P) =
      if G.pentagonOColumns C P = ∅ then 1 else 0 := by
  classical
  simp [G.pentagonWeight_eq_monomial R C P, constantCoeff_monomial,
    Finset.sum_eq_zero_iff, Finset.eq_empty_iff_forall_notMem]

/-- An initial-side pentagon contributes a constant term precisely when it covers no
`O`-marking. -/
@[simp]
theorem constantCoeff_initialPentagonWeight {x y : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    constantCoeff (G.initialPentagonWeight R C P) =
      if G.OColumnsOfSquares P.coveredSquares = ∅ then 1 else 0 := by
  classical
  simp [G.initialPentagonWeight_eq_monomial R C P, constantCoeff_monomial,
    Finset.sum_eq_zero_iff, Finset.eq_empty_iff_forall_notMem]

/-- The constant coefficient counts the pentagons of both kinds which also avoid every
`O`-marking. The counted sets already impose emptiness and avoidance of all `X`-markings. -/
@[simp]
theorem constantCoeff_commutationPentagonCoefficient (x y : GridState n) :
    constantCoeff (G.commutationPentagonCoefficient R C x y) =
      (((G.pentagons C x y).filter fun P => G.pentagonOColumns C P = ∅).card : R) +
      (((G.initialPentagons C x y).filter fun P =>
        G.OColumnsOfSquares P.coveredSquares = ∅).card : R) := by
  classical
  simp [commutationPentagonCoefficient_def, pentagonCoefficient_def,
    initialPentagonCoefficient_def, map_sum]

/-- The fully blocked commutation map: its matrix entries are the constant coefficients of the
unblocked pentagon coefficients. It counts empty pentagons carrying neither `X` nor `O` markings,
over any commutative coefficient semiring. -/
noncomputable def fullyBlockedCommutationMap : GridChain R n →ₗ[R] GridChain R n :=
  (G.commutationMap R C).constantCoeffReduction

/-- On a single generator, the fully blocked map reads the constant pentagon coefficient. -/
theorem fullyBlockedCommutationMap_single_apply (x y : GridState n) (r : R) :
    G.fullyBlockedCommutationMap R C (Finsupp.single x r) y =
      r * constantCoeff (G.commutationPentagonCoefficient R C x y) := by
  rw [fullyBlockedCommutationMap, LinearMap.constantCoeffReduction_single_apply,
    G.commutationMap_single_apply]

/-- On an arbitrary chain, the fully blocked map multiplies by the matrix of constant pentagon
coefficients. -/
@[simp]
theorem fullyBlockedCommutationMap_apply_apply (c : GridChain R n) (y : GridState n) :
    G.fullyBlockedCommutationMap R C c y =
      c.sum fun x r => r * constantCoeff (G.commutationPentagonCoefficient R C x y) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd, Finsupp.sum_add_index', add_mul]
  | single x r =>
    rw [fullyBlockedCommutationMap_single_apply, Finsupp.sum_single_index (by simp)]

/-- Taking constant coefficients commutes with the commutation map. In particular, the
semilinear variable swap of the unblocked map becomes an ordinary linear map after blocking. -/
@[simp]
theorem fullyBlockedCommutationMap_mapRange_constantCoeff (c : GridChainMinus R n) :
    G.fullyBlockedCommutationMap R C (c.mapRange constantCoeff (map_zero _)) =
      (G.commutationMap R C c).mapRange constantCoeff (map_zero _) := by
  exact LinearMap.constantCoeffReduction_mapRange_constantCoeff (G.commutationMap R C) c
    (fun p => constantCoeff_rename _ p)

/-- The pentagon map after blocking all marking variables intertwines the fully blocked
differentials. -/
theorem fullyBlockedCommutationMap_comp_fullyBlockedDifferential :
    G.fullyBlockedCommutationMap (ZMod 2) C ∘ₗ G.fullyBlockedDifferential =
      (G.swapColumns C.column (finRotate n C.column)).fullyBlockedDifferential ∘ₗ
        G.fullyBlockedCommutationMap (ZMod 2) C := by
  apply LinearMap.eq_of_mapRange_constantCoeff _ _ (f :=
    (G.commutationMap (ZMod 2) C).comp (G.unblockedDifferential (ZMod 2))) (f' :=
    ((G.swapColumns C.column (finRotate n C.column)).unblockedDifferential (ZMod 2)).comp
      (G.commutationMap (ZMod 2) C))
  · intro c
    simp only [LinearMap.comp_apply, fullyBlockedDifferential_mapRange_constantCoeff,
      fullyBlockedCommutationMap_mapRange_constantCoeff]
  · intro c
    simp only [LinearMap.comp_apply, fullyBlockedCommutationMap_mapRange_constantCoeff,
      fullyBlockedDifferential_mapRange_constantCoeff]
  · exact G.commutationMap_comp_unblockedDifferential C (ZMod 2)

end TauCeti.GridDiagram
