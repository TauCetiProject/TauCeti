/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Relabeling
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The unblocked grid differential under the half-turn

Rotating a planar grid diagram by a half-turn is an isotopy of the link it draws, and it
preserves the convention that vertical segments cross over horizontal ones. On the torus the
half-turn moves the square named by its lower-left corner `(c, r)` to the square named by
`(c.rev, r.rev)`, which is `GridDiagram.rotate`, and it moves the grid point `(c, r)` to the grid
point with both coordinates negated modulo `n`, which is `GridState.halfTurn`. A half-turn
exchanges the south-west and north-east corners of a rectangle (and likewise the north-west and
south-east ones), so the pair of corners lying on the source state is again the south-west and
north-east pair. It therefore carries the rectangles counted by the unblocked differential of
`G` to those counted by the unblocked differential of `G.rotate`
(`GridRectangleBetween.halfTurnEquiv`), together with the markings they cover.

The variables `V_c` of `GC⁻` are indexed by the columns of the `O`-markings, and the half-turn
moves the `O`-marking of column `c` to column `c.rev`. So the map on `GC⁻` that moves each grid
state by `GridState.halfTurn` and renames the variables along `Fin.revPerm`
(`GridChain.halfTurnRenameEquiv`) intertwines the unblocked differentials of `G` and of
`G.rotate`.

## Main definitions

* `TauCeti.GridChain.halfTurnRenameEquiv`: the semilinear equivalence on `GC⁻` that moves grid
  states by the half-turn and renames the coefficient variables along `Fin.revPerm`.

## Main results

* `TauCeti.GridDiagram.unblockedCoefficient_rotate_halfTurn`: the matrix coefficients of the
  unblocked differential of `G.rotate` are the renamed coefficients of that of `G`.
* `TauCeti.GridDiagram.unblockedDifferential_rotate_halfTurnRenameEquiv`,
  `TauCeti.GridDiagram.unblockedDifferential_halfTurnRenameEquiv`: the half-turn
  intertwines the unblocked differentials of `G` and of `G.rotate`, in both directions.
* `TauCeti.GridChain.halfTurnRenameEquiv_halfTurnRenameEquiv`: the half-turn of chains is an
  involution.

## References

The symmetries of grid diagrams, among them the half-turn, are in Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 3; the unblocked complex is defined in Chapter 4.6.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridChain

variable {n : ℕ} (R : Type*) [CommSemiring R]

/-- The semilinear equivalence on `GC⁻` induced by the half-turn: it moves every grid state by
`GridState.halfTurn` and renames the coefficient variables along `Fin.revPerm`, the column
permutation by which `GridDiagram.rotate` moves the `O`-markings. -/
noncomputable def halfTurnRenameEquiv :
    GridChainMinus R n ≃ₛₗ[((renameEquiv R (Fin.revPerm (n := n))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] GridChainMinus R n :=
  (Finsupp.mapRange.linearEquiv
    (renameEquiv R (Fin.revPerm (n := n))).toRingEquiv.toSemilinearEquiv).trans
    (Finsupp.domLCongr (Function.Involutive.toPerm _ GridState.halfTurn_involutive))

/-- The coefficient of a half-turned chain at a state is the renamed coefficient at the
half-turned state. -/
@[simp]
theorem halfTurnRenameEquiv_apply (c : GridChainMinus R n) (y : GridState n) :
    halfTurnRenameEquiv R c y = rename Fin.rev (c y.halfTurn) := by
  rw [halfTurnRenameEquiv]
  rfl

/-- The half-turn sends a generator with coefficient `a` to the half-turned generator with the
renamed coefficient. -/
@[simp]
theorem halfTurnRenameEquiv_single (x : GridState n) (a : MvPolynomial (Fin n) R) :
    halfTurnRenameEquiv R (Finsupp.single x a) = Finsupp.single x.halfTurn (rename Fin.rev a) := by
  ext y : 1
  rw [halfTurnRenameEquiv_apply]
  simp only [Finsupp.single_apply, GridState.halfTurn_involutive.eq_iff]
  split_ifs <;> simp

/-- The half-turn of chains is an involution. -/
@[simp]
theorem halfTurnRenameEquiv_halfTurnRenameEquiv (c : GridChainMinus R n) :
    halfTurnRenameEquiv R (halfTurnRenameEquiv R c) = c := by
  ext y : 1
  rw [halfTurnRenameEquiv_apply, halfTurnRenameEquiv_apply, GridState.halfTurn_halfTurn,
    rename_rename, Fin.rev_involutive.comp_self, rename_id_apply]

end GridChain

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

open GridRectangleBetween

/-- The half-turn preserves and reflects `X`-avoidance of a rectangle. -/
theorem disjoint_XSet_rotate_halfTurnEquiv {x y : GridState n} (r : GridRectangleBetween x y) :
    Disjoint (halfTurnEquiv x y r).toGridRectangle.coveredSquares G.rotate.XSet ↔
      Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  simp only [Finset.disjoint_left, Prod.forall, mem_coveredSquares_halfTurnEquiv, mem_XSet_rotate]
  constructor
  · intro h c r hc
    simpa using h c.rev r.rev (by simpa using hc)
  · intro h c r hc
    exact h _ _ hc

/-- The half-turn identifies the rectangles counted by the unblocked differentials of `G` and of
`G.rotate`. -/
theorem mem_unblockedRectangles_rotate_halfTurnEquiv {x y : GridState n}
    (r : GridRectangleBetween x y) :
    halfTurnEquiv x y r ∈ G.rotate.unblockedRectangles x.halfTurn y.halfTurn ↔
      r ∈ G.unblockedRectangles x y := by
  simp only [mem_unblockedRectangles, isEmpty_halfTurnEquiv, disjoint_XSet_rotate_halfTurnEquiv]

/-- The half-turn moves the `O`-columns a rectangle covers by `Fin.rev`. -/
@[simp]
theorem OColumns_rotate_halfTurnEquiv {x y : GridState n} (r : GridRectangleBetween x y) :
    G.rotate.OColumns (halfTurnEquiv x y r).toGridRectangle =
      (G.OColumns r.toGridRectangle).map Fin.revPerm.toEmbedding := by
  ext c
  simp only [mem_OColumns, mem_coveredSquares_halfTurnEquiv, rotate_O, GridState.rotate_apply,
    Fin.rev_rev, Finset.mem_map_equiv, Fin.revPerm_symm, Fin.revPerm_apply]

variable (R : Type*) [CommSemiring R]

/-- The half-turn renames the variables in the weight of a rectangle along `Fin.rev`. -/
@[simp]
theorem OMonomial_rotate_halfTurnEquiv {x y : GridState n} (r : GridRectangleBetween x y) :
    G.rotate.OMonomial R (halfTurnEquiv x y r).toGridRectangle =
      rename Fin.rev (G.OMonomial R r.toGridRectangle) := by
  rw [OMonomial_eq_monomial, OMonomial_eq_monomial, OColumns_rotate_halfTurnEquiv,
    rename_monomial, Finset.sum_map, Finsupp.mapDomain_finsetSum]
  simp only [Equiv.coe_toEmbedding, Finsupp.mapDomain_single, Fin.revPerm_apply]

/-- The half-turn renames the variables in the matrix coefficients of the unblocked
differential: those of `G.rotate` between half-turned states are those of `G`, renamed along
`Fin.rev`. -/
@[simp]
theorem unblockedCoefficient_rotate_halfTurn (x y : GridState n) :
    G.rotate.unblockedCoefficient R x.halfTurn y.halfTurn =
      rename Fin.rev (G.unblockedCoefficient R x y) := by
  rw [unblockedCoefficient_def, unblockedCoefficient_def, map_sum]
  refine (Finset.sum_equiv (halfTurnEquiv x y)
    (fun r => (G.mem_unblockedRectangles_rotate_halfTurnEquiv r).symm) fun r _ => ?_).symm
  rw [OMonomial_rotate_halfTurnEquiv]

/-- **The half-turn is a symmetry of `GC⁻`.** Moving grid states by the half-turn and renaming
the variables along `Fin.rev` intertwines the unblocked differentials of `G` and of
`G.rotate`. -/
theorem unblockedDifferential_rotate_comp_halfTurnRenameEquiv :
    (G.rotate.unblockedDifferential R).comp (GridChain.halfTurnRenameEquiv R).toLinearMap =
      (GridChain.halfTurnRenameEquiv R).toLinearMap.comp (G.unblockedDifferential R) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.halfTurn = y := ⟨y.halfTurn, GridState.halfTurn_halfTurn y⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    GridChain.halfTurnRenameEquiv_single, map_one, unblockedDifferential_single_apply,
    GridChain.halfTurnRenameEquiv_apply, GridState.halfTurn_halfTurn,
    unblockedCoefficient_rotate_halfTurn]

/-- The half-turn intertwines the unblocked differentials of `G` and of `G.rotate`,
pointwise. -/
@[simp]
theorem unblockedDifferential_rotate_halfTurnRenameEquiv (c : GridChainMinus R n) :
    G.rotate.unblockedDifferential R (GridChain.halfTurnRenameEquiv R c) =
      GridChain.halfTurnRenameEquiv R (G.unblockedDifferential R c) :=
  LinearMap.congr_fun (G.unblockedDifferential_rotate_comp_halfTurnRenameEquiv R) c

/-- Since the half-turn is an involution, it also intertwines the unblocked differentials of
`G.rotate` and of `G`. -/
theorem unblockedDifferential_halfTurnRenameEquiv (c : GridChainMinus R n) :
    G.unblockedDifferential R (GridChain.halfTurnRenameEquiv R c) =
      GridChain.halfTurnRenameEquiv R (G.rotate.unblockedDifferential R c) := by
  simpa only [rotate_rotate] using G.rotate.unblockedDifferential_rotate_halfTurnRenameEquiv R c

end GridDiagram

end TauCeti
