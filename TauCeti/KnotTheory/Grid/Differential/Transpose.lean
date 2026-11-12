/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The unblocked grid differential under the diagonal reflection

Reflecting a grid diagram across the main diagonal (`GridDiagram.transpose`) exchanges its rows
and columns. It reflects grid states (`GridState.transpose`), and the reflection of a rectangle
from `x` to `y` is a rectangle from `x.transpose` to `y.transpose`
(`GridRectangleBetween.transpose`): the reflection fixes the south-west and north-east corners of
a rectangle, so the corners lying on the source state stay the south-west and north-east pair.
It preserves emptiness, and it carries the markings a rectangle covers to the reflected markings.

The variables `V_c` of `GC⁻` are indexed by the columns of the `O`-markings. The `O`-marking of
`G` in column `c` lies in row `G.O c`, and its reflection is the `O`-marking of `G.transpose` in
column `G.O c`. So the map on `GC⁻` that reflects each grid state and renames the variables along
the permutation `G.O` (`GridDiagram.transposeRenameEquiv`) intertwines the unblocked differentials
of `G` and of `G.transpose`. Unlike the half-turn, the renaming depends on the diagram, and the
inverse map is the one attached to `G.transpose`.

Reflecting in the diagonal and exchanging which segments cross over turns the planar link diagram
into its image under a half-turn of space about the diagonal, so `G.transpose` presents the link
of `G` with its orientation reversed. This file does not use that interpretation. Its role is
combinatorial: the reflection exchanges row and column commutations
(`GridDiagram.isColumnCommutation_transpose`), so it transports commutation invariance from
columns to rows.

## Main definitions

* `TauCeti.GridDiagram.transposeRenameEquiv`: the semilinear equivalence on `GC⁻` that reflects
  grid states and renames the coefficient variables along `G.O`.

## Main results

* `TauCeti.GridDiagram.unblockedCoefficient_transpose`: the matrix coefficients of the unblocked
  differential of `G.transpose` are the renamed coefficients of that of `G`.
* `TauCeti.GridDiagram.unblockedDifferential_transpose_transposeRenameEquiv`,
  `TauCeti.GridDiagram.unblockedDifferential_transposeRenameEquiv`: the reflection intertwines the
  unblocked differentials of `G` and of `G.transpose`, in both directions.
* `TauCeti.GridDiagram.transposeRenameEquiv_transpose_transposeRenameEquiv`,
  `TauCeti.GridDiagram.transposeRenameEquiv_symm_apply`: the reflection of `G.transpose` is the
  inverse of that of `G`.

## References

The symmetries of grid diagrams are in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3; the unblocked complex is defined in Chapter 4.6. The fully blocked version of
this symmetry is `GridDiagram.fullyBlockedDifferential_transpose`. The construction adapts the
half-turn symmetry of `TauCeti.KnotTheory.Grid.Differential.HalfTurn`
(`GridChain.halfTurnRenameEquiv` and `GridDiagram.unblockedCoefficient_rotate_halfTurn`),
replacing its fixed variable reversal by the diagram-dependent renaming along `G.O`.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The semilinear equivalence on `GC⁻` induced by the diagonal reflection of `G`: it reflects
every grid state by `GridState.transpose` and renames the coefficient variables along `G.O`, the
permutation by which `G.transpose` moves the `O`-markings to new columns. -/
noncomputable def transposeRenameEquiv :
    GridChainMinus R n ≃ₛₗ[((renameEquiv R G.O.toPerm).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] GridChainMinus R n :=
  (Finsupp.mapRange.linearEquiv
    (renameEquiv R G.O.toPerm).toRingEquiv.toSemilinearEquiv).trans
    (GridChain.transposeEquiv (MvPolynomial (Fin n) R) n)

/-- The coefficient of a reflected chain at a state is the renamed coefficient at the reflected
state. -/
@[simp]
theorem transposeRenameEquiv_apply (c : GridChainMinus R n) (y : GridState n) :
    G.transposeRenameEquiv R c y = rename G.O.toPerm (c y.transpose) := by
  rw [transposeRenameEquiv, LinearEquiv.trans_apply, GridChain.transposeEquiv_apply,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply,
    RingEquiv.toSemilinearEquiv_apply, AlgEquiv.coe_toRingEquiv, renameEquiv_apply]

/-- The reflection sends a generator with coefficient `a` to the reflected generator with the
renamed coefficient. -/
@[simp]
theorem transposeRenameEquiv_single (x : GridState n) (a : MvPolynomial (Fin n) R) :
    G.transposeRenameEquiv R (Finsupp.single x a) =
      Finsupp.single x.transpose (rename G.O.toPerm a) := by
  have hinv : Function.Involutive (GridState.transpose (n := n)) := GridState.transpose_transpose
  ext y : 1
  rw [transposeRenameEquiv_apply]
  simp only [Finsupp.single_apply, ← hinv.eq_iff]
  split_ifs <;> simp

/-- Reflecting `G.transpose` undoes the reflection of `G`: the renaming along `G.transpose.O`
inverts the renaming along `G.O`. -/
@[simp]
theorem transposeRenameEquiv_transpose_transposeRenameEquiv (c : GridChainMinus R n) :
    G.transpose.transposeRenameEquiv R (G.transposeRenameEquiv R c) = c := by
  ext y : 1
  rw [transposeRenameEquiv_apply, transposeRenameEquiv_apply, GridState.transpose_transpose,
    rename_rename, transpose_O]
  exact (congrArg (rename · (c y)) (G.O.toPerm.symm_comp_self)).trans (rename_id_apply _)

/-- The inverse of the reflection of `G` is the reflection of `G.transpose`. -/
@[simp]
theorem transposeRenameEquiv_symm_apply (c : GridChainMinus R n) :
    (G.transposeRenameEquiv R).symm c = G.transpose.transposeRenameEquiv R c := by
  rw [LinearEquiv.symm_apply_eq]
  -- `G.transpose.transpose` is `G` by definition, so the involution law applies as stated.
  exact (G.transpose.transposeRenameEquiv_transpose_transposeRenameEquiv R c).symm

open GridRectangleBetween

omit R in
/-- The reflection preserves and reflects `X`-avoidance of a rectangle. -/
theorem disjoint_XSet_transpose {x y : GridState n} (r : GridRectangleBetween x y) :
    Disjoint r.transpose.toGridRectangle.coveredSquares G.transpose.XSet ↔
      Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  rw [transpose_toGridRectangle, GridRectangle.coveredSquares_transpose, transpose_XSet,
    Finset.disjoint_image Prod.swap_injective]

omit R in
/-- The reflection identifies the rectangles counted by the unblocked differentials of `G` and of
`G.transpose`. -/
theorem mem_unblockedRectangles_transpose {x y : GridState n} (r : GridRectangleBetween x y) :
    r.transpose ∈ G.transpose.unblockedRectangles x.transpose y.transpose ↔
      r ∈ G.unblockedRectangles x y := by
  simp only [mem_unblockedRectangles, isEmpty_transpose, disjoint_XSet_transpose]

omit R in
/-- The reflection moves the `O`-columns a rectangle covers along `G.O`. -/
@[simp]
theorem OColumns_transpose (r : GridRectangle n) :
    G.transpose.OColumns r.transpose = (G.OColumns r).map G.O.toPerm.toEmbedding := by
  ext c
  obtain ⟨d, rfl⟩ := G.O.toPerm.surjective c
  have h : (G.O.toPerm d, G.transpose.O (G.O.toPerm d)) = Prod.swap (d, G.O d) := by
    rw [transpose_O, GridState.transpose_apply, Equiv.symm_apply_apply, Prod.swap_prod_mk]
    -- `rw` closes the goal by `rfl`: `G.O d` is `G.O.toPerm d` by the `CoeFun` instance.
  rw [mem_OColumns, GridRectangle.coveredSquares_transpose, h,
    Prod.swap_injective.mem_finset_image, Finset.mem_map_equiv, Equiv.symm_apply_apply,
    mem_OColumns]

/-- The reflection renames the variables in the weight of a rectangle along `G.O`. -/
@[simp]
theorem OMonomial_transpose (r : GridRectangle n) :
    G.transpose.OMonomial R r.transpose = rename G.O.toPerm (G.OMonomial R r) := by
  rw [OMonomial_eq_monomial, OMonomial_eq_monomial, OColumns_transpose, rename_monomial,
    Finset.sum_map, Finsupp.mapDomain_finsetSum]
  simp only [Equiv.coe_toEmbedding, Finsupp.mapDomain_single]

/-- The reflection renames the variables in the matrix coefficients of the unblocked
differential: those of `G.transpose` between reflected states are those of `G`, renamed along
`G.O`. -/
@[simp]
theorem unblockedCoefficient_transpose (x y : GridState n) :
    G.transpose.unblockedCoefficient R x.transpose y.transpose =
      rename G.O.toPerm (G.unblockedCoefficient R x y) := by
  rw [unblockedCoefficient_def, unblockedCoefficient_def, map_sum]
  refine (Finset.sum_equiv (transposeEquiv x y)
    (fun r => (G.mem_unblockedRectangles_transpose r).symm) fun r _ => ?_).symm
  rw [transposeEquiv_apply, transpose_toGridRectangle, OMonomial_transpose]

/-- **The diagonal reflection is a symmetry of `GC⁻`.** Reflecting grid states and renaming the
variables along `G.O` intertwines the unblocked differentials of `G` and of `G.transpose`. -/
theorem unblockedDifferential_transpose_comp_transposeRenameEquiv :
    (G.transpose.unblockedDifferential R).comp (G.transposeRenameEquiv R).toLinearMap =
      (G.transposeRenameEquiv R).toLinearMap.comp (G.unblockedDifferential R) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.transpose = y := ⟨y.transpose, GridState.transpose_transpose y⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    transposeRenameEquiv_single, map_one, unblockedDifferential_single_apply,
    transposeRenameEquiv_apply, GridState.transpose_transpose, unblockedCoefficient_transpose]

/-- The reflection intertwines the unblocked differentials of `G` and of `G.transpose`,
pointwise. -/
@[simp]
theorem unblockedDifferential_transpose_transposeRenameEquiv (c : GridChainMinus R n) :
    G.transpose.unblockedDifferential R (G.transposeRenameEquiv R c) =
      G.transposeRenameEquiv R (G.unblockedDifferential R c) :=
  LinearMap.congr_fun (G.unblockedDifferential_transpose_comp_transposeRenameEquiv R) c

/-- The reflection of `G.transpose` intertwines the unblocked differentials of `G.transpose` and
of `G`. -/
theorem unblockedDifferential_transposeRenameEquiv (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.transpose.transposeRenameEquiv R c) =
      G.transpose.transposeRenameEquiv R (G.transpose.unblockedDifferential R c) := by
  simpa only [transpose_transpose] using
    G.transpose.unblockedDifferential_transpose_transposeRenameEquiv R c

end GridDiagram

end TauCeti
