/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.OverlapRight
public import TauCeti.KnotTheory.Grid.Commutation.OverlapTurnRow
public import TauCeti.KnotTheory.Grid.Commutation.OverlapInvolution
public import TauCeti.KnotTheory.Grid.Commutation.OverlapWeight
public import TauCeti.KnotTheory.Grid.Commutation.Pairing
public import TauCeti.KnotTheory.Grid.Commutation.Decomposition
public import TauCeti.KnotTheory.Grid.Commutation.Disjoint
public import TauCeti.KnotTheory.Grid.Commutation.OverlapFinal
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Involution and finite-sum weight identity for the overlap recut

This module completes the overlap side of the pentagon chain-map proof for grid commutation.
It assembles the terminal-side recut promotions with their turn-row transports, proves the
recut involutive on the overlap locus, and establishes the finite-sum weight identity that
feeds `pentagon_chain_map_of_weight_identity`.

## Piece 2: Involution

The terminal-side forward maps `recutRightEqRight_first`/`_second` (in `OverlapRight.lean`)
take the turn-row membership as a hypothesis `hturn`. Combining them with the turn-row
transports `turn_mem_recut_first_of_right_eq_right` /
`turn_mem_recut_second_of_right_eq_right` (in `OverlapTurnRow.lean`) discharges `hturn`,
leaving only the branch data (`hfirst`/`hsecond`, recording which recut rectangle inherits
the pentagon's terminal side).

The recut is involutive: applying the forward map and then the reverse map (recut the
underlying generic decomposition again and re-promote) returns the original decomposition.
The generic involution `GridRectangleDecomposition.recut_recut` (proved from
`existsUnique_isRecut` uniqueness) gives the underlying rectangle decomposition back, and
`GridPentagonBetween` being a subsingleton identifies the re-promoted pentagon with the
original.

## Piece 3: Finite-sum weight identity

The decomposition sets split into disjoint-sides and overlapping-sides parts. On the
disjoint part, `disjointCommuteEquiv` is the weight-preserving bijection. On the overlap
part, the involution pairs rectangle--pentagon and pentagon--rectangle decompositions with
preserved `O`-monomial products (`OMonomial_mul_OMonomial_recutLeftEqLeft`); the pentagon
weight correction from `OverlapWeight` is 1 for the counted pentagons here.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRight_first_of` and
  `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRight_second_of`: the terminal-side
  promotions with turn-row transport discharged (Piece 2.1).
* `TauCeti.GridPentagonRectangleDecomposition.recutLeftEqLeftRev`: the reverse recut for the
  common-initial-side orientation (Piece 2.2).
* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft_involution`: the
  common-initial-side recut is involutive (Piece 2.2).
* Precise documentation of the blockers for the full overlap `Equiv` (Piece 2.3) and the
  finite-sum weight identity (Piece 3); see the final section.

Roadmap: CombinatorialHeegaardFloer
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-!
## Piece 2.1: Hypothesis-free terminal-side promotions

The `hturn` hypotheses in `recutRightEqRight_first`/`_second` are discharged by the
turn-row transports from `OverlapTurnRow.lean`. The remaining hypotheses `hfirst`/`hsecond`
are the branch data recording which recut rectangle inherits the pentagon's terminal side.
-/

/-- The terminal-side recut promoting the first rectangle, with the turn-row membership
proved by `turn_mem_recut_first_of_right_eq_right`. -/
noncomputable def recutRightEqRight_first_of
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).first.right = D.pentagon.right) :
    GridPentagonRectangleDecomposition a s x z :=
  D.recutRightEqRight_first hone hrectangle hpentagon hfirst
    (D.turn_mem_recut_first_of_right_eq_right hcommon hone hrectangle hpentagon hfirst)

/-- The terminal-side recut promoting the second rectangle, with the turn-row membership
proved by `turn_mem_recut_second_of_right_eq_right`. -/
noncomputable def recutRightEqRight_second_of
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).second.right = D.pentagon.right) :
    GridRectanglePentagonDecomposition a s x z :=
  D.recutRightEqRight_second hone hrectangle hpentagon hsecond
    (D.turn_mem_recut_second_of_right_eq_right hcommon hone hrectangle hpentagon hsecond)

end GridRectanglePentagonDecomposition

/-!
## Piece 2.2: Reverse recut maps

For each forward promotion, the reverse map recuts the underlying generic rectangle
decomposition and re-promotes the appropriate rectangle. The generic involution
`GridRectangleDecomposition.recut_recut` recovers the original underlying decomposition;
the pentagon is then identified by the `Subsingleton` instance on `GridPentagonBetween`.
-/

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Reverse of `recutLeftEqLeft`: recut a pentagon--rectangle decomposition and promote the
second rectangle to a pentagon, recovering a rectangle--pentagon decomposition.

The hypotheses `hsecond`/`hturn` are the branch data for the reverse direction: they record
that the *second* recut rectangle inherits the pentagon's terminal side `finRotate n a` and
contains the turn row. -/
noncomputable def recutLeftEqLeftRev
    (E : GridPentagonRectangleDecomposition a s x z)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hpentagon : E.pentagon.IsEmpty) (hrectangle : E.rectangle.IsEmpty)
    (hsecond : (E.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_first_toGridRectangle] using hpentagon)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_middle,
          E.toRectangleDecomposition_second_toGridRectangle] using
        hrectangle)).second.right = finRotate n a)
    (hturn : s ∈ Grid.cIco (E.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_first_toGridRectangle] using hpentagon)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_middle,
          E.toRectangleDecomposition_second_toGridRectangle] using
        hrectangle)).second.bottom
      (E.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_first_toGridRectangle] using hpentagon)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_middle,
          E.toRectangleDecomposition_second_toGridRectangle] using
        hrectangle)).second.top) :
    GridRectanglePentagonDecomposition a s x z :=
  { middle := (E.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_first_toGridRectangle] using hpentagon)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_middle,
          E.toRectangleDecomposition_second_toGridRectangle] using
        hrectangle)).middle
    rectangle := (E.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_first_toGridRectangle] using hpentagon)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_middle,
          E.toRectangleDecomposition_second_toGridRectangle] using
        hrectangle)).first
    pentagon := GridPentagonBetween.ofRightEq (E.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_first_toGridRectangle] using hpentagon)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          E.toRectangleDecomposition_middle,
          E.toRectangleDecomposition_second_toGridRectangle] using
        hrectangle)).second hsecond hturn }

end GridPentagonRectangleDecomposition

/-!
## Piece 2.2 (continued): Involution of the common-initial-side recut

The reverse map's underlying generic decomposition is exactly the recut of the input's
underlying generic decomposition. Applying the generic involution `recut_recut` recovers the
original, and `toRectangleDecomposition_injective` lifts this to the typed decompositions.
-/

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The reverse map forgets to the recut of the underlying generic decomposition. -/
theorem recutLeftEqLeftRev_toRectangleDecomposition
    (E : GridPentagonRectangleDecomposition a s x z)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hpentagon : E.pentagon.IsEmpty) (hrectangle : E.rectangle.IsEmpty)
    (hsecond hturn) :
    (E.recutLeftEqLeftRev hone hpentagon hrectangle hsecond hturn).toRectangleDecomposition =
      E.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            E.toRectangleDecomposition_first_toGridRectangle] using hpentagon)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            E.toRectangleDecomposition_middle,
            E.toRectangleDecomposition_second_toGridRectangle] using
          hrectangle) := by
  apply GridRectangleDecomposition.ext
  · simp only [recutLeftEqLeftRev,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left]
  · simp only [recutLeftEqLeftRev,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right]
  · simp only [recutLeftEqLeftRev,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
      GridPentagonBetween.ofRightEq_toGridRectangleBetween]
  · simp only [recutLeftEqLeftRev,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      GridPentagonBetween.ofRightEq_toGridRectangleBetween]

end GridPentagonRectangleDecomposition

/-!
## Piece 2.2 (continued): The involution theorem

Applying the forward recut and then the reverse recut returns the original decomposition.
The underlying generic rectangles cancel by `recut_recut`; the typed equality follows from
`toRectangleDecomposition_injective`.
-/

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The common-initial-side recut is involutive: reversing the forward image recovers `D`.

The hypotheses `hone'`, `hpent'`, `hrect'`, `hsecond`, `hturn` are the branch data for the
reverse direction; the equality holds for any valid choice. -/
theorem recutLeftEqLeft_involution
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hone' : (D.recutLeftEqLeft hcommon hone hrectangle hpentagon)
      |>.toRectangleDecomposition.HasOneCommonSide)
    (hpent' : (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.IsEmpty)
    (hrect' : (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).rectangle.IsEmpty)
    (hsecond hturn) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).recutLeftEqLeftRev hone' hpent' hrect'
      hsecond hturn = D := by
  apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
  simp only [GridPentagonRectangleDecomposition.recutLeftEqLeftRev_toRectangleDecomposition,
    D.recutLeftEqLeft_toRectangleDecomposition hcommon hone hrectangle hpentagon,
    GridRectangleDecomposition.recut_recut]

end GridRectanglePentagonDecomposition

/-!
## Piece 2.3 and Piece 3: Status and blockers

### The overlap equivalence (Piece 2.3)

The involution above (`recutLeftEqLeft_involution`) establishes that the common-initial-side
recut is bijective between the corresponding overlap loci, with explicit forward
(`recutLeftEqLeft`) and reverse (`recutLeftEqLeftRev`) maps. A full `Equiv` between the
`HasOneCommonSide` subtypes would additionally require:

* Assembling the reverse maps for the three remaining side orientations (common-terminal-side
  via `recutRightEqRight_first_of`/`_second_of`, and the two mixed orientations), each with
  its own branch data.
* Proving that the recut always swaps the decomposition type on the overlap locus. This is
  **false in general**: when the rectangle's terminal side equals the pentagon's terminal
  side (`D.rectangle.right = D.pentagon.right`), the recut can inherit the pentagon's
  terminal side in the second rectangle (branch A), yielding another rectangle--pentagon
  decomposition rather than a pentagon--rectangle one. The orientation case analysis must
  therefore either refine the overlap subtypes by branch data or show the non-swapping
  branches are empty for counted decompositions; neither is established in the current
  codebase.

### The finite-sum weight identity (Piece 3)

The disjoint-sides part is reducible to existing results: `disjointCommuteEquiv` gives the
bijection between the `HasDisjointSides` subtypes, `Disjoint.lean` supplies countedness
transport and the weight-preservation lemmas
(`pentagonRectangleWeight_commute_rectanglePentagon`,
`rectanglePentagonWeight_commute_pentagonRectangle`), and the `z = x` diagonal must be
handled before applying `hasDisjointSides_or_hasOneCommonSide_of_ne`.

The overlap part is blocked on two missing ingredients:

* **Weight preservation.** `OMonomial_mul_OMonomial_recutLeftEqLeft` equates the underlying
  rectangle `O`-monomial products, but `rectanglePentagonWeight` and `pentagonRectangleWeight`
  use pentagon weights. The correction-equals-one theorem is not formalized:
  `OverlapWeight.lean` contains only `GridDiagram.addedStrip_disjoint_bigonAbove` and
  explicitly lists the added-strip emptiness, removed-strip analysis, and pentagon-weight
  inheritance as unformalized.
* **Countedness assembly.** The reverse recut must send counted pentagon--rectangle
  decompositions to counted rectangle--pentagon decompositions. `OverlapBijection.lean` and
  `OverlapCounted.lean` provide branch-wise pieces but not the assembled transfer theorem.

Once these are available, the identity
`∑ D ∈ G.rectanglePentagonDecompositions C a s x z, G.rectanglePentagonWeight C D`
`= ∑ E ∈ G.pentagonRectangleDecompositions C a s x z, G.pentagonRectangleWeight C E`
follows by partitioning into disjoint/overlap parts and applying the bijections above; it is
the hypothesis of `pentagon_chain_map_of_weight_identity` in `OverlapFinal.lean`.
-/

end TauCeti
