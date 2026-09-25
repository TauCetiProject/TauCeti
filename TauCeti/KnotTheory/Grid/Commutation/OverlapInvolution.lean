/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.OverlapRight
public import TauCeti.KnotTheory.Grid.Commutation.OverlapWeight
public import TauCeti.KnotTheory.Grid.Commutation.OverlapCounted
public import TauCeti.KnotTheory.Grid.Commutation.OverlapBijection
public import TauCeti.KnotTheory.Grid.Commutation.Pairing
public import TauCeti.KnotTheory.Grid.Commutation.Decomposition
public import TauCeti.KnotTheory.Grid.Commutation.OverlapFinal

/-!
# Involution and weight identity for the overlap recut

This file records the precise statements needed to complete the pentagon chain-map assembly,
with proofs where the available machinery suffices.

## Piece 1: Turn-row transports (statement and analysis)

The `hturn` hypotheses in `OverlapRight.recutRightEqRight_first`/`_second` require:
- For `_first`: `s ∈ Grid.cIco E.first.bottom E.first.top`
  when `E.first.right = D.pentagon.right`
- For `_second`: `s ∈ Grid.cIco E.second.bottom E.second.top`
  when `E.second.right = D.pentagon.right`

where `E` is the generic recut of `D.toRectangleDecomposition`.

**What is established**: In the common-terminal-side case with
`hcommon : D.rectangle.right = D.pentagon.right`:
- `D.toRectangleDecomposition.first.right = D.toRectangleDecomposition.second.right`
- `IsRecutOfRightEqRight` gives two branches:
  - Branch A: `E.first.right = D.first.left`, `E.second.right = D.first.right`
  - Branch B: `E.first.right = D.first.right`, `E.second.right = D.second.left`
- Since `D.pentagon.right = D.first.right` (via `hcommon'`), the hypothesis
  `E.first.right = D.pentagon.right` forces Branch B (Branch A would give
  `D.first.left = D.first.right`, contradicting `left_ne_right`).
- Similarly, `E.second.right = D.pentagon.right` forces Branch A.

**What remains**: The row intervals `E.first.bottom/top` and `E.second.bottom/top`
are determined by the `IsRecut` repartition data, not directly by the branch equations.
The transport needs:
1. `E.first.bottom` and `E.first.top` expressed via the original corner rows
   (from the `IsRecut.isRepartition` covered-square data or the middle-state equations).
2. The cyclic row order `D.first.bottom ∈ cIoo D.second.bottom D.first.top`
   (from `cyclicOrder_of_isEmpty_of_right_eq_right`).
3. The pentagon turn membership `s ∈ cIco D.pentagon.bottom D.pentagon.top`
   transferred to `s ∈ cIco D.second.bottom D.second.top` (via `toRectangleDecomposition`).
4. Interval combination: showing the turn row lies in the appropriate recut rectangle's
   row span using the branch-specific row splits.

This mirrors `turn_mem_recut_first_of_left_eq_left` in `Overlap.lean`, which handles the
common-initial-side case using `cyclicOrder_of_isEmpty_of_left_eq_left` and
`IsRecutOfLeftEqLeft.recut_branch`.

## Piece 2: Involution (statement and analysis)

The overlap bijection needs `recutLeftEqLeft` to be involutive on the overlap locus, or
an explicit reverse map. The generic recut has symmetry properties
(`isRecut_symm_of_right_eq_right` in `Recut/Pairing.lean`), but lifting these to the
typed `recutLeftEqLeft`/`recutRightEqRight_*` requires:
1. The turn-row transports from Piece 1 (to apply the forward map to recut outputs).
2. Showing the recut of a recut recovers the original decomposition
   (via the uniqueness part of `existsUnique_isRecut`).
3. Verifying the pentagon promotion is compatible with the involution
   (the `ofRightEq`/`ofLeftEq` promotions must match up).

## Piece 3: Finite-sum weight identity (statement and analysis)

The target identity:
```
(∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) =
∑ D ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R D
```

**Disjoint part** (ready): `disjointCommuteEquiv` gives the bijection; weight preservation
follows from the `commute` weight lemmas in `Disjoint.lean`.

**Overlap part** (needs Pieces 1-2): The recut bijection on the overlap locus with
weight preservation from `OMonomial_mul_OMonomial_recutLeftEqLeft` plus the
`OverlapWeight` correction (= 1 when the strips avoid O-markings).

**Combination** (needs the partition): The decomposition sets must be partitioned into
disjoint-sides vs. overlapping-sides subsets, with the two bijections covering the
respective parts. This uses `HasDisjointSides` vs. `HasOneCommonSide` classification.

Once Piece 3 is established, `pentagon_chain_map_of_weight_identity` in `OverlapFinal.lean`
gives the chain-map theorem immediately.

## What this file proves

The branch-forcing lemmas: the `hfirst`/`hsecond` hypotheses in `OverlapRight` determine
which recut branch holds. These are the first step of Piece 1.

Roadmap: CombinatorialHeegaardFloer
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-!
## Branch determination for the terminal-side recut

When the rectangle and pentagon share their terminal side, the hypothesis that a specific
recut rectangle inherits the pentagon's terminal side determines the recut branch.
-/

/-- If the first recut rectangle has the pentagon's terminal side, the recut is in the
second branch of `IsRecutOfRightEqRight` (where `E.first.right = D.first.right`). -/
theorem recut_branch_of_first_right_eq
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
    D.toRectangleDecomposition.second.left ∈
        Grid.cIoo D.toRectangleDecomposition.first.left
          D.toRectangleDecomposition.first.right := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  have hpen_right : D.pentagon.right = D.toRectangleDecomposition.first.right := by
    rw [← toRectangleDecomposition_second_right D, ← hcommon']
  rcases hbranch with ⟨hcol, -, hEfirst, -⟩ | ⟨hcol, -, -, -⟩
  · -- First branch: E.first.right = D.first.left, so D.first.left = D.pentagon.right
    -- = D.first.right, contradicting left_ne_right.
    exfalso
    rw [hEfirst, hpen_right] at hfirst
    exact D.toRectangleDecomposition.first.left_ne_right hfirst
  · exact hcol

/-- If the second recut rectangle has the pentagon's terminal side, the recut is in the
first branch of `IsRecutOfRightEqRight` (where `E.second.right = D.first.right`). -/
theorem recut_branch_of_second_right_eq
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
    D.toRectangleDecomposition.first.left ∈
        Grid.cIoo D.toRectangleDecomposition.second.left
          D.toRectangleDecomposition.first.right := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  have hpen_right : D.pentagon.right = D.toRectangleDecomposition.first.right := by
    rw [← toRectangleDecomposition_second_right D, ← hcommon']
  rcases hbranch with ⟨hcol, -, -, hEsecond⟩ | ⟨-, -, -, hEsecond⟩
  · exact hcol
  · -- Second branch: E.second.right = D.second.left, so D.second.left = D.pentagon.right
    -- = D.first.right = D.second.right (by hcommon'), contradicting left_ne_right.
    exfalso
    rw [hEsecond, hpen_right, hcommon'] at hsecond
    exact D.toRectangleDecomposition.second.left_ne_right hsecond

end GridRectanglePentagonDecomposition

end TauCeti
