/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Tau
public import TauCeti.KnotTheory.Grid.TorusLink.Homology

/-!
# The invariant `τ` of the torus knot grids

On the standard grid `torusLink p q` of the `(p + 1, q + 1)` torus link, the `X`-marking state is
a cycle of maximal Alexander grading `p q / 2` that generates a tower of the unblocked grid
homology `GH⁻` (`TorusLink/Homology.lean`). When `p + 1` and `q + 1` are coprime the grid is a
knot grid, and the invariant `τ` of the diagram is minus that grading
(`GridDiagram.two_mul_tau_torusLink`): `2 τ = -p q`. The sign records that the tower of this
grid sits in the *top* Alexander degree; the book's value `τ(T_{p,q}) = (p - 1)(q - 1) / 2` is
for the positive torus knot, and `τ` changes sign under taking the mirror image; the knot this
grid presents is the mirror image of that one.

The two smallest knot instances are the `5 × 5` trefoil grid, with `τ = -1`
(`GridDiagram.tau_torusLink_one_two`), and the `7 × 7` grid of the `(3, 4)` torus knot, with
`τ = -3` (`GridDiagram.tau_torusLink_two_three`). The unknot grids are the torus link grids with
`q = 0`, so every unknot grid has `τ = 0` (`GridDiagram.tau_unknot`).

These are statements about the diagrams: reading them as values of the concordance invariant of
the presented knots requires the invariance of `GH⁻` under grid moves, which is not established
here.

## Main results

* `TauCeti.GridDiagram.two_mul_tau_torusLink`: `2 τ(torusLink p q) = -p q` on a torus knot grid.
* `TauCeti.GridDiagram.tau_torusLink_one_two`, `TauCeti.GridDiagram.tau_torusLink_two_three`:
  `τ = -1` on the `5 × 5` trefoil grid and `τ = -3` on the `7 × 7` grid of the `(3, 4)` torus knot.
* `TauCeti.GridDiagram.tau_unknot`: `τ = 0` on every unknot grid.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Chapter 6, where `τ` of the torus knots is computed from the
  class of this grid state.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {p q : ℕ} (h : (p + 1).Coprime (q + 1)) (K : Type*) [Field K] [CharP K 2]

/-- **`τ` of a torus knot grid**: on the standard grid of the `(p + 1, q + 1)` torus knot,
`2 τ = -p q`. -/
theorem two_mul_tau_torusLink :
    2 * ((isKnot_torusLink_iff p q).mpr h).tau K = -(p * q : ℤ) := by
  rw [IsKnot.tau_def, mul_neg, two_mul_supNonTorsionDegree_torusLink h K]

/-- On the `5 × 5` trefoil grid, `τ = -1`. -/
@[simp]
theorem tau_torusLink_one_two : ((isKnot_torusLink_iff 1 2).mpr (by decide)).tau K = -1 := by
  have h := two_mul_tau_torusLink (p := 1) (q := 2) (by decide) K
  omega

/-- On the `7 × 7` grid of the `(3, 4)` torus knot, `τ = -3`. -/
@[simp]
theorem tau_torusLink_two_three : ((isKnot_torusLink_iff 2 3).mpr (by decide)).tau K = -3 := by
  have h := two_mul_tau_torusLink (p := 2) (q := 3) (by decide) K
  omega

/-- **`τ` of an unknot grid is zero**: the unknot grids are the torus link grids with `q = 0`. -/
@[simp]
theorem tau_unknot (hU : (unknot p).IsKnot) : hU.tau K = 0 := by
  -- `unknot p` is `torusLink p 0`; the diagram is rewritten under the dependent binder `hU`.
  revert hU
  rw [← torusLink_zero_right]
  intro hU
  have h := two_mul_tau_torusLink (p := p) (q := 0) (Nat.coprime_one_right _) K
  omega

end GridDiagram

end TauCeti
