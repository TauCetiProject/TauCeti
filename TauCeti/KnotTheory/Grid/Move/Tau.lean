/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Invariance
public import TauCeti.KnotTheory.Grid.Move.Unknot
public import TauCeti.KnotTheory.Grid.TorusLink.Tau

/-!
# The invariant `τ` of grid knots

For a grid link with one component, `GridLink.IsKnot.tau` is the integer `τ` of any presenting
knot grid diagram. Independence of the representative follows from invariance under all grid
moves. The computation rule `GridLink.IsKnot.tau_toGridLink` lets callers evaluate it on a
chosen diagram without using the representative selected in the definition.

Over a field of characteristic two the unknot has `τ = 0`. The standard grid of the
`(p + 1, q + 1)` torus knot, for coprime `p + 1` and `q + 1`, represents a grid knot with
`2τ = -pq`. The negative sign follows the definition of `τ` as minus the maximal non-torsion
Alexander degree, as in `TorusLink/Tau.lean`.

This is an invariant of grid knots, defined as grid links with one component. No identification
with embedded knots or claim of concordance invariance is used here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 5 and 6.
The definition uses `GridDiagram.IsKnot.tau` and its grid-move invariance.
-/

public section

namespace TauCeti.GridLink.IsKnot

variable {L : GridLink} (hL : L.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- The integer invariant `τ` of a grid knot, evaluated on a presenting knot diagram.

It is independent of the representative by `GridDiagram.IsKnot.tau_eq_of_movesTo`.
The coefficient ring is retained explicitly, as in the diagram invariant. -/
noncomputable def tau : ℤ :=
  let G := Classical.choose L.exists_gridDiagram
  ((isKnot_toGridLink G.2).mp ((Classical.choose_spec L.exists_gridDiagram).symm ▸ hL)).tau K

/-- Evaluate `τ` on any knot diagram presenting the grid knot. -/
theorem tau_eq_of_toGridLink_eq {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
    (h : G.toGridLink = L) : hL.tau K = hG.tau K := by
  unfold tau
  apply GridDiagram.IsKnot.tau_eq_of_movesTo
  exact ((Classical.choose L.exists_gridDiagram).2.toGridLink_eq_iff_movesTo).mp
    ((Classical.choose_spec L.exists_gridDiagram).trans h.symm)

/-- On the grid knot presented by a diagram, `τ` is the diagram's invariant. -/
@[simp]
theorem tau_toGridLink {n : ℕ} {G : GridDiagram n} (hG : G.toGridLink.IsKnot) :
    hG.tau K = ((isKnot_toGridLink G).mp hG).tau K :=
  tau_eq_of_toGridLink_eq hG K ((isKnot_toGridLink G).mp hG) rfl

end TauCeti.GridLink.IsKnot

namespace TauCeti.GridLink

variable (K : Type*) [Field K] [CharP K 2]

/-- The unknot, as a grid knot independently of grid size, has `τ = 0`. -/
@[simp]
theorem tau_unknot : isKnot_unknot.tau K = 0 := by
  rw [IsKnot.tau_eq_of_toGridLink_eq _ K (GridDiagram.isKnot_unknot 0)
    (GridDiagram.toGridLink_unknot 0)]
  exact GridDiagram.tau_unknot K _

/-- The knot presented by the standard `(p + 1, q + 1)` torus grid has `2τ = -pq`.
The negative sign follows the definition of `τ` as minus the maximal non-torsion degree. -/
theorem two_mul_tau_toGridLink_torusLink {p q : ℕ} (h : (p + 1).Coprime (q + 1)) :
    2 * ((isKnot_toGridLink _).mpr ((GridDiagram.isKnot_torusLink_iff p q).mpr h)).tau K =
      -(p * q : ℤ) := by
  rw [IsKnot.tau_toGridLink]
  exact GridDiagram.two_mul_tau_torusLink h K

end TauCeti.GridLink
