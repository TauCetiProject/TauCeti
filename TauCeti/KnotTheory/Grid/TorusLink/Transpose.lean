/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Move.Basic
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

/-!
# Transposing a torus link grid

The standard grid of the `(p + 1, q + 1)` torus link has its `O`-markings on the diagonal and its
`X`-markings `q + 1` rows above it, modulo the grid number `(p + 1) + (q + 1)`. Reflecting it
across the diagonal keeps the `O`-markings on the diagonal and puts the `X`-markings `q + 1` rows
below it, which is `p + 1` rows above it modulo the grid number. That is the standard grid of the
`(q + 1, p + 1)` torus link, once the grid sizes `(p + 1) + (q + 1)` and `(q + 1) + (p + 1)` are
identified. So the two grid links are transposes of each other.

Transposition is an automorphism of the crossing-change graph
(`GridLink.crossingChangeGraphTransposeIso`), so this lets every statement about the unknotting
number of the `(p + 1, q + 1)` torus link grid be transported to the `(q + 1, p + 1)` one.

## Main results

* `TauCeti.GridDiagram.toGridLink_transpose_torusLink`: the transpose of the `(p + 1, q + 1)`
  torus link grid presents the same grid link as the `(q + 1, p + 1)` torus link grid.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 3: torus knot grids and the symmetries of grid diagrams.
-/

public section

namespace TauCeti

namespace GridDiagram

/-- Two grid diagrams of equal grid numbers whose markings agree, once the columns and rows of
the two grids are identified, present the same grid link. -/
private theorem toGridLink_eq_of_cast {n m : ℕ} (h : n = m) {G : GridDiagram n}
    {G' : GridDiagram m} (hO : ∀ c, (G.O c : ℕ) = G'.O (Fin.cast h c))
    (hX : ∀ c, (G.X c : ℕ) = G'.X (Fin.cast h c)) : G.toGridLink = G'.toGridLink := by
  subst h
  congr 1
  exact GridDiagram.ext (GridState.ext fun c => Fin.ext (by simpa using hO c))
    (GridState.ext fun c => Fin.ext (by simpa using hX c))

variable (p q : ℕ)

/-- In the transpose of the `(p + 1, q + 1)` torus link grid the `X`-marking of column `c` sits
`p + 1` rows above the diagonal, modulo the grid number. -/
private theorem transpose_torusLink_X_val (c : Fin (p + 1 + (q + 1))) :
    ((torusLink p q).transpose.X c : ℕ) = (c + (p + 1)) % (p + 1 + (q + 1)) := by
  set d : Fin (p + 1 + (q + 1)) := ⟨(c + (p + 1)) % (p + 1 + (q + 1)), Nat.mod_lt _ (by omega)⟩
  have hd : (torusLink p q).X d = c := by
    ext
    rw [torusLink_X_val, Nat.mod_add_mod, show (c : ℕ) + (p + 1) + (q + 1) =
      c + (p + 1 + (q + 1)) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt c.isLt]
  rw [transpose_X]
  conv_lhs => rw [← hd, GridState.transpose_apply_apply]

/-- The transpose of the standard grid of the `(p + 1, q + 1)` torus link presents the same grid
link as the standard grid of the `(q + 1, p + 1)` torus link. -/
@[simp]
theorem toGridLink_transpose_torusLink :
    (torusLink p q).transpose.toGridLink = (torusLink q p).toGridLink := by
  refine toGridLink_eq_of_cast (by omega) (fun c => ?_) (fun c => ?_)
  · simp [← Equiv.Perm.inv_def]
  · rw [transpose_torusLink_X_val, torusLink_X_val, Fin.val_cast, Nat.add_comm (q + 1)]

end GridDiagram

end TauCeti
