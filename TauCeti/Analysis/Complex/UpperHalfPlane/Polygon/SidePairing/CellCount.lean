/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.PermutationTriple
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import TauCeti.Combinatorics.ChordDiagram
import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic

/-!
# The cell count of a side-paired polygon

Let `σ` pair the sides of a convex hyperbolic `n`-gon `P`, with vertices in `ℍ ∪ ∂ℍ`. Gluing `P`
along `σ`, and filling in a point at each ideal vertex cycle, gives a closed surface with a cell
decomposition read off the polygon:

* one `0`-cell for each finite vertex cycle, one for each ideal vertex cycle, and one at the
  midpoint of each of the `k` self-paired sides;
* one `1`-cell for each pair of sides, `σ.SideRepresentative`, a self-paired side being folded
  onto its half;
* one `2`-cell, the interior of `P`.

Its alternating cell count is `SidePairing.cellEulerChar`, the integer
`V + c + k - E + 1` for `V` finite vertex cycles, `c` ideal vertex cycles and `E` pairs of sides.
For a fundamental polygon of a Fuchsian group `Γ` this is the Euler characteristic of the
compactified quotient `X(Γ)`; for a compact polygon this identification is
`SidePairing.eulerChar_orbitRel_quotient_eq_cellEulerChar`.

This file shows, from the combinatorics of the gluing alone, that the cell count has the two
properties of the Euler characteristic of a closed connected orientable surface: it is at most
`2` and it is even. The vertex cycles are the cycles of the successor permutation
`σ.next = finRotate n * σ.pair` (`next_eq_finRotate_mul`), and the pairs of sides are the orbits
of the involution `σ.pair` (`orbitCount_pair`); both orbit counts come from the permutation
triple of `σ`. The bound is then the boundary-count bound for a one-vertex chord diagram,
`Equiv.Perm.orbitCount_finRotate_mul_add_orbitCount_le`: each pair of sides glued adds at most
one vertex cycle. The parity is the multiplicativity of the sign of a
permutation: the cell count is the Euler characteristic of the permutation triple
`PermutationTriple.ofTwo σ.pair (finRotate n)`, which is even
(`TauCeti.PermutationTriple.even_eulerChar`).

## Main definitions

* `TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.cellEulerChar`: the alternating cell count
  `V + c + k - E + 1` of the gluing of `P` along `σ`.

## Main results

* `TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.cellEulerChar_le_two`: the cell count is at
  most `2`.
* `TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.even_cellEulerChar`: the cell count is even.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §§9.2–9.3 and 10.4 (the quotient of a fundamental polygon and its genus).
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, Proposition 1.5.3 (the Euler characteristic of a
  surface glued from permutations is at most two and even).
-/

public section

open Equiv Equiv.Perm

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-! ### The successor permutation -/

/-- The side-pairing successor `j ↦ σ.pair j + 1` is the involution `σ.pair` followed by the
rotation of the vertex indices. -/
theorem next_eq_finRotate_mul : σ.next = finRotate n * σ.pair := by
  ext j
  rw [next_apply, Perm.mul_apply, finRotate_apply]

/-! ### The cell count -/

/-- The **cell count** of the gluing of `P` along `σ`: the number `V + c + k - E + 1` of `0`-cells
minus `1`-cells plus `2`-cells of the cell decomposition with the `V` finite vertex cycles, the
`c` ideal vertex cycles and the midpoints of the `k` self-paired sides as vertices, the `E` pairs
of sides as edges, and the interior of `P` as its one face. -/
noncomputable def cellEulerChar : ℤ :=
  Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
    Nat.card {i : Fin n // σ.pair i = i} - Nat.card σ.SideRepresentative + 1

/-- The defining formula for the cell count. -/
theorem cellEulerChar_def :
    σ.cellEulerChar = Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
      Nat.card {i : Fin n // σ.pair i = i} - Nat.card σ.SideRepresentative + 1 :=
  (rfl)

/-- The cell count through the permutations `σ.next` and `σ.pair`: it is
`orbitCount σ.next + orbitCount σ.pair - n + 1`, the Euler characteristic of the one-vertex chord
diagram of `σ.pair` with its boundary cycles capped. -/
theorem cellEulerChar_eq_orbitCount :
    σ.cellEulerChar = orbitCount σ.next + orbitCount σ.pair - n + 1 := by
  have h := σ.two_mul_natCard_sideRepresentative
  rw [cellEulerChar_def, orbitCount_next, orbitCount_pair]
  omega

/-- **The cell count is at most two.** Gluing the sides of a polygon in pairs leaves at most one
more vertex cycle than there are pairs of sides. -/
theorem cellEulerChar_le_two : σ.cellEulerChar ≤ 2 := by
  have h := σ.pair.orbitCount_finRotate_mul_add_orbitCount_le
  rw [← next_eq_finRotate_mul] at h
  rw [cellEulerChar_eq_orbitCount]
  omega

/-- **The cell count is even**, as the Euler characteristic of a closed orientable surface is:
it is the Euler characteristic of the permutation triple with components `σ.pair` and the
rotation of the vertex indices, whose third component is `σ.next⁻¹`. -/
theorem even_cellEulerChar : Even σ.cellEulerChar := by
  have hrot : orbitCount (finRotate n) = 1 := by simp [orbitCount_finRotate, NeZero.ne n]
  have h : σ.cellEulerChar = (PermutationTriple.ofTwo σ.pair (finRotate n)).eulerChar := by
    rw [cellEulerChar_eq_orbitCount, PermutationTriple.eulerChar_def,
      PermutationTriple.ofTwo_σ0, PermutationTriple.ofTwo_σ1, PermutationTriple.ofTwo_σinf,
      ← next_eq_finRotate_mul, orbitCount_inv, hrot]
    push_cast
    ring
  exact h ▸ (PermutationTriple.ofTwo _ _).even_eulerChar

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
