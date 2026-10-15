/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Indexed

/-!
# The countable join model for a universal group space

Specializing the indexed join to the constant family on `ℕ` gives `universalGSpace G`, the
underlying space in Milnor's join construction.  The distinguished vertex over index zero
supplies its base point when `G` has a chosen unit.  Later constructions can define the diagonal
group action directly on these labelled vertices.

## Main definitions

* `TauCeti.universalGSpace`: the realization of the countable join of copies of `G`.
* `TauCeti.universalGSpaceBasepoint`: the distinguished vertex over index zero.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

namespace TauCeti

universe u

/-- Milnor's countable join of copies of a type, realized with the weak topology. -/
abbrev universalGSpace (G : Type u) : Type _ :=
  (indexedJoin fun _ : ℕ => G).Realization

/-- The distinguished vertex over index zero in the countable join of copies of a type with a
chosen unit. -/
def universalGSpaceBasepoint (G : Type u) [One G] : universalGSpace G :=
  (indexedJoin fun _ : ℕ => G).vertex ⟨0, 1⟩

/-- The barycentric coordinates of the distinguished point are concentrated at the vertex
labelled by index zero and the chosen unit. -/
@[simp]
theorem universalGSpaceBasepoint_val (G : Type u) [One G] :
    (universalGSpaceBasepoint G : (Σ _ : ℕ, G) →₀ ℝ) = Finsupp.single ⟨0, 1⟩ 1 := by
  rw [universalGSpaceBasepoint, AbstractSimplicialComplex.vertex_val]

end TauCeti
