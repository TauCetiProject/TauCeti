/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Topological abelianization

The **topological abelianization** of a topological group `G` is the quotient
`G^{ab} = G ⧸ closure [G, G]` by the topological closure of the commutator subgroup. When `G` is
profinite this is the profinite abelianization, and it is the home of the `q`-invariant in the
pro-`p` Demushkin theory of the ProfiniteProPGroups roadmap.

The signature matches `ProfiniteProPGroups/Suggested.lean` (`topAbelianization`).

## Main definitions

* `TauCeti.topAbelianization`: `G ⧸ (commutator G).topologicalClosure`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.4 (abelianization of profinite groups).
-/

public section

namespace TauCeti

universe u

/-- The **topological abelianization** `G^{ab} = G ⧸ closure [G,G]`, the profinite abelianization
when `G` is profinite and the home of the `q`-invariant. -/
abbrev topAbelianization (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Type u :=
  G ⧸ (commutator G).topologicalClosure

end TauCeti
