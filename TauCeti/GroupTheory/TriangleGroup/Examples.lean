/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Regular
public import TauCeti.Combinatorics.PermutationTriple.Examples

/-!
# Examples of regular triples and triangle groups

This file applies the triangle-group regularity API to the concrete permutation triples from
`TauCeti.Combinatorics.PermutationTriple.Examples`.

## Main results

* `TauCeti.TriangleGroup.index_ker_toPerm_torusTriple`: the torus triple gives a normal subgroup of
  index `4` of `Δ(4, 4, 2)`.
-/

public section

namespace TauCeti

namespace TriangleGroup

/-- The torus triple, with cycle types `[4], [4], [2, 2]`, exhibits a normal subgroup of index `4`
in `Δ(4, 4, 2)`: the kernel of its representation. -/
theorem index_ker_toPerm_torusTriple :
    (toPerm (a := 4) (b := 4) (c := 2) PermutationTriple.torusTriple
      (by rw [PermutationTriple.torusTriple_σ0]; decide)
      (by rw [PermutationTriple.torusTriple_σ1]; decide)
      (by rw [PermutationTriple.torusTriple_σinf]; decide)).ker.index = 4 :=
  index_ker_toPerm_of_isRegular _ _ _ _ PermutationTriple.isRegular_torusTriple

end TriangleGroup

end TauCeti
