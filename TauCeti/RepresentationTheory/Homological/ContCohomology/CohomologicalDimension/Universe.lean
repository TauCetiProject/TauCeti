/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.GroupTheory.Torsion
import TauCeti.RepresentationTheory.Homological.ContCohomology.Universe

/-!
# Cohomological dimension does not depend on the extra coefficient universe

For a topological group `G : Type u`, the invariants `cohomologicalDimensionAt.{v} p G` and
`strictCohomologicalDimensionAt.{v} p G` quantify over coefficient modules in `Type (max u v)`.
At the parameters `max u v` and `v` these are the same modules; in particular `v = u` and `v = 0`
both give the modules `M : Type u`. But the continuous cohomology
`Hⁱ(G, M) = continuousCohomology i (ofDiscreteModule ℤ G M)` inside the two invariants is built
with different universe parameters of Mathlib's construction, and the two objects are not
identified by `rfl`. They are isomorphic, by `TopRep.continuousCohomologyUniverseIso`, and an
additive isomorphism preserves both the vanishing of a group and the vanishing of its `p`-primary
component. So the vanishing predicates agree at the two parameters, and with them the invariants.

The theorems compare only parameters with the same coefficient universe `Type (max u v)`; they say
nothing about coefficient modules in a strictly larger universe.

## Main results

* `TauCeti.cohomologicalDimensionLE_universe_iff`,
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: the vanishing predicates at the
  parameters `max u v` and `v` are equivalent.
* `TauCeti.cohomologicalDimensionAt_universe_eq`: **`cd_p G` is the same at the parameters
  `max u v` and `v`**; at `v = 0` this says that `cd_p G` read at `v = u` equals `cd_p G` read at
  `v = 0`.
* `TauCeti.strictCohomologicalDimensionAt_universe_eq`: **the same for `scd_p G`.**
-/

public section

namespace TauCeti

universe u v

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The ordinary vanishing predicate does not depend on the extra coefficient universe: it holds
at the parameter `max u v` exactly when it holds at `v`. -/
theorem cohomologicalDimensionLE_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n := by
  simp only [cohomologicalDimensionLE_iff]
  constructor <;> intro h M _ _ _ _ _ hM i hi
  · exact (TopRep.continuousCohomologyUniverseIso.{0, u, v} (ofDiscreteModule ℤ G M)
      i).toContinuousLinearEquiv.toEquiv.subsingleton_congr.1 (h M hM i hi)
  · exact (TopRep.continuousCohomologyUniverseIso.{0, u, v} (ofDiscreteModule ℤ G M)
      i).toContinuousLinearEquiv.toEquiv.subsingleton_congr.2 (h M hM i hi)

/-- The strict vanishing predicate does not depend on the extra coefficient universe: it holds at
the parameter `max u v` exactly when it holds at `v`. -/
theorem strictCohomologicalDimensionLE_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔ StrictCohomologicalDimensionLE.{v} p G n := by
  simp only [strictCohomologicalDimensionLE_iff]
  constructor <;> intro h M _ _ _ _ _ i hi
  · exact (TopRep.continuousCohomologyUniverseIso.{0, u, v} (ofDiscreteModule ℤ G M)
      i).toContinuousLinearEquiv.toAddEquiv.primaryComponent_eq_bot_iff.1 (h M i hi)
  · exact (TopRep.continuousCohomologyUniverseIso.{0, u, v} (ofDiscreteModule ℤ G M)
      i).toContinuousLinearEquiv.toAddEquiv.primaryComponent_eq_bot_iff.2 (h M i hi)

/-- **`cd_p` does not depend on the extra coefficient universe.** For a topological group
`G : Type u`, the `p`-cohomological dimension read at the universe parameter `max u v` equals the
one read at `v`; both quantify over coefficient modules in `Type (max u v)`. At `v = 0` this is
the equality `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G :=
  eq_of_forall_ge_iff fun c ↦ by
    induction c using ENat.recTopCoe with
    | top => simp only [le_top]
    | coe n =>
      exact (cohomologicalDimensionAt_le_iff p G n).trans <|
        (cohomologicalDimensionLE_universe_iff p G n).trans
          (cohomologicalDimensionAt_le_iff p G n).symm

/-- **`scd_p` does not depend on the extra coefficient universe.** For a topological group
`G : Type u`, the strict `p`-cohomological dimension read at the universe parameter `max u v`
equals the one read at `v`. At `v = 0` this is the equality
`strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G :=
  eq_of_forall_ge_iff fun c ↦ by
    induction c using ENat.recTopCoe with
    | top => simp only [le_top]
    | coe n =>
      exact (strictCohomologicalDimensionAt_le_iff p G n).trans <|
        (strictCohomologicalDimensionLE_universe_iff p G n).trans
          (strictCohomologicalDimensionAt_le_iff p G n).symm

end TauCeti
