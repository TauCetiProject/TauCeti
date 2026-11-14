/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Universe

/-!
# Independence of cohomological dimension from the extra coefficient universe

For a topological group `G : Type u` and an extra universe `v`, the vanishing predicates
`CohomologicalDimensionLE.{v} p G n` and `StrictCohomologicalDimensionLE.{v} p G n` quantify over
discrete `G`-modules `M : Type (max u v)` with continuous action, forming the continuous cohomology
objects `continuousCohomology.{0, u, v} i (ofDiscreteModule ℤ G M)`.

When `v` is replaced by `max u v`, the domain of quantification `Type (max u (max u v))` is
definitionally the same `Type (max u v)`, yet the cohomology objects inside the predicates carry
different extra universe parameters (`max u v` vs `v`) and are not definitionally equal. In
particular, at `v = 0` (`max u 0 = u`), the invariants `cohomologicalDimensionAt.{u} p G` and
`cohomologicalDimensionAt.{0} p G` (and likewise `strictCohomologicalDimensionAt` and
`cohomologicalDimension`) quantify over the same discrete `G`-modules in `Type u` while computing
homology with parameters `u` and `0`.

This file proves that the predicates and the resulting `ℕ∞`-valued dimension invariants agree
across `max u v` and `v` — and hence across `u` and `0` — for every topological group `G` and every
`p : ℕ`, with no compactness, profiniteness or smallness hypothesis on `G`. For each discrete
`G`-module `M : Type (max u v)`, the additive equivalence
`(ofDiscreteModule ℤ G M).continuousCohomologyUniverseEquiv.{v} i` preserves both triviality and
`p`-primary components (`AddEquiv.primaryComponent_eq_bot_iff`), so the invariants satisfy the same
finite upper bounds in `ℕ∞`.

## Main results

* `TauCeti.cohomologicalDimensionLE_max_universe_iff`,
  `TauCeti.cohomologicalDimensionLE_universe_iff`: `CohomologicalDimensionLE` agrees at `max u v`
  and `v`, and in particular at `u` and `0`.
* `TauCeti.strictCohomologicalDimensionLE_max_universe_iff`,
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: the same for
  `StrictCohomologicalDimensionLE`.
* `TauCeti.cohomologicalDimensionAt_max_universe_eq`,
  `TauCeti.cohomologicalDimensionAt_universe_eq`: `cd_p G` at `max u v` equals `cd_p G` at `v`, and
  in particular `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`.
* `TauCeti.strictCohomologicalDimensionAt_max_universe_eq`,
  `TauCeti.strictCohomologicalDimensionAt_universe_eq`: `scd_p G` at `max u v` equals `scd_p G` at
  `v`, and in particular
  `strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`.
* `TauCeti.cohomologicalDimension_max_universe_eq`,
  `TauCeti.cohomologicalDimension_universe_eq`: `cd G` at `max u v` equals `cd G` at `v`, and in
  particular `cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3,
  (3.3.1).
-/

public section

namespace TauCeti

section MaxUniverse

universe v u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `CohomologicalDimensionLE` at extra universe `max u v` is equivalent to
`CohomologicalDimensionLE` at `v`. -/
theorem cohomologicalDimensionLE_max_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff, cohomologicalDimensionLE_iff]
  exact forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun i ↦
      forall_congr' fun _ ↦
        (ofDiscreteModule ℤ G M).subsingleton_continuousCohomology_universe_iff.{v} i

/-- `StrictCohomologicalDimensionLE` at extra universe `max u v` is equivalent to
`StrictCohomologicalDimensionLE` at `v`. -/
theorem strictCohomologicalDimensionLE_max_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔ StrictCohomologicalDimensionLE.{v} p G n := by
  rw [strictCohomologicalDimensionLE_iff, strictCohomologicalDimensionLE_iff]
  exact forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun i ↦ forall_congr' fun _ ↦
      ((ofDiscreteModule ℤ G M).continuousCohomologyUniverseEquiv.{v} i).primaryComponent_eq_bot_iff
        p

/-- **`cd_p` does not depend on absorbing `u` into the extra coefficient universe**:
`cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G`. -/
theorem cohomologicalDimensionAt_max_universe_eq :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G :=
  WithTop.eq_of_forall_le_coe_iff fun n : ℕ ↦
    (cohomologicalDimensionAt_le_iff p G n).trans <|
      (cohomologicalDimensionLE_max_universe_iff.{v} p G n).trans
        (cohomologicalDimensionAt_le_iff p G n).symm

/-- **`scd_p` does not depend on absorbing `u` into the extra coefficient universe**:
`strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G`. -/
theorem strictCohomologicalDimensionAt_max_universe_eq :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G :=
  WithTop.eq_of_forall_le_coe_iff fun n : ℕ ↦
    (strictCohomologicalDimensionAt_le_iff p G n).trans <|
      (strictCohomologicalDimensionLE_max_universe_iff.{v} p G n).trans
        (strictCohomologicalDimensionAt_le_iff p G n).symm

/-- **`cd` does not depend on absorbing `u` into the extra coefficient universe**:
`cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G`. -/
theorem cohomologicalDimension_max_universe_eq :
    cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G :=
  WithTop.eq_of_forall_le_coe_iff fun n : ℕ ↦
    (cohomologicalDimension_le_iff G n).trans <|
      (forall_congr' fun q ↦ forall_congr' fun _ ↦
        cohomologicalDimensionLE_max_universe_iff.{v} q G n).trans
        (cohomologicalDimension_le_iff G n).symm

end MaxUniverse

section UniverseEq

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For `G : Type u`, `CohomologicalDimensionLE` at extra universe `u` is equivalent to
`CohomologicalDimensionLE` at `0`. -/
theorem cohomologicalDimensionLE_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n :=
  cohomologicalDimensionLE_max_universe_iff.{0} p G n

/-- For `G : Type u`, `StrictCohomologicalDimensionLE` at extra universe `u` is equivalent to
`StrictCohomologicalDimensionLE` at `0`. -/
theorem strictCohomologicalDimensionLE_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n :=
  strictCohomologicalDimensionLE_max_universe_iff.{0} p G n

/-- **`cd_p` does not depend on the extra coefficient universe**: for every topological group
`G : Type u`, `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G :=
  cohomologicalDimensionAt_max_universe_eq.{0} p G

/-- **`scd_p` does not depend on the extra coefficient universe**: for every topological group
`G : Type u`,
`strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G :=
  strictCohomologicalDimensionAt_max_universe_eq.{0} p G

/-- **`cd` does not depend on the extra coefficient universe**: for every topological group
`G : Type u`, `cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G :=
  cohomologicalDimension_max_universe_eq.{0} G

end UniverseEq

end TauCeti
