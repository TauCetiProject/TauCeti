/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.UniverseCast

/-!
# Independence of cohomological dimension from the extra coefficient universe

For a topological group `G : Type u`, the vanishing predicates `TauCeti.CohomologicalDimensionLE`
and `TauCeti.StrictCohomologicalDimensionLE` and the dimension invariants
`TauCeti.cohomologicalDimensionAt`, `TauCeti.strictCohomologicalDimensionAt`, and
`TauCeti.cohomologicalDimension` take an explicit extra universe parameter `v` and quantify over
discrete `G`-modules `M : Type (max u v)` with continuous action. Replacing `v` by `max u v` — and,
in particular, comparing `v = u` with `v = 0` — leaves the universe `max u v` of coefficient
modules definitionally unchanged, while the continuous cohomology groups
`continuousCohomology i (ofDiscreteModule ℤ G M)` inside the predicates are formed at two different
universe parameters of Mathlib's construction.

Because continuous cohomology is independent of that extra universe parameter
(`TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_max_universe_iff` and
`TauCeti.ContinuousCohomology.primaryComponent_continuousCohomology_eq_bot_max_universe_iff`), both
vanishing predicates and all three dimension invariants agree between `max u v` and `v`, and in
particular between `u` and `0`, for every topological group `G` without compactness or
profiniteness assumptions.

## Main results

* `TauCeti.cohomologicalDimensionLE_max_universe_iff`,
  `TauCeti.cohomologicalDimensionLE_universe_iff`: universe independence of
  `CohomologicalDimensionLE`.
* `TauCeti.strictCohomologicalDimensionLE_max_universe_iff`,
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: universe independence of
  `StrictCohomologicalDimensionLE`.
* `TauCeti.cohomologicalDimensionAt_max_universe_eq`,
  `TauCeti.cohomologicalDimensionAt_universe_eq`: `cd_p G` at `max u v` equals `cd_p G` at `v` (in
  particular, `cd_p G` at `u` equals `cd_p G` at `0`).
* `TauCeti.strictCohomologicalDimensionAt_max_universe_eq`,
  `TauCeti.strictCohomologicalDimensionAt_universe_eq`: `scd_p G` at `max u v` equals `scd_p G` at
  `v` (in particular, `scd_p G` at `u` equals `scd_p G` at `0`).
* `TauCeti.cohomologicalDimension_max_universe_eq`,
  `TauCeti.cohomologicalDimension_universe_eq`: `cd G` at `max u v` equals `cd G` at `v` (in
  particular, `cd G` at `u` equals `cd G` at `0`).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3,
  (3.3.1).
* J.-P. Serre, *Galois Cohomology*, Ch. I §3.1.
-/

public section

namespace TauCeti

open _root_.TauCeti.ContinuousCohomology

universe v u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

-- None of the `*_max_universe_*` or `*_universe_*` lemmas in this file is marked `@[simp]`: at
-- `v = u` (respectively `u = 0`) the two sides are syntactically identical, so `simp` would loop.

/-- The ordinary vanishing predicate `CohomologicalDimensionLE` is unchanged upon replacing the
extra coefficient universe `v` by `max u v`. -/
theorem cohomologicalDimensionLE_max_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff, cohomologicalDimensionLE_iff]
  refine forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    imp_congr_right fun _ ↦ forall_congr' fun i ↦ imp_congr_right fun _ ↦ ?_
  exact subsingleton_continuousCohomology_max_universe_iff.{v} (ofDiscreteModule ℤ G M) i

/-- For `G : Type u`, `CohomologicalDimensionLE` at extra universe `u` is equivalent to
`CohomologicalDimensionLE` at extra universe `0`. -/
theorem cohomologicalDimensionLE_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n :=
  cohomologicalDimensionLE_max_universe_iff.{0} p G n

/-- The strict vanishing predicate `StrictCohomologicalDimensionLE` is unchanged upon replacing the
extra coefficient universe `v` by `max u v`. -/
theorem strictCohomologicalDimensionLE_max_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔ StrictCohomologicalDimensionLE.{v} p G n := by
  rw [strictCohomologicalDimensionLE_iff, strictCohomologicalDimensionLE_iff]
  refine forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun i ↦ imp_congr_right fun _ ↦ ?_
  exact primaryComponent_continuousCohomology_eq_bot_max_universe_iff.{v}
    (ofDiscreteModule ℤ G M) p i

/-- For `G : Type u`, `StrictCohomologicalDimensionLE` at extra universe `u` is equivalent to
`StrictCohomologicalDimensionLE` at extra universe `0`. -/
theorem strictCohomologicalDimensionLE_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n :=
  strictCohomologicalDimensionLE_max_universe_iff.{0} p G n

/-- **The `p`-cohomological dimension is unchanged upon replacing the extra coefficient universe
`v` by `max u v`.** -/
theorem cohomologicalDimensionAt_max_universe_eq :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G :=
  eq_of_forall_ge_iff <| ENat.recTopCoe (by simp) fun n ↦ by
    rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionAt_le_iff]
    exact cohomologicalDimensionLE_max_universe_iff.{v} p G n

/-- **`cd_p` does not depend on the extra coefficient universe**: for `G : Type u`,
`cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G :=
  cohomologicalDimensionAt_max_universe_eq.{0} p G

/-- **The strict `p`-cohomological dimension is unchanged upon replacing the extra coefficient
universe `v` by `max u v`.** -/
theorem strictCohomologicalDimensionAt_max_universe_eq :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G :=
  eq_of_forall_ge_iff <| ENat.recTopCoe (by simp) fun n ↦ by
    rw [strictCohomologicalDimensionAt_le_iff, strictCohomologicalDimensionAt_le_iff]
    exact strictCohomologicalDimensionLE_max_universe_iff.{v} p G n

/-- **`scd_p` does not depend on the extra coefficient universe**: for `G : Type u`,
`strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G :=
  strictCohomologicalDimensionAt_max_universe_eq.{0} p G

/-- **The cohomological dimension is unchanged upon replacing the extra coefficient universe `v` by
`max u v`.** -/
theorem cohomologicalDimension_max_universe_eq :
    cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G :=
  eq_of_forall_ge_iff <| ENat.recTopCoe (by simp) fun n ↦ by
    rw [cohomologicalDimension_le_iff, cohomologicalDimension_le_iff]
    exact forall_congr' fun q ↦ imp_congr_right fun _ ↦
      cohomologicalDimensionLE_max_universe_iff.{v} q G n

/-- **`cd` does not depend on the extra coefficient universe**: for `G : Type u`,
`cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G :=
  cohomologicalDimension_max_universe_eq.{0} G

end TauCeti
