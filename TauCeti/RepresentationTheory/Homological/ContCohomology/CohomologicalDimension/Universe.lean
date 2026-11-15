/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Universe

/-!
# Independence of cohomological dimension from the redundant coefficient universe parameter

For a topological group `G : Type u` and `p : ℕ`, the vanishing predicates
`TauCeti.CohomologicalDimensionLE.{v} p G n` and
`TauCeti.StrictCohomologicalDimensionLE.{v} p G n` quantify over discrete `G`-modules
`M : Type (max u v)`. Replacing `v` by `max u v` — and in particular comparing `v = u` with
`v = 0`, where `max u u = max u 0 = u` — leaves the domain `Type (max u v)` of coefficient modules
unchanged, while forming Mathlib's `continuousCohomology i (ofDiscreteModule ℤ G M)` at two
different auxiliary universe parameters.

Using the additive equivalence `TauCeti.ContCohomology.universeEquiv` between those two cohomology
groups, this file proves that both vanishing predicates and the invariants
`TauCeti.cohomologicalDimensionAt`, `TauCeti.strictCohomologicalDimensionAt`, and
`TauCeti.cohomologicalDimension` agree at `max u v` and at `v` (and hence in particular at `u` and
at `0`), for every topological group `G` with no compactness, profiniteness, or smallness
assumptions.

## Main results

* `TauCeti.cohomologicalDimensionLE_max_universe_iff`,
  `TauCeti.strictCohomologicalDimensionLE_max_universe_iff`: the ordinary and strict vanishing
  predicates at `max u v` and at `v` are equivalent; `TauCeti.cohomologicalDimensionLE_universe_iff`
  and `TauCeti.strictCohomologicalDimensionLE_universe_iff` specialize this to `u` and `0`.
* `TauCeti.cohomologicalDimensionAt_max_universe_eq`,
  `TauCeti.strictCohomologicalDimensionAt_max_universe_eq`,
  `TauCeti.cohomologicalDimension_max_universe_eq`: `cd_p`, `scd_p`, and `cd` agree at `max u v`
  and at `v`.
* `TauCeti.cohomologicalDimensionAt_universe_eq`,
  `TauCeti.strictCohomologicalDimensionAt_universe_eq`,
  `TauCeti.cohomologicalDimension_universe_eq`: **`cd_p`, `scd_p`, and `cd` agree at `v = u` and at
  `v = 0`**, for every topological group `G : Type u`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §3,
  (3.3.1).
-/

public section

namespace TauCeti

open ContCohomology

section MaxUniverse

universe v u

section Predicates

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

/-- `CohomologicalDimensionLE` is unchanged when the extra universe parameter `v` is replaced by
`max u v`. -/
theorem cohomologicalDimensionLE_max_universe_iff :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n := by
  simp only [cohomologicalDimensionLE_iff]
  refine forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    imp_congr_right fun _ ↦ forall_congr' fun i ↦ imp_congr_right fun _ ↦ ?_
  exact subsingleton_continuousCohomology_max_universe_iff.{0, u, v} (ofDiscreteModule ℤ G M) i

/-- `StrictCohomologicalDimensionLE` is unchanged when the extra universe parameter `v` is replaced
by `max u v`. -/
theorem strictCohomologicalDimensionLE_max_universe_iff :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔
      StrictCohomologicalDimensionLE.{v} p G n := by
  simp only [strictCohomologicalDimensionLE_iff]
  refine forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun i ↦ imp_congr_right fun _ ↦ ?_
  exact primaryComponent_continuousCohomology_max_universe_eq_bot_iff.{0, u, v}
    (ofDiscreteModule ℤ G M) i p

end Predicates

/-- The `p`-cohomological dimension `cd_p G` is unchanged when the extra universe parameter `v` is
replaced by `max u v`. -/
theorem cohomologicalDimensionAt_max_universe_eq (p : ℕ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G :=
  eq_of_forall_ge_iff fun c ↦ ENat.recTopCoe (by simp)
    (fun n ↦ by
      simp only [cohomologicalDimensionAt_le_iff]
      exact cohomologicalDimensionLE_max_universe_iff.{v, u}) c

/-- The strict `p`-cohomological dimension `scd_p G` is unchanged when the extra universe parameter
`v` is replaced by `max u v`. -/
theorem strictCohomologicalDimensionAt_max_universe_eq (p : ℕ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G :=
  eq_of_forall_ge_iff fun c ↦ ENat.recTopCoe (by simp)
    (fun n ↦ by
      simp only [strictCohomologicalDimensionAt_le_iff]
      exact strictCohomologicalDimensionLE_max_universe_iff.{v, u}) c

/-- The cohomological dimension `cd G` is unchanged when the extra universe parameter `v` is
replaced by `max u v`. -/
theorem cohomologicalDimension_max_universe_eq (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G :=
  eq_of_forall_ge_iff fun c ↦ ENat.recTopCoe (by simp)
    (fun n ↦ by
      simp only [cohomologicalDimension_le_iff]
      exact forall_congr' fun _ ↦ imp_congr_right fun _ ↦
        cohomologicalDimensionLE_max_universe_iff.{v, u}) c

end MaxUniverse

section ZeroUniverse

universe u

section Predicates

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

/-- For `G : Type u`, `CohomologicalDimensionLE` agrees at the universe parameters `v = u` and
`v = 0`. -/
theorem cohomologicalDimensionLE_universe_iff :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n :=
  cohomologicalDimensionLE_max_universe_iff.{0, u}

/-- For `G : Type u`, `StrictCohomologicalDimensionLE` agrees at the universe parameters `v = u`
and `v = 0`. -/
theorem strictCohomologicalDimensionLE_universe_iff :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n :=
  strictCohomologicalDimensionLE_max_universe_iff.{0, u}

end Predicates

/-- **`cd_p` does not depend on the redundant coefficient universe parameter**: for every
topological group `G : Type u` and `p : ℕ`, `cohomologicalDimensionAt.{u} p G` equals
`cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G :=
  cohomologicalDimensionAt_max_universe_eq.{0, u} p G

/-- **`scd_p` does not depend on the redundant coefficient universe parameter**: for every
topological group `G : Type u` and `p : ℕ`, `strictCohomologicalDimensionAt.{u} p G` equals
`strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq (p : ℕ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G :=
  strictCohomologicalDimensionAt_max_universe_eq.{0, u} p G

/-- **`cd` does not depend on the redundant coefficient universe parameter**: for every topological
group `G : Type u`, `cohomologicalDimension.{u} G` equals `cohomologicalDimension.{0} G`. -/
theorem cohomologicalDimension_universe_eq (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G :=
  cohomologicalDimension_max_universe_eq.{0, u} G

end ZeroUniverse

end TauCeti
