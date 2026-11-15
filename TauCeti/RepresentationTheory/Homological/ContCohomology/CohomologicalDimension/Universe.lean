/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.UniverseComparison

/-!
# Independence of cohomological dimension from the extra coefficient universe

For a topological group `G : Type u`, the vanishing predicates `TauCeti.CohomologicalDimensionLE`
and `TauCeti.StrictCohomologicalDimensionLE` and the `ℕ∞`-valued invariants
`TauCeti.cohomologicalDimensionAt`, `TauCeti.strictCohomologicalDimensionAt`, and
`TauCeti.cohomologicalDimension` carry an extra universe parameter `v` so that discrete coefficient
`G`-modules can range over `Type (max u v)`.

At `v = u` and at `v = 0`, both instantiations quantify over discrete `G`-modules `M : Type u`
(since `max u u` and `max u 0` are both definitionally `u`), while the continuous cohomology
objects `continuousCohomology i (ofDiscreteModule ℤ G M)` inside them are formed at different
extra universe parameters of Mathlib's construction. By
`TauCeti.ContinuousCohomology.continuousCohomology_universe_eq`, those cohomology objects agree in
every degree for every topological group `G`, with no compactness, profiniteness, or smallness
hypothesis on `G`. Consequently both vanishing predicates and all three dimension invariants take
identical values at `v = u` and at `v = 0`.

None of the equalities or equivalences here is marked `@[simp]`, because at `u = 0` the left- and
right-hand sides coincide syntactically and a `simp` rule would loop.

## Main results

* `TauCeti.cohomologicalDimensionLE_universe_iff`,
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: the ordinary and strict vanishing
  predicates at extra universe `u` are equivalent to those at extra universe `0`.
* `TauCeti.cohomologicalDimensionAt_universe_eq`: `cd_p` at extra universe `u` equals `cd_p` at
  extra universe `0`.
* `TauCeti.strictCohomologicalDimensionAt_universe_eq`: `scd_p` at extra universe `u` equals
  `scd_p` at extra universe `0`.
* `TauCeti.cohomologicalDimension_universe_eq`: `cd` at extra universe `u` equals `cd` at extra
  universe `0`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3,
  (3.3.1).
* J.-P. Serre, *Galois Cohomology*, Ch. I §3.1.
-/

public section

namespace TauCeti

open TauCeti.ContinuousCohomology

universe u

section Predicates

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

-- None of the `.{u}`-to-`.{0}` equivalences or equalities in this file is marked `@[simp]`:
-- at `u = 0` both sides are syntactically identical, so `simp` would loop.
/-- For a topological group `G : Type u`, the vanishing predicate `CohomologicalDimensionLE p G n`
at extra coefficient universe `u` is equivalent to that at extra coefficient universe `0`. -/
theorem cohomologicalDimensionLE_universe_iff :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n := by
  rw [cohomologicalDimensionLE_iff, cohomologicalDimensionLE_iff]
  refine forall_congr' fun (M : Type u) ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    imp_congr_right fun _ ↦ forall_congr' fun i ↦ imp_congr_right fun _ ↦ ?_
  rw [continuousCohomology_universe_eq i (ofDiscreteModule ℤ G M)]

/-- For a topological group `G : Type u`, the strict vanishing predicate
`StrictCohomologicalDimensionLE p G n` at extra coefficient universe `u` is equivalent to that at
extra coefficient universe `0`. -/
theorem strictCohomologicalDimensionLE_universe_iff :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n := by
  rw [strictCohomologicalDimensionLE_iff, strictCohomologicalDimensionLE_iff]
  refine forall_congr' fun (M : Type u) ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun i ↦ imp_congr_right fun _ ↦ ?_
  rw [continuousCohomology_universe_eq i (ofDiscreteModule ℤ G M)]

end Predicates

section Invariants

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The `p`-cohomological dimension does not depend on the extra coefficient universe**: for a
topological group `G : Type u`, `cohomologicalDimensionAt p G` formed at extra universe `u` equals
that formed at extra universe `0`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G :=
  eq_of_forall_ge_iff fun c ↦
    ENat.recTopCoe (by simp) (fun _ ↦ by simp [cohomologicalDimensionLE_universe_iff]) c

/-- **The strict `p`-cohomological dimension does not depend on the extra coefficient universe**:
for a topological group `G : Type u`, `strictCohomologicalDimensionAt p G` formed at extra universe
`u` equals that formed at extra universe `0`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G :=
  eq_of_forall_ge_iff fun c ↦
    ENat.recTopCoe (by simp) (fun _ ↦ by simp [strictCohomologicalDimensionLE_universe_iff]) c

/-- **The cohomological dimension does not depend on the extra coefficient universe**: for a
topological group `G : Type u`, `cohomologicalDimension G` formed at extra universe `u` equals that
formed at extra universe `0`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G :=
  eq_of_forall_ge_iff fun c ↦
    ENat.recTopCoe (by simp) (fun _ ↦ by simp [cohomologicalDimensionLE_universe_iff]) c

end Invariants

end TauCeti
