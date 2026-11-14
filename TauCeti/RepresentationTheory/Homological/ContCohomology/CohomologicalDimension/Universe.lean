/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Universe

/-!
# Cohomological dimension does not depend on the extra coefficient universe

For a topological group `G : Type u`, the invariants `cd_p G = cohomologicalDimensionAt.{v} p G`,
`scd_p G = strictCohomologicalDimensionAt.{v} p G` and `cd G = cohomologicalDimension.{v} G`
quantify over discrete coefficient modules `M : Type (max u v)`. The extra universe `v` also
selects the universe parameter of Mathlib's continuous cohomology
`continuousCohomology i (ofDiscreteModule ℤ G M)`, so the invariants at two values of `v` with the
same coefficient universe, such as `v = u` and `v = 0`, are not definitionally equal.

This file shows that they are equal: `v` matters only through `max u v`. The cohomology objects
at the parameters `v` and `max u v` coincide (`TauCeti.continuousCohomology_universe_eq`), so the
vanishing predicates agree degree by degree. In particular the invariants at `v = u` and at
`v = 0` agree, so theorems proved at either instantiation apply at the other.

## Main results

* `TauCeti.cohomologicalDimensionLE_universe_iff`,
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: the vanishing predicates at `max u v`
  and at `v` agree.
* `TauCeti.cohomologicalDimensionAt_universe_eq`: `cd_p G` at `max u v` is `cd_p G` at `v`.
* `TauCeti.strictCohomologicalDimensionAt_universe_eq`: the same for `scd_p G`.
* `TauCeti.cohomologicalDimension_universe_eq`: the same for `cd G`.
-/

public section

namespace TauCeti

universe v u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The ordinary vanishing predicate at the extra universe `max u v` agrees with the one at `v`:
both quantify over the same coefficient modules, and their cohomology objects are equal. -/
theorem cohomologicalDimensionLE_universe_iff {n : ℕ} :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff, cohomologicalDimensionLE_iff]
  constructor
  · intro h M _ _ _ _ _ hM i hi
    rw [TauCeti.continuousCohomology_universe_eq.{0, u, v}]
    exact h M hM i hi
  · intro h M _ _ _ _ _ hM i hi
    rw [← TauCeti.continuousCohomology_universe_eq.{0, u, v}]
    exact h M hM i hi

/-- The strict vanishing predicate at the extra universe `max u v` agrees with the one at `v`:
both quantify over the same coefficient modules, and their cohomology objects are equal. -/
theorem strictCohomologicalDimensionLE_universe_iff {n : ℕ} :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔ StrictCohomologicalDimensionLE.{v} p G n := by
  rw [strictCohomologicalDimensionLE_iff, strictCohomologicalDimensionLE_iff]
  constructor
  · intro h M _ _ _ _ _ i hi
    rw [TauCeti.continuousCohomology_universe_eq.{0, u, v}]
    exact h M i hi
  · intro h M _ _ _ _ _ i hi
    rw [← TauCeti.continuousCohomology_universe_eq.{0, u, v}]
    exact h M i hi

variable (p G)

/-- **`cd_p` does not depend on the extra coefficient universe** beyond `max u v`:
`cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G`. At `v = 0` this
says that `cd_p G` is the same at the parameters `u` and `0`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using ENat.recTopCoe with
  | top => simp only [le_top]
  | coe n =>
    exact (cohomologicalDimensionAt_le_iff p G n).trans
      (cohomologicalDimensionLE_universe_iff.trans (cohomologicalDimensionAt_le_iff p G n).symm)

/-- **`scd_p` does not depend on the extra coefficient universe** beyond `max u v`:
`strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G`. At
`v = 0` this says that `scd_p G` is the same at the parameters `u` and `0`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using ENat.recTopCoe with
  | top => simp only [le_top]
  | coe n =>
    exact (strictCohomologicalDimensionAt_le_iff p G n).trans
      (strictCohomologicalDimensionLE_universe_iff.trans
        (strictCohomologicalDimensionAt_le_iff p G n).symm)

/-- `cd` does not depend on the extra coefficient universe beyond `max u v`:
`cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using ENat.recTopCoe with
  | top => simp only [le_top]
  | coe n =>
    exact (cohomologicalDimension_le_iff G n).trans
      ((forall₂_congr fun _ _ ↦ cohomologicalDimensionLE_universe_iff).trans
        (cohomologicalDimension_le_iff G n).symm)

end TauCeti
