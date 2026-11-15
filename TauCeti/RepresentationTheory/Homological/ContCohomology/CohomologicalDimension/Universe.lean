/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Universe
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialGroup

/-!
# Independence of cohomological dimension from the redundant auxiliary universe

For a topological group `G : Type u`, the predicates `TauCeti.CohomologicalDimensionLE.{v} p G n`
and `TauCeti.StrictCohomologicalDimensionLE.{v} p G n` quantify over discrete `G`-modules
`M : Type (max u v)` with continuous action, and evaluate Mathlib's continuous cohomology
`continuousCohomology.{0, u, v} i (ofDiscreteModule ℤ G M)`.

Because `max u (max u v) = max u v` definitionally, the predicates at `max u v` and at `v`
quantify over the exact same coefficient modules `M : Type (max u v)`. In particular, at `v = 0`
(`max u 0 = u`), the instantiations at `u` and at `0` quantify over the same discrete `G`-modules
`M : Type u`, although the cohomology objects inside them carry different auxiliary universe
parameters (`u` versus `0`) and are not definitionally equal.

Using `TopRep.continuousCohomologyUniverseIso` from
`TauCeti.RepresentationTheory.Homological.ContCohomology.Universe`, which preserves both
triviality and `p`-primary components of continuous cohomology, this file proves that the
vanishing predicates and the resulting `ℕ∞`-valued invariants agree between `max u v` and `v`, and
therefore between `u` and `0`, for every topological group `G` without compactness, profiniteness,
or `Type 0` hypotheses:

* `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`;
* `strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`;
* `cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`.

These theorems compare `max u v` with `v` (and hence `u` with `0`); they say nothing about
coefficient modules in a universe strictly larger than `max u v`.

## Main results

* `TauCeti.cohomologicalDimensionLE_max_iff`, `TauCeti.cohomologicalDimensionLE_universe_iff`:
  equivalence of `CohomologicalDimensionLE` at `max u v` and `v`, and at `u` and `0`.
* `TauCeti.strictCohomologicalDimensionLE_max_iff`,
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: the same for
  `StrictCohomologicalDimensionLE`.
* `TauCeti.cohomologicalDimensionAt_max_eq`, `TauCeti.cohomologicalDimensionAt_universe_eq`:
  `cd_p` agrees at `max u v` and `v`, and in particular at `u` and `0`.
* `TauCeti.strictCohomologicalDimensionAt_max_eq`,
  `TauCeti.strictCohomologicalDimensionAt_universe_eq`: `scd_p` agrees at `max u v` and `v`, and in
  particular at `u` and `0`.
* `TauCeti.cohomologicalDimension_max_eq`, `TauCeti.cohomologicalDimension_universe_eq`: `cd`
  agrees at `max u v` and `v`, and in particular at `u` and `0`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §3,
  (3.3.1): definition of ordinary and strict `p`-cohomological dimension.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.1: definition of `p`-cohomological dimension and
  strict `p`-cohomological dimension.
-/

public section

namespace TauCeti

universe v u

section Predicates

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

/-- `CohomologicalDimensionLE` at auxiliary universe `max u v` is equivalent to
`CohomologicalDimensionLE` at `v`. -/
theorem cohomologicalDimensionLE_max_iff :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff, cohomologicalDimensionLE_iff]
  exact forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun i ↦ forall_congr' fun _ ↦
      (ofDiscreteModule ℤ G M).subsingleton_continuousCohomology_max_iff i

/-- For `G : Type u`, `CohomologicalDimensionLE` at auxiliary universe `u` is equivalent to
`CohomologicalDimensionLE` at `0`. -/
theorem cohomologicalDimensionLE_universe_iff :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n :=
  cohomologicalDimensionLE_max_iff.{0, u}

/-- `StrictCohomologicalDimensionLE` at auxiliary universe `max u v` is equivalent to
`StrictCohomologicalDimensionLE` at `v`. -/
theorem strictCohomologicalDimensionLE_max_iff :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔ StrictCohomologicalDimensionLE.{v} p G n := by
  rw [strictCohomologicalDimensionLE_iff, strictCohomologicalDimensionLE_iff]
  exact forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun i ↦ forall_congr' fun _ ↦
      (ofDiscreteModule ℤ G M).primaryComponent_continuousCohomology_max_eq_bot_iff i p

/-- For `G : Type u`, `StrictCohomologicalDimensionLE` at auxiliary universe `u` is equivalent to
`StrictCohomologicalDimensionLE` at `0`. -/
theorem strictCohomologicalDimensionLE_universe_iff :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n :=
  strictCohomologicalDimensionLE_max_iff.{0, u}

end Predicates

section Invariants

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- As predicates on `ℕ`, `CohomologicalDimensionLE` at `max u v` and at `v` are equal. -/
theorem cohomologicalDimensionLE_max_eq :
    CohomologicalDimensionLE.{max u v} p G = CohomologicalDimensionLE.{v} p G :=
  funext fun _ ↦ propext cohomologicalDimensionLE_max_iff

/-- As predicates on `ℕ`, `CohomologicalDimensionLE` at `u` and at `0` are equal. -/
theorem cohomologicalDimensionLE_universe_eq :
    CohomologicalDimensionLE.{u} p G = CohomologicalDimensionLE.{0} p G :=
  cohomologicalDimensionLE_max_eq.{0, u} p G

/-- As predicates on `ℕ`, `StrictCohomologicalDimensionLE` at `max u v` and at `v` are equal. -/
theorem strictCohomologicalDimensionLE_max_eq :
    StrictCohomologicalDimensionLE.{max u v} p G = StrictCohomologicalDimensionLE.{v} p G :=
  funext fun _ ↦ propext strictCohomologicalDimensionLE_max_iff

/-- As predicates on `ℕ`, `StrictCohomologicalDimensionLE` at `u` and at `0` are equal. -/
theorem strictCohomologicalDimensionLE_universe_eq :
    StrictCohomologicalDimensionLE.{u} p G = StrictCohomologicalDimensionLE.{0} p G :=
  strictCohomologicalDimensionLE_max_eq.{0, u} p G

/-- The `p`-cohomological dimension `cohomologicalDimensionAt` agrees at auxiliary universes
`max u v` and `v`. -/
theorem cohomologicalDimensionAt_max_eq :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G :=
  WithTop.eq_of_forall_le_coe_iff fun n ↦
    (cohomologicalDimensionAt_le_iff p G n).trans
      (cohomologicalDimensionLE_max_iff.trans (cohomologicalDimensionAt_le_iff p G n).symm)

/-- **`cd_p` does not depend on the redundant auxiliary coefficient universe**: for any topological
group `G : Type u`, `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G :=
  cohomologicalDimensionAt_max_eq.{0, u} p G

/-- The strict `p`-cohomological dimension `strictCohomologicalDimensionAt` agrees at auxiliary
universes `max u v` and `v`. -/
theorem strictCohomologicalDimensionAt_max_eq :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G :=
  WithTop.eq_of_forall_le_coe_iff fun n ↦
    (strictCohomologicalDimensionAt_le_iff p G n).trans
      (strictCohomologicalDimensionLE_max_iff.trans
        (strictCohomologicalDimensionAt_le_iff p G n).symm)

/-- **`scd_p` does not depend on the redundant auxiliary coefficient universe**: for any topological
group `G : Type u`,
`strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G :=
  strictCohomologicalDimensionAt_max_eq.{0, u} p G

/-- The cohomological dimension `cohomologicalDimension` agrees at auxiliary universes `max u v`
and `v`. -/
theorem cohomologicalDimension_max_eq :
    cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G :=
  WithTop.eq_of_forall_le_coe_iff fun n ↦
    (cohomologicalDimension_le_iff G n).trans
      ((forall₂_congr fun _ _ ↦ cohomologicalDimensionLE_max_iff).trans
        (cohomologicalDimension_le_iff G n).symm)

/-- **`cd` does not depend on the redundant auxiliary coefficient universe**: for any topological
group `G : Type u`, `cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G :=
  cohomologicalDimension_max_eq.{0, u} G

end Invariants

end TauCeti

end

section
open TauCeti

/-- Over the trivial topological group `PUnit.{u + 1}` in an arbitrary universe `u`, both ordinary
and strict `p`-cohomological dimension vanish at auxiliary universe `0`, and hence also at
auxiliary universe `u` by `cohomologicalDimensionAt_universe_eq` and
`strictCohomologicalDimensionAt_universe_eq`. -/
example (p : ℕ) :
    cohomologicalDimensionAt.{u} p PUnit.{u + 1} = 0 ∧
      strictCohomologicalDimensionAt.{u} p PUnit.{u + 1} = 0 := by
  have hcd₀ : cohomologicalDimensionAt.{0} p PUnit.{u + 1} = 0 := by
    rw [cohomologicalDimensionAt_eq_zero_iff]
    rintro M _ _ _ _ _ _ (_ | i) hi
    · exact (lt_irrefl 0 hi).elim
    · infer_instance
  have hscd₀ : strictCohomologicalDimensionAt.{0} p PUnit.{u + 1} = 0 := by
    rw [← nonpos_iff_eq_zero]
    refine (strictCohomologicalDimensionAt_le_iff p PUnit.{u + 1} 0).2 ?_
    rw [strictCohomologicalDimensionLE_iff]
    rintro M _ _ _ _ _ (_ | i) hi
    · exact (lt_irrefl 0 hi).elim
    · exact (AddSubgroup.eq_bot_iff_forall _).2 fun x _ ↦ Subsingleton.elim x 0
  exact ⟨(cohomologicalDimensionAt_universe_eq p PUnit.{u + 1}).trans hcd₀,
    (strictCohomologicalDimensionAt_universe_eq p PUnit.{u + 1}).trans hscd₀⟩

end
