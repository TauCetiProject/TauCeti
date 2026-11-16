/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Universe

/-!
# Independence of cohomological dimension from the auxiliary universe parameter

For a topological group `G : Type u`, the vanishing predicates `TauCeti.CohomologicalDimensionLE`
and `TauCeti.StrictCohomologicalDimensionLE` at universe parameter `v` quantify over discrete
coefficient modules `M : Type (max u v)`. Replacing `v` by `max u v` leaves the coefficient type
`Type (max u v)` unchanged while normalizing the auxiliary universe parameter passed to Mathlib's
`continuousCohomology`.

In particular, at `v = 0` (`max u 0 = u`), the invariants `cohomologicalDimensionAt.{u} p G` and
`cohomologicalDimensionAt.{0} p G` — as well as their strict and global counterparts — quantify over
the exact same discrete `G`-modules in `Type u`, even though the cohomology objects inside them are
not definitionally equal. Using the canonical additive equivalence
`TopRep.continuousCohomologyUniverseAddEquiv` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Universe`, which preserves triviality and
`p`-primary components, this file proves that the predicates and invariants at `max u v` and `v`
agree for every topological group `G`, and deduces the agreement between `v = u` and `v = 0`.

## Main results

* `TauCeti.cohomologicalDimensionLE_max_iff`, `TauCeti.strictCohomologicalDimensionLE_max_iff`:
  the ordinary and strict vanishing predicates at universe parameters `max u v` and `v` are
  equivalent.
* `TauCeti.cohomologicalDimensionAt_max_eq`, `TauCeti.strictCohomologicalDimensionAt_max_eq`,
  `TauCeti.cohomologicalDimension_max_eq`: `cd_p`, `scd_p`, and `cd` agree at universe parameters
  `max u v` and `v`.
* `TauCeti.cohomologicalDimensionLE_universe_iff`,
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: equivalence of the vanishing predicates at
  `v = u` and `v = 0`.
* `TauCeti.cohomologicalDimensionAt_universe_eq`,
  `TauCeti.strictCohomologicalDimensionAt_universe_eq`,
  `TauCeti.cohomologicalDimension_universe_eq`: **`cd_p`, `scd_p`, and `cd` agree at `v = u` and
  `v = 0`** for every topological group `G : Type u`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3,
  (3.3.1): `cd_p G` and `scd_p G` are invariants of the discrete `G`-modules over `G`.
* J.-P. Serre, *Galois Cohomology*, Ch. I §3.1.
-/

public section

namespace TauCeti

section MaxUniverse

universe v u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The ordinary cohomological-dimension vanishing predicate at universe parameter `max u v` is
equivalent to the one at universe parameter `v`. -/
theorem cohomologicalDimensionLE_max_iff (n : ℕ) :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff, cohomologicalDimensionLE_iff]
  exact forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ imp_congr_right fun _ ↦ forall_congr' fun i ↦
      imp_congr_right fun _ ↦
        (ofDiscreteModule ℤ G M).subsingleton_continuousCohomology_max_iff.{0, u, v} i

/-- The strict cohomological-dimension vanishing predicate at universe parameter `max u v` is
equivalent to the one at universe parameter `v`. -/
theorem strictCohomologicalDimensionLE_max_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔ StrictCohomologicalDimensionLE.{v} p G n := by
  rw [strictCohomologicalDimensionLE_iff, strictCohomologicalDimensionLE_iff]
  exact forall_congr' fun M ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun i ↦ imp_congr_right fun _ ↦
      (ofDiscreteModule ℤ G M).primaryComponent_continuousCohomology_max_eq_bot_iff.{0, u, v}
        i p

/-- **`cd_p G` agrees at universe parameters `max u v` and `v`**, for every topological group
`G`. -/
theorem cohomologicalDimensionAt_max_eq :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G :=
  WithTop.eq_of_forall_le_coe_iff fun n ↦
    (cohomologicalDimensionAt_le_iff p G n).trans
      ((cohomologicalDimensionLE_max_iff p G n).trans
        (cohomologicalDimensionAt_le_iff p G n).symm)

/-- **`scd_p G` agrees at universe parameters `max u v` and `v`**, for every topological group
`G`. -/
theorem strictCohomologicalDimensionAt_max_eq :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G :=
  WithTop.eq_of_forall_le_coe_iff fun n ↦
    (strictCohomologicalDimensionAt_le_iff p G n).trans
      ((strictCohomologicalDimensionLE_max_iff p G n).trans
        (strictCohomologicalDimensionAt_le_iff p G n).symm)

/-- **`cd G` agrees at universe parameters `max u v` and `v`**, for every topological group `G`. -/
theorem cohomologicalDimension_max_eq :
    cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G :=
  WithTop.eq_of_forall_le_coe_iff fun n ↦
    (cohomologicalDimension_le_iff G n).trans
      ((forall_congr' fun q ↦ imp_congr_right fun _ ↦ cohomologicalDimensionLE_max_iff q G n).trans
        (cohomologicalDimension_le_iff G n).symm)

end MaxUniverse

section SameUniverse

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For `G : Type u`, `CohomologicalDimensionLE` agrees at auxiliary universe parameters `u` and
`0`, both quantifying over discrete `p`-primary torsion `G`-modules in `Type u`. -/
theorem cohomologicalDimensionLE_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n :=
  cohomologicalDimensionLE_max_iff.{0, u} p G n

/-- For `G : Type u`, `StrictCohomologicalDimensionLE` agrees at auxiliary universe parameters `u`
and `0`, both quantifying over discrete `G`-modules in `Type u`. -/
theorem strictCohomologicalDimensionLE_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n :=
  strictCohomologicalDimensionLE_max_iff.{0, u} p G n

/-- **`cd_p` does not depend on the auxiliary coefficient universe.** For every topological group
`G : Type u`, `cohomologicalDimensionAt.{u} p G` equals `cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G :=
  cohomologicalDimensionAt_max_eq.{0, u} p G

/-- **`scd_p` does not depend on the auxiliary coefficient universe.** For every topological group
`G : Type u`, `strictCohomologicalDimensionAt.{u} p G` equals
`strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G :=
  strictCohomologicalDimensionAt_max_eq.{0, u} p G

/-- **`cd` does not depend on the auxiliary coefficient universe.** For every topological group
`G : Type u`, `cohomologicalDimension.{u} G` equals `cohomologicalDimension.{0} G`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G :=
  cohomologicalDimension_max_eq.{0, u} G

end SameUniverse

end TauCeti
