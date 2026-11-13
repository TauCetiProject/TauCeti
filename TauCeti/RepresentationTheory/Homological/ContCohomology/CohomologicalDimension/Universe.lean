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

For a topological group `G : Type u`, the vanishing predicates `CohomologicalDimensionLE.{v} p G n`
and `StrictCohomologicalDimensionLE.{v} p G n` quantify over discrete `G`-modules
`M : Type (max u v)` with a continuous `G`-action and read Mathlib's continuous cohomology
`continuousCohomology.{0, u, v} i (ofDiscreteModule ℤ G M)`.

At `v = u` and at `v = 0` the coefficient modules range over the very same universe `Type u`
(`max u u = max u 0 = u`), while the canonical cohomology objects inside the predicates carry
different auxiliary universe parameters and are not definitionally equal. Transporting vanishing
and `p`-primary components across `TopRep.continuousCohomologyUniverseIso` shows that both
predicates, and hence `cohomologicalDimensionAt` (`cd_p`), `strictCohomologicalDimensionAt`
(`scd_p`), and `cohomologicalDimension` (`cd`), agree at `v = u` and `v = 0` for every topological
group `G`, with no compactness, profiniteness, or smallness hypothesis on `G` and no primality
hypothesis on `p`.

## Main results

* `TauCeti.cohomologicalDimensionLE_universe_iff` and
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: equivalence of the ordinary and strict
  vanishing predicates at `v = u` and `v = 0`.
* `TauCeti.cohomologicalDimensionAt_universe_eq`: `cd_p G` at `v = u` equals `cd_p G` at `v = 0`.
* `TauCeti.strictCohomologicalDimensionAt_universe_eq`: `scd_p G` at `v = u` equals `scd_p G` at
  `v = 0`.
* `TauCeti.cohomologicalDimension_universe_eq`: `cd G` at `v = u` equals `cd G` at `v = 0`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §3.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.1.
-/

public section

namespace TauCeti

universe u

section Predicates

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

/-- `CohomologicalDimensionLE.{u} p G n` transfers to parameter `0`. -/
theorem CohomologicalDimensionLE.toUniverseZero
    (h : CohomologicalDimensionLE.{u} p G n) : CohomologicalDimensionLE.{0} p G n := by
  rw [cohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ hM i hi
  exact ((ofDiscreteModule ℤ G M).subsingleton_continuousCohomology_universe_iff i).1 (h M hM i hi)

/-- `CohomologicalDimensionLE.{0} p G n` transfers to parameter `u`. -/
theorem CohomologicalDimensionLE.ofUniverseZero
    (h : CohomologicalDimensionLE.{0} p G n) : CohomologicalDimensionLE.{u} p G n := by
  rw [cohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ hM i hi
  exact ((ofDiscreteModule ℤ G M).subsingleton_continuousCohomology_universe_iff i).2 (h M hM i hi)

/-- `StrictCohomologicalDimensionLE.{u} p G n` transfers to parameter `0`. -/
theorem StrictCohomologicalDimensionLE.toUniverseZero
    (h : StrictCohomologicalDimensionLE.{u} p G n) : StrictCohomologicalDimensionLE.{0} p G n := by
  rw [strictCohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ i hi
  exact ((ofDiscreteModule ℤ G M).primaryComponent_continuousCohomology_universe_eq_bot_iff i p).1
    (h M i hi)

/-- `StrictCohomologicalDimensionLE.{0} p G n` transfers to parameter `u`. -/
theorem StrictCohomologicalDimensionLE.ofUniverseZero
    (h : StrictCohomologicalDimensionLE.{0} p G n) : StrictCohomologicalDimensionLE.{u} p G n := by
  rw [strictCohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ i hi
  exact ((ofDiscreteModule ℤ G M).primaryComponent_continuousCohomology_universe_eq_bot_iff i p).2
    (h M i hi)

end Predicates

section Invariants

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The ordinary vanishing predicate agrees at universe parameters `u` and `0`.** -/
theorem cohomologicalDimensionLE_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n :=
  ⟨CohomologicalDimensionLE.toUniverseZero, CohomologicalDimensionLE.ofUniverseZero⟩

/-- **The strict vanishing predicate agrees at universe parameters `u` and `0`.** -/
theorem strictCohomologicalDimensionLE_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n :=
  ⟨StrictCohomologicalDimensionLE.toUniverseZero, StrictCohomologicalDimensionLE.ofUniverseZero⟩

/-- **`cd_p` does not depend on the extra coefficient universe (`v = u` vs `v = 0`).** -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionAt_le_iff]
    exact cohomologicalDimensionLE_universe_iff p G n

/-- **`scd_p` does not depend on the extra coefficient universe (`v = u` vs `v = 0`).** -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [strictCohomologicalDimensionAt_le_iff, strictCohomologicalDimensionAt_le_iff]
    exact strictCohomologicalDimensionLE_universe_iff p G n

/-- **`cd` does not depend on the extra coefficient universe (`v = u` vs `v = 0`).** -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [cohomologicalDimension_le_iff, cohomologicalDimension_le_iff]
    exact forall₂_congr fun q _ ↦ cohomologicalDimensionLE_universe_iff q G n

end Invariants

end TauCeti
