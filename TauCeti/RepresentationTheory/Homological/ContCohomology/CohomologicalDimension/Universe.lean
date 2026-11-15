/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Map.Basic

/-!
# Independence of cohomological dimension from the extra coefficient universe

For a topological group `G : Type u`, the vanishing predicates `CohomologicalDimensionLE.{v} p G n`
and `StrictCohomologicalDimensionLE.{v} p G n` quantify over discrete `G`-modules in
`Type (max u v)`. At the two parameters `v = u` and `v = 0` this is the very same universe `Type u`
of coefficient modules, because `max u u = u = max u 0`; however, inside each predicate the
canonical cohomology group `continuousCohomology i (ofDiscreteModule ℤ G M)` is instantiated at the
extra universe parameter `v = u` on one side and `v = 0` on the other, so the two cohomology groups
are not definitionally equal.

Using the canonical topological `ℤ`-linear equivalence
`TauCeti.ContCohomology.continuousCohomologyUniverseCLE (ofDiscreteModule ℤ G M) i` between the two
continuous cohomology groups in every degree `i`, this file proves that both vanishing predicates
and all three dimension invariants agree at `v = u` and `v = 0` for every topological group `G`,
without any compactness, profiniteness or smallness assumption:

* `TauCeti.cohomologicalDimensionLE_universe_iff` and
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: equivalence of the ordinary and strict
  vanishing predicates at `v = u` and `v = 0`;
* `TauCeti.cohomologicalDimensionAt_universe_eq`:
  `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`;
* `TauCeti.strictCohomologicalDimensionAt_universe_eq`:
  `strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`;
* `TauCeti.cohomologicalDimension_universe_eq`:
  `cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §3.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.1.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Extra-universe invariance of `CohomologicalDimensionLE`.** For `G : Type u`, the ordinary
vanishing predicate at the extra universe parameter `u` is equivalent to that at `0`. -/
theorem cohomologicalDimensionLE_universe_iff (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n := by
  rw [cohomologicalDimensionLE_iff, cohomologicalDimensionLE_iff]
  constructor <;> intro h M _ _ _ _ _ hM i hi
  · have := h M hM i hi
    exact (ContCohomology.continuousCohomologyUniverseCLE
      (ofDiscreteModule ℤ G M) i).symm.toEquiv.subsingleton
  · have := h M hM i hi
    exact (ContCohomology.continuousCohomologyUniverseCLE
      (ofDiscreteModule ℤ G M) i).toEquiv.subsingleton

/-- **Extra-universe invariance of `StrictCohomologicalDimensionLE`.** For `G : Type u`, the strict
vanishing predicate at the extra universe parameter `u` is equivalent to that at `0`. -/
theorem strictCohomologicalDimensionLE_universe_iff (n : ℕ) :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n := by
  have aux {A B : Type u} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
      (hA : AddCommGroup.primaryComponent A p = ⊥) :
      AddCommGroup.primaryComponent B p = ⊥ := by
    refine (AddSubgroup.eq_bot_iff_forall _).2 fun y hy ↦ ?_
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 hy
    refine e.symm.injective ?_
    have hy' : e.symm y ∈ AddCommGroup.primaryComponent A p :=
      AddCommGroup.mem_primaryComponent.2 ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
    rw [hA, AddSubgroup.mem_bot] at hy'
    rw [hy', map_zero]
  rw [strictCohomologicalDimensionLE_iff, strictCohomologicalDimensionLE_iff]
  constructor <;> intro h M _ _ _ _ _ i hi
  · exact aux
      (ContCohomology.continuousCohomologyUniverseCLE
        (ofDiscreteModule ℤ G M) i).toLinearEquiv.toAddEquiv
      (h M i hi)
  · exact aux
      (ContCohomology.continuousCohomologyUniverseCLE
        (ofDiscreteModule ℤ G M) i).symm.toLinearEquiv.toAddEquiv
      (h M i hi)

/-- **`cd_p` does not depend on the extra coefficient universe.** For every topological group
`G : Type u`, `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G := by
  refine eq_of_forall_ge_iff fun c ↦ c.recTopCoe (by simp) fun n ↦ ?_
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionAt_le_iff,
    cohomologicalDimensionLE_universe_iff]

/-- **`scd_p` does not depend on the extra coefficient universe.** For every topological group
`G : Type u`, `strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G := by
  refine eq_of_forall_ge_iff fun c ↦ c.recTopCoe (by simp) fun n ↦ ?_
  rw [strictCohomologicalDimensionAt_le_iff, strictCohomologicalDimensionAt_le_iff,
    strictCohomologicalDimensionLE_universe_iff]

/-- **`cd` does not depend on the extra coefficient universe.** For every topological group
`G : Type u`, `cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G := by
  refine eq_of_forall_ge_iff fun c ↦ c.recTopCoe (by simp) fun n ↦ ?_
  simp only [cohomologicalDimension_le_iff, cohomologicalDimensionLE_universe_iff]

end TauCeti
