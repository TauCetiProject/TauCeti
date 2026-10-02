/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.OfTriple
-- Kernel reduction of the finite searches needs the unexposed cycle-data and cycle-factor bodies.
import all TauCeti.Combinatorics.PermutationTriple.CycleData
import all Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Classification of connected triples in small degrees

Through degree three, the ordered full cycle partitions determine a connected permutation
triple up to simultaneous relabeling. Consequently every inhabited ordered passport in these
degrees has size one, even without using its monodromy subgroup to distinguish classes.

The cycle-data tables list all three degree-two classes and all seven degree-three classes.
In degree three, the three cyclic genus-zero classes have an unramified branch point, the
three nonabelian classes have two transpositions, and the remaining class has three full
cycles and genus one. Fixed points are included in every displayed partition.

The finite classifications are checked by kernel reduction, using Mathlib's permutation
partition and Tau Ceti's decidable relabeling relation. No representatives are selected.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

public section

namespace TauCeti

namespace PermutationTriple

private theorem equivalent_of_cycleData_eq_two :
    ∀ t t' : ConnectedTriple 2, t.1.cycleData = t'.1.cycleData → Equivalent t.1 t'.1 := by
  decide +kernel

private theorem equivalent_of_cycleData_eq_three :
    ∀ t t' : ConnectedTriple 3, t.1.cycleData = t'.1.cycleData → Equivalent t.1 t'.1 := by
  decide +kernel

/-- Through degree three, the ordered full cycle partitions classify connected triples up to
simultaneous relabeling. The monodromy group is not needed as an additional invariant. -/
theorem equivalent_iff_cycleData_eq_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t t' : ConnectedTriple n) : Equivalent t.1 t'.1 ↔ t.1.cycleData = t'.1.cycleData := by
  refine ⟨cycleData_eq_of_equivalent, fun h => ?_⟩
  have hn0 := t.2.ne_zero
  interval_cases n
  · exact (hn0 rfl).elim
  · have ht : t.1 = t'.1 := Subsingleton.elim _ _
    rw [ht]
    exact equivalent_iff_exists_smul_eq.mpr ⟨1, one_smul _ _⟩
  · exact equivalent_of_cycleData_eq_two t t' h
  · exact equivalent_of_cycleData_eq_three t t' h

/-- The unique ordered cycle datum in degree one. -/
theorem image_cycleData_one :
    (Finset.univ : Finset (ConnectedTriple 1)).image (fun t => t.1.cycleData) =
      {({1}, {1}, {1})} := by
  decide +kernel

/-- The complete table of ordered full cycle data in degree two. The three classes differ by
which branch point is unramified. -/
theorem image_cycleData_two :
    (Finset.univ : Finset (ConnectedTriple 2)).image (fun t => t.1.cycleData) =
      {({1, 1}, {2}, {2}), ({2}, {1, 1}, {2}), ({2}, {2}, {1, 1})} := by
  decide +kernel

/-- The complete table of ordered full cycle data in degree three. There are three cyclic
spherical classes, three nonabelian spherical classes, and one cyclic Euclidean class. -/
theorem image_cycleData_three :
    (Finset.univ : Finset (ConnectedTriple 3)).image (fun t => t.1.cycleData) =
      {({1, 1, 1}, {3}, {3}), ({3}, {1, 1, 1}, {3}), ({3}, {3}, {1, 1, 1}),
        ({2, 1}, {2, 1}, {3}), ({2, 1}, {3}, {2, 1}), ({3}, {2, 1}, {2, 1}),
        ({3}, {3}, {3})} := by
  decide +kernel

/-- Through degree three, the Euler characteristic is zero for the triple with three full
three-cycles, and two for every other connected triple. -/
theorem eulerChar_eq_ite_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t : ConnectedTriple n) :
    t.1.eulerChar = if t.1.cycleData = ({3}, {3}, {3}) then 0 else 2 := by
  have hn0 := t.2.ne_zero
  have hd : t.1.cycleData ∈
      (Finset.univ : Finset (ConnectedTriple n)).image (fun s => s.1.cycleData) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ t)
  rw [eulerChar_eq_cycleCounts, cycleCounts_eq_card_cycleData]
  interval_cases n
  · exact (hn0 rfl).elim
  · rw [image_cycleData_one] at hd
    simp only [Finset.mem_singleton] at hd
    norm_num [hd]
  · rw [image_cycleData_two] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd | hd <;> norm_num [hd]
  · rw [image_cycleData_three] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd <;> norm_num [hd] <;> decide

/-- The unique positive-genus class through degree three is the class with full cycle
partition `[3]` at all three branch points, and it has genus one. -/
theorem genus_eq_ite_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t : ConnectedTriple n) :
    t.1.genus = if t.1.cycleData = ({3}, {3}, {3}) then 1 else 0 := by
  rw [genus_def, eulerChar_eq_ite_of_degree_le_three hn t]
  split_ifs <;> norm_num

/-- The class with three full three-cycles is Euclidean; every other connected class through
degree three is spherical. -/
theorem geometryType_eq_ite_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t : ConnectedTriple n) :
    t.1.geometryType =
      if t.1.cycleData = ({3}, {3}, {3}) then .euclidean else .spherical := by
  split_ifs with h
  · apply (geometryType_eq_euclidean_iff t.1).mpr
    simp only [← orderTriple_σ0, ← orderTriple_σ1, ← orderTriple_σinf,
      orderTriple_eq_lcm_cycleData]
    norm_num [h]
  · apply (geometryType_eq_spherical_iff t.1).mpr
    simp only [← orderTriple_σ0, ← orderTriple_σ1, ← orderTriple_σinf,
      orderTriple_eq_lcm_cycleData]
    have hn0 := t.2.ne_zero
    have hd : t.1.cycleData ∈
        (Finset.univ : Finset (ConnectedTriple n)).image (fun s => s.1.cycleData) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ t)
    interval_cases n
    · exact (hn0 rfl).elim
    · rw [image_cycleData_one] at hd
      simp only [Finset.mem_singleton] at hd
      norm_num [hd]
    · rw [image_cycleData_two] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with hd | hd | hd <;> norm_num [hd]
    · rw [image_cycleData_three] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with hd | hd | hd | hd | hd | hd | hd
      all_goals norm_num [hd]
      exact h hd

end PermutationTriple

namespace PassportSpec

variable {n : ℕ}

/-- Through degree three, an inhabited ordered passport consists of exactly one isomorphism
class. This is stronger than bounding its size: the class is identified by any member. -/
theorem classSet_eq_singleton_of_degree_le_three (hn : n ≤ 3) (P : PassportSpec n)
    (t : ConnectedTriple n) (ht : HasPassport t P) :
    P.classSet = {ConnectedIsoClass.mk t} := by
  classical
  ext c
  obtain ⟨s, rfl⟩ := ConnectedIsoClass.mk_surjective c
  simp only [mem_classSet, ConnectedIsoClass.hasPassport_mk, Finset.mem_singleton]
  constructor
  · intro hs
    apply ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr
    exact (PermutationTriple.equivalent_iff_cycleData_eq_of_degree_le_three hn s t).mpr
      (cycleData_eq_of_hasPassport hs ht)
  · intro h
    have hc := (ConnectedIsoClass.hasPassport_mk t P).mpr ht
    rw [← h] at hc
    exact (ConnectedIsoClass.hasPassport_mk s P).mp hc

/-- Through degree three, a passport has size one exactly when it is inhabited. Admissibility
alone is not substituted for existence of a product-one triple. -/
theorem passportSize_eq_one_iff_of_degree_le_three (hn : n ≤ 3) (P : PassportSpec n) :
    P.passportSize = 1 ↔ ∃ t : ConnectedTriple n, HasPassport t P := by
  constructor
  · intro h
    exact (passportSize_pos_iff P).mp (by omega)
  · rintro ⟨t, ht⟩
    rw [passportSize_def, classSet_eq_singleton_of_degree_le_three hn P t ht,
      Finset.card_singleton]

/-- Every ordered passport in degree at most three has size zero or one. -/
theorem passportSize_le_one_of_degree_le_three (hn : n ≤ 3) (P : PassportSpec n) :
    P.passportSize ≤ 1 := by
  by_cases h : 0 < P.passportSize
  · obtain ⟨t, ht⟩ := (passportSize_pos_iff P).mp h
    rw [(passportSize_eq_one_iff_of_degree_le_three hn P).mpr ⟨t, ht⟩]
  · omega

end PassportSpec

namespace ConnectedTriple

/-- The ordered passport of any connected triple through degree three has size one. -/
theorem passportSize_passportOf_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t : ConnectedTriple n) : t.passportOf.passportSize = 1 :=
  (PassportSpec.passportSize_eq_one_iff_of_degree_le_three hn t.passportOf).mpr
    ⟨t, t.hasPassport_passportOf⟩

end ConnectedTriple

end TauCeti
