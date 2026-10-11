/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.SmallDegrees
public import TauCeti.GroupTheory.Perm.ComputedCycleType

/-!
# The low-degree LMFDB Belyi records

This file records the thirteen LMFDB Belyi-map entries of degree at most four as connected
permutation triples, and checks that their branch-point orbits are exactly the low-degree
branch-point orbits. The stored permutations use the database's left-to-right composition
convention, so the triples below use their componentwise inverses.

The comparison certifies the listed records against the complete combinatorial classification;
it does not assert that the database contains every ordered triple or every Belyi map.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Algorithm 2.3.1.
* LMFDB, [Belyi map records of degree at most four](https://www.lmfdb.org/Belyi/?deg=1-4).
-/

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-- A frozen low-degree LMFDB record, represented by its label and monodromy triple in Tau
Ceti's multiplication convention. -/
structure SmallDegreeRecord where
  /-- The LMFDB label of this Belyi-map record. -/
  label : String
  /-- The degree of the corresponding Belyi map. -/
  degree : ℕ
  /-- The record's monodromy triple in Tau Ceti's multiplication convention. -/
  triple : ConnectedTriple degree
  degree_le_four : degree ≤ 4

private def r3 : Equiv.Perm (Fin 3) := [(0 : Fin 3), 1, 2].formPerm
private def r4 : Equiv.Perm (Fin 4) := [(0 : Fin 4), 1, 2, 3].formPerm
private def c012 : Equiv.Perm (Fin 4) := [(0 : Fin 4), 1, 2].formPerm
private def c013 : Equiv.Perm (Fin 4) := [(0 : Fin 4), 1, 3].formPerm
private def c023 : Equiv.Perm (Fin 4) := [(0 : Fin 4), 2, 3].formPerm
private def c132 : Equiv.Perm (Fin 4) := [(1 : Fin 4), 3, 2].formPerm

/-- The thirteen degree-at-most-four records in the frozen LMFDB Belyi table. Each entry is the
componentwise inverse of the stored triple, expressed as a connected triple. -/
def smallDegreeRecords : List SmallDegreeRecord :=
  [ ⟨"1T1-1_1_1-a", 1, ⟨ofTwo 1 1, by decide⟩, by decide⟩
  , ⟨"2T1-2_2_1.1-a", 2, ⟨ofTwo (Equiv.swap 0 1) (Equiv.swap 0 1), by decide⟩, by decide⟩
  , ⟨"3T1-3_3_1.1.1-a", 3, ⟨ofTwo r3⁻¹ r3, by decide⟩, by decide⟩
  , ⟨"3T1-3_3_3-a", 3, ⟨ofTwo r3⁻¹ r3⁻¹, by decide⟩, by decide⟩
  , ⟨"3T2-3_2.1_2.1-a", 3,
      ⟨ofTwo r3⁻¹ (Equiv.swap 1 2), by decide⟩, by decide⟩
  , ⟨"4T1-4_4_1.1.1.1-a", 4, ⟨ofTwo r4⁻¹ r4, by decide⟩, by decide⟩
  , ⟨"4T1-4_4_2.2-a", 4, ⟨ofTwo r4⁻¹ r4⁻¹, by decide⟩, by decide⟩
  , ⟨"4T2-2.2_2.2_2.2-a", 4,
      ⟨ofTwo (Equiv.swap 0 3 * Equiv.swap 1 2)
        (Equiv.swap 0 1 * Equiv.swap 2 3), by decide⟩, by decide⟩
  , ⟨"4T3-4_2.2_2.1.1-a", 4,
      ⟨ofTwo r4⁻¹ (Equiv.swap 0 1 * Equiv.swap 2 3), by decide⟩, by decide⟩
  , ⟨"4T4-3.1_3.1_2.2-a", 4,
      ⟨ofTwo c012⁻¹ c013⁻¹, by decide⟩, by decide⟩
  , ⟨"4T4-3.1_3.1_3.1-a", 4,
      ⟨ofTwo c012⁻¹ c023⁻¹, by decide⟩, by decide⟩
  , ⟨"4T5-4_3.1_2.1.1-a", 4,
      ⟨ofTwo r4⁻¹ c132⁻¹, by decide⟩, by decide⟩
  , ⟨"4T5-4_4_3.1-a", 4,
      ⟨ofTwo r4⁻¹ ([(0 : Fin 4), 2, 3, 1].formPerm)⁻¹, by decide⟩, by decide⟩ ]

/-- The frozen table contains thirteen records of degree at most four. -/
theorem smallDegreeRecords_length : smallDegreeRecords.length = 13 := by decide

/-- The full ordered cycle datum attached to an LMFDB record. -/
def computedCycleData (r : SmallDegreeRecord) := (r.degree, r.triple.1.cycleData)

/-- The cycle partitions with their branch-point order forgotten. -/
def computedUnorderedCycleData (r : SmallDegreeRecord) : ℕ × Multiset (Multiset ℕ) :=
  (r.degree, r.triple.1.unorderedCycleData)

/-- The thirteen frozen records have pairwise distinct ordered cycle data, hence represent
distinct connected-triple isomorphism classes in their respective degrees. -/
theorem computedCycleData_nodup : (smallDegreeRecords.map computedCycleData).Nodup := by
  decide +kernel

/-- No two frozen records lie in the same branch-point orbit of cycle data. -/
theorem computedUnorderedCycleData_nodup :
    (smallDegreeRecords.map computedUnorderedCycleData).Nodup := by
  unfold computedUnorderedCycleData
  simp only [unorderedCycleData_def]
  decide +kernel

/-- The unordered cycle data of the frozen records give the explicit thirteen-entry
degree-at-most-four table. -/
theorem computedUnorderedCycleData_eq_small_degree_table :
    (smallDegreeRecords.map computedUnorderedCycleData).toFinset =
      { (1, {{1}, {1}, {1}}),
        (2, {{1, 1}, {2}, {2}}),
        (3, {{1, 1, 1}, {3}, {3}}),
        (3, {{2, 1}, {2, 1}, {3}}),
        (3, {{3}, {3}, {3}}),
        (4, {{1, 1, 1, 1}, {4}, {4}}),
        (4, {{2, 1, 1}, {2, 2}, {4}}),
        (4, {{2, 2}, {2, 2}, {2, 2}}),
        (4, {{2, 2}, {4}, {4}}),
        (4, {{2, 2}, {3, 1}, {3, 1}}),
        (4, {{3, 1}, {3, 1}, {3, 1}}),
        (4, {{3, 1}, {4}, {4}}),
        (4, {{2, 1, 1}, {3, 1}, {4}}) } := by
  unfold computedUnorderedCycleData
  simp only [unorderedCycleData_def]
  decide +kernel

/-- The displayed unordered data are precisely the degree-at-most-four branch-point orbits
from the complete connected-triple tables. -/
theorem unorderedCycleData_eq_classification (n : ℕ) (hn : n ≤ 4) :
  (((smallDegreeRecords.filter (fun r => r.degree = n)).map
    (fun r => (computedUnorderedCycleData r).2)).toFinset) =
      (Finset.univ : Finset (ConnectedTriple n)).image
        (fun t => t.1.unorderedCycleData) := by
  interval_cases n
  · decide +kernel
  · rw [PermutationTriple.image_unorderedCycleData_one]
    unfold computedUnorderedCycleData
    simp only [unorderedCycleData_def]
    decide +kernel
  · rw [PermutationTriple.image_unorderedCycleData_two]
    unfold computedUnorderedCycleData
    simp only [unorderedCycleData_def]
    decide +kernel
  · rw [PermutationTriple.image_unorderedCycleData_three]
    unfold computedUnorderedCycleData
    simp only [unorderedCycleData_def]
    decide +kernel
  · rw [PermutationTriple.image_unorderedCycleData_four]
    unfold computedUnorderedCycleData
    simp only [unorderedCycleData_def]
    decide +kernel

end LMFDB
end PermutationTriple
end TauCeti
