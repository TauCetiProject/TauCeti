/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.BlockQuotient
public import TauCeti.Combinatorics.PermutationTriple.Primitivity.Basic
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

Distinct records have distinct isomorphism classes of triples. Exactly four records are
imprimitive, and each of them primitivizes to the record `2T1-2_2_1.1-a`: its monodromy action has
a maximal proper block with two translates, and the quotient by these translates is the triple of
that record, the double cover of the sphere branched over `0` and `1`.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Algorithm 2.3.1.
* LMFDB, [Belyi map records of degree at most four](https://www.lmfdb.org/Belyi/?deg=1-4).
-/

open Equiv MulAction
open scoped Pointwise

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

/-! ### Isomorphism classes and primitivizations -/

namespace SmallDegreeRecord

/-- The isomorphism class of the triple of a record, together with its degree. -/
def isoClass (r : SmallDegreeRecord) : Σ n, ConnectedIsoClass n :=
  ⟨r.degree, ConnectedIsoClass.mk r.triple⟩

theorem isoClass_def (r : SmallDegreeRecord) :
    r.isoClass = ⟨r.degree, ConnectedIsoClass.mk r.triple⟩ := (rfl)

/-- Records with the same isomorphism class have the same ordered cycle data. -/
theorem computedCycleData_eq_of_isoClass_eq {r r' : SmallDegreeRecord}
    (h : r.isoClass = r'.isoClass) : computedCycleData r = computedCycleData r' := by
  rw [isoClass_def, isoClass_def] at h
  obtain ⟨_, n, t, _⟩ := r
  obtain ⟨_, n', t', _⟩ := r'
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  exact Prod.ext rfl (cycleData_eq_of_equivalent
    (ConnectedIsoClass.mk_eq_mk_iff_equivalent.mp (eq_of_heq h)))

end SmallDegreeRecord

/-- Distinct frozen records have distinct isomorphism classes of triples. -/
theorem isoClass_nodup : (smallDegreeRecords.map SmallDegreeRecord.isoClass).Nodup := by
  have h := computedCycleData_nodup
  rw [List.Nodup, List.pairwise_map] at h ⊢
  exact h.imp fun hne heq ↦ hne (SmallDegreeRecord.computedCycleData_eq_of_isoClass_eq heq)

/-- Exactly four frozen records are imprimitive, all of degree four. -/
theorem map_label_filter_not_isPrimitive :
    (smallDegreeRecords.filter fun r ↦ ¬ r.triple.1.IsPrimitive).map SmallDegreeRecord.label =
      ["4T1-4_4_1.1.1.1-a", "4T1-4_4_2.2-a", "4T2-2.2_2.2_2.2-a", "4T3-4_2.2_2.1.1-a"] := by
  decide +kernel

/-- A finite certificate that a connected triple primitivizes to the double cover branched over
`0` and `1`: a nonempty block `B` with two translates, maximal among blocks, which neither `t.σ0`
nor `t.σ1` maps to itself. -/
private theorem exists_blockQuotient_eq_ofTwo_swap {n : ℕ} (t : ConnectedTriple n)
    (B : Finset (Fin n)) (hB : t.1.isBlockBool B = true) (hBne : B.Nonempty)
    (hmax : ∀ D : Finset (Fin n), t.1.isBlockBool D = true → B ⊆ D → D = B ∨ D = Finset.univ)
    (hcard : B.card * 2 = n) (h0 : B.image t.1.σ0 ≠ B) (h1 : B.image t.1.σ1 ≠ B) :
    ∃ C : Set (Fin n), IsBlock t.1.monodromyGroup C ∧ C.Nonempty ∧
      (∀ D : Set (Fin n), IsBlock t.1.monodromyGroup D → C ⊆ D → D = C ∨ D = Set.univ) ∧
      ∃ e : orbit t.1.monodromyGroup C ≃ Fin 2,
        t.1.blockQuotient C e = ofTwo (swap 0 1) (swap 0 1) := by
  classical
  have hB' := (t.1.isBlockBool_eq_true_iff B).mp hB
  have hBne' : (B : Set (Fin n)).Nonempty := Finset.coe_nonempty.mpr hBne
  have h := ncard_mul_eq_of_isBlock t.2.isPretransitive hB' hBne' (Finite.equivFin _)
  rw [Set.ncard_coe_finset] at h
  refine ⟨B, hB', hBne', fun D hD hsub ↦ ?_,
    Finite.equivFinOfCardEq (Nat.eq_of_mul_eq_mul_left hBne.card_pos (h.trans hcard.symm)), ?_⟩
  · rw [← Set.coe_toFinset D] at hD hsub ⊢
    rcases hmax D.toFinset ((t.1.isBlockBool_eq_true_iff _).mpr hD) (Finset.coe_subset.mp hsub)
      with hD | hD
    · exact Or.inl (by rw [hD])
    · exact Or.inr (by rw [hD, Finset.coe_univ])
  · refine blockQuotient_eq_ofTwo_swap _ _ _ ?_ ?_
    · rwa [← Finset.coe_image, Ne, Finset.coe_inj]
    · rwa [← Finset.coe_image, Ne, Finset.coe_inj]

/-- **The imprimitive frozen records primitivize to `2T1-2_2_1.1-a`.** The monodromy action of the
triple of every imprimitive record has a nonempty block, maximal among blocks, with two translates,
and the quotient by these translates has the isomorphism class of the record `2T1-2_2_1.1-a`. -/
theorem exists_isoClass_blockQuotient_eq {r : SmallDegreeRecord} (hr : r ∈ smallDegreeRecords)
    (hprim : ¬ r.triple.1.IsPrimitive) :
    ∃ B : Set (Fin r.degree), IsBlock r.triple.1.monodromyGroup B ∧ B.Nonempty ∧
      (∀ C : Set (Fin r.degree), IsBlock r.triple.1.monodromyGroup C → B ⊆ C →
        C = B ∨ C = Set.univ) ∧
      ∃ e : orbit r.triple.1.monodromyGroup B ≃ Fin 2, ∃ q ∈ smallDegreeRecords,
        q.label = "2T1-2_2_1.1-a" ∧
          q.isoClass = ⟨2, ConnectedIsoClass.mk
            ⟨r.triple.1.blockQuotient B e, r.triple.1.isConnected_blockQuotient B e⟩⟩ := by
  -- The quotient is the triple of the record `2T1-2_2_1.1-a` itself.
  suffices ∃ B : Set (Fin r.degree), IsBlock r.triple.1.monodromyGroup B ∧ B.Nonempty ∧
      (∀ C : Set (Fin r.degree), IsBlock r.triple.1.monodromyGroup C → B ⊆ C →
        C = B ∨ C = Set.univ) ∧
      ∃ e : orbit r.triple.1.monodromyGroup B ≃ Fin 2,
        r.triple.1.blockQuotient B e = ofTwo (swap 0 1) (swap 0 1) by
    obtain ⟨B, hB, hBne, hmax, e, he⟩ := this
    refine ⟨B, hB, hBne, hmax, e,
      ⟨"2T1-2_2_1.1-a", 2, ⟨ofTwo (swap 0 1) (swap 0 1), by decide⟩, by decide⟩,
      by simp [smallDegreeRecords], rfl, ?_⟩
    rw [SmallDegreeRecord.isoClass_def]
    exact congrArg (fun t ↦ (⟨2, ConnectedIsoClass.mk t⟩ : Σ n, ConnectedIsoClass n))
      (Subtype.ext he.symm)
  simp only [smallDegreeRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
  -- The nine primitive records are excluded by the finite primitivity test, and each of the four
  -- imprimitive ones has the block `{0, 2}`.
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd (by decide +kernel) hprim
    | exact exists_blockQuotient_eq_ofTwo_swap _ {0, 2} (by decide +kernel) (by decide)
        (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

end LMFDB
end PermutationTriple
end TauCeti
