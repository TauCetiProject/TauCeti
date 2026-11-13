/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.LMFDB.CertificationLevel
public import TauCeti.Combinatorics.PermutationTriple.LMFDB.PassportRecord.Examples

/-!
# The map rows `3T2-3_2.1_2.1-a` and `4T1-4_4_2.2-a`

This file carries the map rows of the LMFDB table of Belyi maps belonging to the passport rows
`TauCeti.PermutationTriple.LMFDB.s3PassportRecord` and
`TauCeti.PermutationTriple.LMFDB.torusPassportRecord` through the map-row certificates. Each row is
valid for its passport (`TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor`), its stored map
label extends its passport label and agrees with its stored partitions, it computes the
aggregations `num_orbits = 1` and `maxdegbf = 1` of its passport row, and its stored triple
represents the single isomorphism class of the passport, so that its stored orbit size is the
stored passport size.

The genus-zero row `3T2-3_2.1_2.1-a` stores the triple `(1,2,3)`, `(2,3)`, `(1,2)`, which is
`finRotate 3`, `swap 1 2`, `swap 0 1` on zero-based sheets. These permutations satisfy
`σ0 * σ1 * σinf = 1`, the database's left-to-right relation, and do not satisfy
`σinf * σ1 * σ0 = 1`, the relation of a `TauCeti.PermutationTriple`
(`TauCeti.PermutationTriple.LMFDB.mul_mul_ne_one_s3StoredTriple`). So the stored data is read
correctly only through the translation `TauCeti.PermutationTriple.LMFDB.StoredTriple.toTriple`,
which relabels it to `TauCeti.PermutationTriple.s3Triple`. The passport row `3T2-3_2.1_2.1` is
primitive and stores this map row as its own primitivization, and the row certifies it
(`TauCeti.PermutationTriple.LMFDB.isPrimitivizationOf_s3PassportRecord`).

The genus-one row `4T1-4_4_2.2-a` is the superelliptic curve `y⁴ = t (t - 1)` with `β = t`. Its
stored triple here is the database form, under
`TauCeti.PermutationTriple.equivOppositeConvention`, of `TauCeti.PermutationTriple.torusTriple`.
This triple is a representative of the passport chosen in this file and is not checked against the
literal stored permutations of the frozen record; since the passport has a single isomorphism
class, any representative is isomorphic to it.

The equations, the curve links, and the labels of related objects of both rows are carrier data
that validity does not read (`TauCeti.PermutationTriple.LMFDB.BelyiRecord.isValidFor_congr`); they
are left empty here rather than reproduced. In particular `curveLabel` does not record the link of
`4T1-4_4_2.2-a` to an elliptic curve over `ℚ`. The equality of each stored orbit size with the size
of the Galois orbit of the isomorphism class is an orbit certificate, which these rows do not
carry.

## Main results

* `TauCeti.PermutationTriple.LMFDB.mul_mul_ne_one_s3StoredTriple`: the stored triple of
  `3T2-3_2.1_2.1-a` does not satisfy this library's relation.
* `TauCeti.PermutationTriple.LMFDB.equivalent_toTriple_s3StoredTriple`: its translation is
  isomorphic to `s3Triple`.
* `TauCeti.PermutationTriple.LMFDB.isValidFor_s3BelyiRecord` and
  `TauCeti.PermutationTriple.LMFDB.isValidFor_torusBelyiRecord`: the two map rows are valid.
* `TauCeti.PermutationTriple.LMFDB.mapRowClasses_s3PassportRecord` and
  `TauCeti.PermutationTriple.LMFDB.mapRowClasses_torusPassportRecord`: each map row represents
  exactly the classes of its passport.
* `TauCeti.PermutationTriple.LMFDB.isPrimitivizationOf_s3PassportRecord`: the map row
  `3T2-3_2.1_2.1-a` certifies the primitivization of its own passport row.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Proceedings of the
  Thirteenth Algorithmic Number Theory Symposium, Open Book Series 2, 2019, §2.
* LMFDB, [Belyi map records of degree at most four](https://www.lmfdb.org/Belyi/?deg=1-4).
-/

open Equiv

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-! ### The genus-zero row `3T2-3_2.1_2.1-a` -/

/-- The stored triple of the map row `3T2-3_2.1_2.1-a`, in the database's convention: the stored
cycles `(1,2,3)`, `(2,3)` and `(1,2)`, which are `finRotate 3`, `swap 1 2` and `swap 0 1` on
zero-based sheets. -/
@[expose] def s3StoredTriple : StoredTriple 3 := ⟨(finRotate 3, swap 1 2, swap 0 1), by decide⟩

/-- The stored triple of `3T2-3_2.1_2.1-a` does not satisfy `σinf * σ1 * σ0 = 1`: read without
the translation, it is not a permutation triple. -/
theorem mul_mul_ne_one_s3StoredTriple :
    s3StoredTriple.1.2.2 * s3StoredTriple.1.2.1 * s3StoredTriple.1.1 ≠ 1 := by
  decide

/-- The stored triple of `3T2-3_2.1_2.1-a` denotes the triple with components `(finRotate 3)⁻¹`
over `0` and `swap 1 2` over `1`. -/
theorem toTriple_s3StoredTriple :
    s3StoredTriple.toTriple = ofTwo (finRotate 3)⁻¹ (swap 1 2) :=
  ext_of_two (by simp [s3StoredTriple]) (by simp [s3StoredTriple])

/-- The translation of the stored triple of `3T2-3_2.1_2.1-a` is connected. -/
theorem isConnected_toTriple_s3StoredTriple : s3StoredTriple.toTriple.IsConnected := by
  rw [toTriple_s3StoredTriple]
  decide

/-- The translation of the stored triple of `3T2-3_2.1_2.1-a` is isomorphic to `s3Triple`, by the
relabeling `swap 0 2`. -/
theorem equivalent_toTriple_s3StoredTriple : s3StoredTriple.toTriple.Equivalent s3Triple := by
  rw [toTriple_s3StoredTriple]
  exact equivalent_iff_exists_smul_eq.2
    ⟨swap 0 2, ext_of_two (by simp only [smul_σ0, ofTwo_σ0, s3Triple_σ0]; decide)
      (by simp only [smul_σ1, ofTwo_σ1, s3Triple_σ1]; decide)⟩

/-- The map row `3T2-3_2.1_2.1-a`: the genus-zero cover of degree three with monodromy `S₃`, with
base field stored as the root `1` of `X - 1`. The equations, the curve link and the labels of
related objects are carrier data that validity does not read, and are left empty rather than
reproduced. -/
@[expose] def s3BelyiRecord : BelyiRecord 3 where
  label := "3T2-3_2.1_2.1-a"
  plabel := "3T2-3_2.1_2.1"
  deg := 3
  lambdas := ({3}, {2, 1}, {2, 1})
  g := 0
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [s3StoredTriple]
  triplesCyc := [([[0, 1, 2]], [[1, 2]], [[0, 1]])]
  curve := ""
  map := ""
  planeModel := ""
  planeConstant := ""
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- The map row `3T2-3_2.1_2.1-a` is valid for every passport of `s3Triple`. -/
theorem isValidFor_s3BelyiRecord {P : PassportSpec 3}
    (hP : PassportSpec.HasPassport ⟨s3Triple, isConnected_s3Triple⟩ P) :
    s3BelyiRecord.IsValidFor P := by
  have he := equivalent_toTriple_s3StoredTriple
  refine BelyiRecord.isValidFor_of_triples_eq_singleton rfl rfl rfl rfl
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      ⟨by decide, by decide, by decide⟩⟩ isConnected_toTriple_s3StoredTriple
    ((PassportSpec.hasPassport_iff_of_equivalent (ConnectedIsoClass.mk_eq_mk_iff.mp
      (ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr he)) P).mpr hP) ?_ ?_
  · rw [cycleData_eq_of_equivalent he, cycleData_s3Triple]
    rfl
  · rw [genus_eq_of_equivalent he, genus_s3Triple]
    rfl

/-! ### The genus-one row `4T1-4_4_2.2-a` -/

/-- A reconstruction of the map row `4T1-4_4_2.2-a`, with stored triple the database form
`(r⁻¹, r⁻¹, r²)` of `torusTriple = (r, r, r⁻²)`, for the rotation `r` of the four sheets, over the
base field stored as the root `1` of `X - 1`. The stored triple is a representative of the passport
rather than a copy of the frozen record. The equations, the curve link and the labels of related
objects are carrier data that validity does not read, and are left empty rather than
reproduced. -/
@[expose] def torusBelyiRecord : BelyiRecord 4 where
  label := "4T1-4_4_2.2-a"
  plabel := "4T1-4_4_2.2"
  deg := 4
  lambdas := ({4}, {4}, {2, 2})
  g := 1
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [equivOppositeConvention 4 torusTriple]
  triplesCyc := [([[0, 3, 2, 1]], [[0, 3, 2, 1]], [[0, 2], [1, 3]])]
  curve := ""
  map := ""
  planeModel := ""
  planeConstant := ""
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- The reconstructed map row `4T1-4_4_2.2-a` is valid for every passport of `torusTriple`. -/
theorem isValidFor_torusBelyiRecord {P : PassportSpec 4}
    (hP : PassportSpec.HasPassport ⟨torusTriple, isConnected_torusTriple⟩ P) :
    torusBelyiRecord.IsValidFor P := by
  have hr : (finRotate 4)⁻¹.IsCycleNotation [[0, 3, 2, 1]] :=
    ⟨by decide, by decide, by decide⟩
  have hinf : (finRotate 4 ^ 2).IsCycleNotation [[0, 2], [1, 3]] :=
    ⟨by decide, by decide, by decide⟩
  refine BelyiRecord.isValidFor_of_triples_eq_singleton rfl rfl rfl rfl
    ⟨by simpa using hr, by simpa using hr, by simpa using hinf⟩
    (by simpa using isConnected_torusTriple) (by simpa using hP) ?_ ?_
  · rw [StoredTriple.toTriple_equivOppositeConvention, cycleData_torusTriple]
    rfl
  · rw [StoredTriple.toTriple_equivOppositeConvention, genus_torusTriple]
    rfl

/-! ### The map labels -/

namespace BelyiRecord

/-- The map label `3T2-3_2.1_2.1-a` parses to the passport `3T2-3_2.1_2.1` and the orbit `a`. -/
theorem parseMapLabel_s3BelyiRecord :
    parseMapLabel 3 s3BelyiRecord.label = some (⟨⟨1, by simp⟩, {3}, {2, 1}, {2, 1}⟩, "a") := by
  rw [parseMapLabel_eq_some_iff_append]
  exact ⟨s3PassportRecord.plabel, by decide +kernel, by decide +kernel,
    by simp, PassportRecord.parsePassportLabel_s3PassportRecord⟩

/-- The stored label of the map row `3T2-3_2.1_2.1-a` extends its passport label and agrees with
its stored partitions. -/
theorem hasValidLabel_s3BelyiRecord : s3BelyiRecord.HasValidLabel :=
  (hasValidLabel_iff_of_parse parseMapLabel_s3BelyiRecord).mpr ⟨by decide +kernel, rfl⟩

/-- The map label `4T1-4_4_2.2-a` parses to the passport `4T1-4_4_2.2` and the orbit `a`. -/
theorem parseMapLabel_torusBelyiRecord :
    parseMapLabel 4 torusBelyiRecord.label = some (⟨⟨0, by simp⟩, {4}, {4}, {2, 2}⟩, "a") := by
  rw [parseMapLabel_eq_some_iff_append]
  exact ⟨torusPassportRecord.plabel, by decide +kernel, by decide +kernel,
    by simp, PassportRecord.parsePassportLabel_torusPassportRecord⟩

/-- The stored label of the map row `4T1-4_4_2.2-a` extends its passport label and agrees with its
stored partitions. -/
theorem hasValidLabel_torusBelyiRecord : torusBelyiRecord.HasValidLabel :=
  (hasValidLabel_iff_of_parse parseMapLabel_torusBelyiRecord).mpr ⟨by decide +kernel, rfl⟩

end BelyiRecord

/-! ### Reconciliation with the passport rows -/

/-- The map row `3T2-3_2.1_2.1-a` carries the passport label `3T2-3_2.1_2.1`. -/
theorem mapRows_s3PassportRecord :
    s3PassportRecord.mapRows [s3BelyiRecord] = [s3BelyiRecord] := by
  rw [PassportRecord.mapRows_def, List.filter_eq_self]
  simp [s3PassportRecord, s3BelyiRecord]

/-- The aggregations of the passport row `3T2-3_2.1_2.1` are computed from its map row: one row
carries its label, with stored orbit size one. -/
theorem isAggregatedFrom_s3PassportRecord :
    s3PassportRecord.IsAggregatedFrom [s3BelyiRecord] where
  numOrbits_eq := by rw [mapRows_s3PassportRecord]; rfl
  maxdegbf_eq := by rw [mapRows_s3PassportRecord]; rfl

open scoped Classical in
/-- The stored triple of the map row `3T2-3_2.1_2.1-a` represents exactly the isomorphism class
of the passport of `s3Triple`, which has only one. -/
theorem mapRowClasses_s3PassportRecord :
    s3PassportRecord.mapRowClasses [s3BelyiRecord] =
      (ConnectedTriple.passportOf ⟨s3Triple, isConnected_s3Triple⟩).classSet.image
        ConnectedIsoClass.forget := by
  refine (isValidAt_s3PassportRecord.sum_orbitSize_eq_passSize_iff
    (ConnectedTriple.hasPassport_passportOf _) (fun q hq ↦ ?_) ?_).mp ?_
  · rw [mapRows_s3PassportRecord, List.mem_singleton] at hq
    exact hq ▸ isValidFor_s3BelyiRecord (ConnectedTriple.hasPassport_passportOf _)
  · rw [mapRows_s3PassportRecord]
    exact List.pairwise_singleton _ _
  · rw [mapRows_s3PassportRecord]
    rfl

/-- The map row `3T2-3_2.1_2.1-a` certifies the stored primitivization of its own passport row,
which is primitive. -/
theorem isPrimitivizationOf_s3PassportRecord :
    s3BelyiRecord.IsPrimitivizationOf s3PassportRecord ⟨s3Triple, isConnected_s3Triple⟩ :=
  .of_card_primitivizationBlock_eq_one (Finset.card_singleton _) rfl
    (ConnectedTriple.hasPassport_passportOf _)
    (isValidFor_s3BelyiRecord (ConnectedTriple.hasPassport_passportOf _))

/-- The map row `4T1-4_4_2.2-a` carries the passport label `4T1-4_4_2.2`. -/
theorem mapRows_torusPassportRecord :
    torusPassportRecord.mapRows [torusBelyiRecord] = [torusBelyiRecord] := by
  rw [PassportRecord.mapRows_def, List.filter_eq_self]
  simp [torusPassportRecord, torusBelyiRecord]

/-- The aggregations of the passport row `4T1-4_4_2.2` are computed from its map row: one row
carries its label, with stored orbit size one. -/
theorem isAggregatedFrom_torusPassportRecord :
    torusPassportRecord.IsAggregatedFrom [torusBelyiRecord] where
  numOrbits_eq := by rw [mapRows_torusPassportRecord]; rfl
  maxdegbf_eq := by rw [mapRows_torusPassportRecord]; rfl

open scoped Classical in
/-- The stored triple of the map row `4T1-4_4_2.2-a` represents exactly the isomorphism class of
the passport of `torusTriple`, which has only one. -/
theorem mapRowClasses_torusPassportRecord :
    torusPassportRecord.mapRowClasses [torusBelyiRecord] =
      (ConnectedTriple.passportOf ⟨torusTriple, isConnected_torusTriple⟩).classSet.image
        ConnectedIsoClass.forget := by
  refine (isValidAt_torusPassportRecord.sum_orbitSize_eq_passSize_iff
    (ConnectedTriple.hasPassport_passportOf _) (fun q hq ↦ ?_) ?_).mp ?_
  · rw [mapRows_torusPassportRecord, List.mem_singleton] at hq
    exact hq ▸ isValidFor_torusBelyiRecord (ConnectedTriple.hasPassport_passportOf _)
  · rw [mapRows_torusPassportRecord]
    exact List.pairwise_singleton _ _
  · rw [mapRows_torusPassportRecord]
    rfl

end LMFDB
end PermutationTriple
end TauCeti
